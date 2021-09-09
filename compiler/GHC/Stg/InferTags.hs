{-# LANGUAGE TypeFamilies, DataKinds, GADTs, FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}

{-# LANGUAGE UndecidableInstances #-}
 -- To permit: type instance XLet 'InferTaggedBinders = XLet 'Vanilla



{-# OPTIONS_GHC -Wno-unused-imports -Wname-shadowing #-}
{-# LANGUAGE FlexibleContexts #-}
module GHC.Stg.InferTags ( inferTags ) where

import GHC.Prelude hiding (id)

import GHC.Core.DataCon
import GHC.Core.TyCon
import GHC.Core.Type
import GHC.Types.Id
import GHC.Stg.Syntax
import GHC.Types.Basic ( Arity, TopLevelFlag(..), RecFlag(..) )
import GHC.Types.Var.Env
import GHC.Types.Var.Set
import GHC.Types.RepType (dataConRuntimeRepStrictness)
import GHC.Core (AltCon(..))
import Data.List (mapAccumL)
import GHC.Utils.Outputable
import GHC.Utils.Misc( zipWithEqual, zipEqual )

import GHC.Stg.InferTags.Types
import GHC.Driver.Ppr
import GHC.Utils.Panic.Plain
import GHC.Utils.Trace

import Data.Maybe
{- Note [Tag inference]
~~~~~~~~~~~~~~~~~~~~~~~
The purpose of this pass is to attach to every binder a flag
to indicate whether or not it is "properly tagged".  A binder
is properly tagged if it is guaranteed:
 - to point to a heap-allocated value
 - and to have the tag of the value encoded in the pointer

  inferTags :: [GenStgTopBinding 'Vanilla] -> [GenStgTopBinding 'InferTaggedBinders]

For example
  let x = Just y in ...

Here x will be properly tagged: it will point to the heap-allocated
values for (Just y), and the tag-bits of the pointer will encode
the tag for Just.

We then take this information in GHC.Stg.InferTags.Rewrite to rewriteTopBinds

Note [Strict field invariant]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
As part of tag inference we introduce the strict field invariant.
Which consist of us saying that:

* Pointers in strict fields must be save to re-evaluate and be
  properly tagged.

Why? Because if we have code like:

case strictPair of
  SP x y ->
    case x of ...

It allows us to safely omit the code to enter x and the check
for the presence of a tag that goes along with it.
However we might still branch on the tag as usual.

This is enforced by the code GHC.Stg.InferTags.Rewrite
where we:

* Look at all constructor allocations.
* Check if arguments to their strict fields are known to be properly tagged
* If not we convert `StrictJust x` into `case x of x' -> StrictJust x'`

However we try to push the case up the AST into the next closure.

For a full example consider this code:

foo ... = ...
  let c = StrictJust x
  in ...

Naively we would rewrite `let c = StrictJust` into `let c = case x of x' -> StrictJust x'`
However that is horrible! We would end up allocating a thunk for `c` first, which only when
evaluated would allocate the constructor.

So instead we try to push the case "up" into a surrounding closure context. So for this case
we instead produce:

  foo ... = ...
    case x of x' ->
      DEFAULT -> let c = StrictJust x'
                in ...

Which means c remains a regular constructor allocation and we avoid unneccesary overhead.
The only problems to this approach are top level definitions and recursive bindings.

For top level bindings we accept the fact that some constructor applications end up as thunks.
It's a rare enough thing that it doesn't really matter and the computation will be shared anyway.

For recursive bindings the isse arises if we have:

  let rec {
    x = e1 -- e1 mentioning y
    y = StrictJust x
  }

We obviously can't wrap the case around the recursive group as `x` isn't in scope there.
This means if we can't proof that the arguments to the strict fields (in this case `x`)
are tagged we have to turn the above into:

  let rec {
    x = e1 -- e1 mentioning y
    y = case x of x' -> StrictJust x'
  }

But this rarely happens so is not a reason for concern.

Note [Tag inference passes]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
SPJ posed the good question why we bother having two different pass
parameterizations for tag inference. After all InferTaggedBinders
already has put the needed information on the binders.

Indeed we could the transformation described in Note [Strict field invariant]
as part of the StgToCmm transformation. But it wouldn't work well with the way
we currently produce Cmm code.

In particular we would have to analyze rhss *before* we can determine
if they should contain the required code for upholding the strict field
invariant or if the code should be placed in front of the code of a given
rhs. This means more dependencies between different parts of codeGen and
more complexity in general so I decided to implement this as an STG transformation
instead.

This doesn't actually mean we *need* two different parameterizations. But since
we already walk the whole AST I figured it would be more efficient to put the
relevant tag information into the StgApp nodes during this pass as well.

It avoids the awkward situation where codegeneration of the context of a let depends
on the rhs of the let itself, avoids the need for all binders to be be tuples and
seemed more efficient.

-}

{- *********************************************************************
*                                                                      *
                         Main inference algorithm
*                                                                      *
********************************************************************* -}

type OutputableInferPass p = (Outputable (TagEnv p)
                              , Outputable (GenStgExpr p)
                              , Outputable (BinderP p)
                              , Outputable (GenStgRhs p))

inferTags :: [GenStgTopBinding 'Vanilla] -> [GenStgTopBinding 'InferTaggedBinders]
inferTags binds =
  -- pprTrace "Binds" (pprGenStgTopBindings shortStgPprOpts $ binds) $
  snd (mapAccumL inferTagTopBind initEnv binds)

-----------------------
inferTagTopBind :: TagEnv 'Vanilla -> GenStgTopBinding 'Vanilla
                -> (TagEnv 'Vanilla, GenStgTopBinding 'InferTaggedBinders)
inferTagTopBind env (StgTopStringLit id bs)
  = (env, StgTopStringLit id bs)
inferTagTopBind env (StgTopLifted bind)
  = (env', StgTopLifted bind')
  where
    (env', bind') = inferTagBind TopLevel env bind


-----------------------
inferTagExpr :: forall p. OutputableInferPass p
  => TagEnv p -> GenStgExpr p -> (TagInfo, GenStgExpr 'InferTaggedBinders)
inferTagExpr env (StgApp _ext fun args)
  = -- pprTrace "inferTagExpr1"
  --     (ppr fun <+> ppr args $$ ppr info $$
  --      text "deadEndInfo:" <> ppr (isDeadEndId fun, idArity fun, length args)
  --     )
    (info, StgApp noEnterInfo fun args)
  where
    !fun_arity = idArity fun
    info | fun_arity == 0
         = TagDunno

         | isDeadEndId fun
         , fun_arity == length args -- The function will actually be entered.
         = TagTagged -- See Note [Bottoms functions are TagTagged]

         | Just (TagSig arity res_info) <- lookupSig env fun
         , arity == length args  -- Saturated
         = res_info

         | otherwise
         = --pprTrace "inferAppUnknown" (ppr fun) $
           TagDunno

inferTagExpr env (StgConApp con cn args tys)
  = (inferConTag env con args, StgConApp con cn args tys)

inferTagExpr _ (StgLit l)
  = (TagTagged, StgLit l)

inferTagExpr env (StgTick tick body)
  = (info, StgTick tick body')
  where
    (info, body') = inferTagExpr env body

inferTagExpr _ (StgOpApp op args ty)
  = -- Do any primops guarantee to return a properly tagged value?
    -- I think not.  Ditto foreign calls.
    (TagDunno, StgOpApp op args ty)

inferTagExpr env (StgLet ext bind body)
  = (info, StgLet ext' bind' body')
  where
    ext' = case te_ext env of ExtEqEv -> ext
    (env', bind') = inferTagBind NotTopLevel env bind
    (info, body') = inferTagExpr env' body

inferTagExpr env (StgLetNoEscape ext bind body)
  = (info, StgLetNoEscape ext' bind' body')
  where
    ext' = case te_ext env of ExtEqEv -> ext
    (env', bind') = inferTagBind NotTopLevel env bind
    (info, body') = inferTagExpr env' body

inferTagExpr in_env (StgCase scrut bndr ty alts)
  -- Unboxed tuples get their info from the expression we scrutinise if any
  | [(DataAlt con, bndrs, rhs)] <- alts
  , isUnboxedTupleDataCon con
  , Just infos <- scrut_infos bndrs
  , let bndrs' = zipWithEqual "inferTagExpr" mk_bndr bndrs infos
        mk_bndr :: BinderP p -> TagInfo -> (Id, TagSig)
        mk_bndr tup_bndr tup_info =
            --  pprTrace "mk_ubx_bndr_info" ( ppr bndr <+> ppr info ) $
            (getBinderId in_env tup_bndr, TagSig 0 tup_info)
        -- no case binder in alt_env here, unboxed tuple binders are dead after unarise
        alt_env = extendSigEnv in_env bndrs'
        (info, rhs') = inferTagExpr alt_env rhs
  =
    -- pprTrace "inferCase1" (
    --   text "scrut:" <> ppr scrut $$
    --   text "bndr:" <> ppr bndr $$
    --   text "infos" <> ppr infos $$
    --   text "out_bndrs" <> ppr bndrs') $
    (info, StgCase scrut' (noSig in_env bndr) ty [(DataAlt con, bndrs', rhs')])

  | null alts -- Empty case, but I might just be paranoid.
  = -- pprTrace "inferCase2" empty $
    (TagDunno, StgCase scrut' bndr' ty [])
  -- More than one alternative OR non-tuple single alternative.
  | otherwise
  = -- pprTrace "inferCase3" empty $
    let
        case_env = extendSigEnv in_env [bndr']

        (infos, alts')
          = unzip [ (info, (con, bndrs', rhs'))
                  | (con, bndrs, rhs) <- alts
                  , let (alt_env,bndrs') = addAltBndrInfo case_env con bndrs
                        (info, rhs') = inferTagExpr alt_env rhs
                         ]
        alt_info = foldr combineAltInfo TagTagged infos
    in -- pprTrace "combine alts:" (ppr alt_info $$ ppr infos)
    ( alt_info
    , StgCase scrut' bndr' ty alts')
  where
    -- Single unboxed tuple alternative
    scrut_infos bndrs = case scrut_info of
      TagTagged -> Just $ replicate (length bndrs) TagProper
      TagTuple infos -> Just infos
      _ -> Nothing
    (scrut_info, scrut') = inferTagExpr in_env scrut
    bndr' = (getBinderId in_env bndr, TagSig 0 TagProper)

-- Not used if we have tuple info about the scrutinee
addAltBndrInfo :: forall p. TagEnv p -> AltCon -> [BinderP p] -> (TagEnv p, [BinderP 'InferTaggedBinders])
addAltBndrInfo env (DataAlt con) bndrs
  | not (isUnboxedTupleDataCon con || isUnboxedSumDataCon con)
  = (out_env, out_bndrs)
  where
    marks = dataConRuntimeRepStrictness con :: [StrictnessMark]
    out_bndrs = zipWith mk_bndr bndrs marks
    out_env = extendSigEnv env out_bndrs

    mk_bndr :: (BinderP p -> StrictnessMark -> (Id, TagSig))
    mk_bndr bndr mark
      | isUnliftedType (idType id) || isMarkedStrict mark
      = (id, TagSig (idArity id) TagProper)
      | otherwise
      = noSig env bndr
        where
          id = getBinderId env bndr

addAltBndrInfo env _ bndrs = (env, map (noSig env) bndrs)

-----------------------------
inferTagBind :: OutputableInferPass p
  => TopLevelFlag -> TagEnv p -> GenStgBinding p -> (TagEnv p, GenStgBinding 'InferTaggedBinders)
inferTagBind top in_env (StgNonRec bndr rhs)
  =
    -- pprTrace "inferBindNonRec" (
    --   ppr bndr $$
    --   ppr (isDeadEndId id) $$
    --   ppr sig)
    (env', StgNonRec (id, sig) rhs')
  where
    id   = getBinderId in_env bndr
    env' = extendSigEnv in_env [(id, sig)]
    (sig,rhs') = inferTagRhs top id in_env rhs

inferTagBind top in_env (StgRec pairs)
  = -- pprTrace "rec" (ppr (map fst pairs) $$ ppr (in_env { te_env = out_env }, StgRec pairs')) $
    (in_env { te_env = out_env }, StgRec pairs')
  where
    (bndrs, rhss)     = unzip pairs
    in_ids            = map (getBinderId in_env) bndrs
    init_sigs         = map initSig rhss
    (out_env, pairs') = go in_env init_sigs rhss

    go :: forall q. OutputableInferPass q => TagEnv q -> [TagSig] -> [GenStgRhs q]
                 -> (TagSigEnv, [((Id,TagSig), GenStgRhs 'InferTaggedBinders)])
    go go_env in_sigs go_rhss
      --   | pprTrace "go" (ppr in_ids $$ ppr in_sigs $$ ppr out_sigs $$ ppr rhss') False
      --  = undefined
       | in_sigs == out_sigs = (te_env rhs_env, in_bndrs `zip` rhss')
       | otherwise     = go env' out_sigs rhss'
       where
         in_bndrs = in_ids `zip` in_sigs
         rhs_env = extendSigEnv go_env in_bndrs
         anaRhs :: Id -> GenStgRhs q -> (TagSig, GenStgRhs 'InferTaggedBinders)
         anaRhs bnd rhs = inferTagRhs top bnd rhs_env rhs
         (out_sigs, rhss') = unzip (zipWithEqual "inferTagBind" anaRhs in_ids go_rhss)
         env' = makeTagged go_env

initSig :: GenStgRhs p -> TagSig
-- Initial signature for the fixpoint loop
initSig (StgRhsCon {})                = TagSig 0              TagTagged
initSig (StgRhsClosure _ _ _ bndrs _) = TagSig (length bndrs) TagTagged


{- Note [Bottoms functions are TagTagged]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If we have a function with two branches which one
being bottom, and the other returning a tagged
unboxed tuple what is the result? We give it TagTagged! (and a arity).

Consider this function:

foo :: Bool -> (# Bool, Bool #)
foo x = case x of
    True -> (# True,True #)
    False -> undefined

The true branch is obviously tagged. The other branch isn't.
We want to treat the *result* of foo as tagged as well so that
the combination of the branches also is tagged if all non-bottom
branches are tagged.
This is save because the  the function is still always called/entered by the backend
because of the arity. So the tag info on functions is essentially only used when one
branch in which the function is applied, is combined with another branch.
The function will never return-hence the tag we give to the returned result straight
up doesn't matter. So we might as well give it TagTagged.

-}

-----------------------------
inferTagRhs :: forall p.
     OutputableInferPass p
  => TopLevelFlag -- ^
  -> Id -- ^ Id we are binding to.
  -> TagEnv p -- ^
  -> GenStgRhs p -- ^
  -> (TagSig, GenStgRhs 'InferTaggedBinders)
inferTagRhs _top bnd_id in_env (StgRhsClosure ext cc upd bndrs body)
  | isDeadEndId bnd_id
  -- TODO: Bottom functions are TagTagged
  = (TagSig arity TagTagged, StgRhsClosure ext' cc upd out_bndrs body')
  | otherwise
  = --pprTrace "inferTagRhsClosure" (ppr (_top, _grp_ids, env,info')) $
    (TagSig arity info', StgRhsClosure ext' cc upd out_bndrs body')
  where
    out_bndrs
      | Just marks <- idCbvMarks_maybe bnd_id
      -- Sometimes an we eta-expand foo with additional arguments after ww, and we also trim
      -- the list of marks to the last strict entry. So we can conservatively
      -- assume these are not strict
      = zipWith (mkArgSig) bndrs (marks ++ repeat NotMarkedStrict)
      | otherwise = map (noSig env') bndrs :: [(Id,TagSig)]

    env' = extendSigEnv in_env out_bndrs
    ext' = case te_ext env' of ExtEqEv -> ext
    (info, body') = inferTagExpr env' body
    arity = length bndrs
    info'
      | arity == 0
      = TagDunno
      -- TODO: We could preserve tuple fields for thunks
      -- as well.

      | otherwise  = info

    mkArgSig :: BinderP p -> StrictnessMark -> (Id,TagSig)
    mkArgSig bndp mark =
      let id = getBinderId in_env bndp
          tag = case mark of
            MarkedStrict -> TagProper
            _
              | isUnliftedType (idType id) -> TagProper
              | otherwise -> TagDunno
      in (id, TagSig (idArity id) tag)

inferTagRhs _top _ env _rhs@(StgRhsCon cc con cn ticks args)
-- Top level constructors, which have untagged arguments to strict fields
-- become thunks. Same goes for rhs which are part of a recursive group.
-- We encode this by giving changing RhsCon nodes the info TagDunno
  = --pprTrace "inferTagRhsCon" (ppr grp_ids) $
    (TagSig 0 (inferConTag env con args), StgRhsCon cc con cn ticks args)

inferConTag :: TagEnv p -> DataCon -> [StgArg] -> TagInfo
inferConTag env con args
  | isUnboxedTupleDataCon con
  = TagTuple $ map (flatten_arg_tag . lookupInfo env) args

  | otherwise
  =
    -- pprTrace "inferConTag"
    --   ( text "con:" <> ppr con $$
    --     text "args:" <> ppr args $$
    --     text "marks:" <> ppr (dataConRuntimeRepStrictness con) $$
    --     text "arg_info:" <> ppr (map (lookupInfo env) args) $$
    --     text "info:" <> ppr info) $
    info

  where
    info = if any arg_needs_eval strictArgs then TagDunno else TagProper
    strictArgs = zipEqual "inferTagRhs" args (dataConRuntimeRepStrictness con) :: ([(StgArg, StrictnessMark)])
    arg_needs_eval (arg,strict)
      -- lazy args
      | not (isMarkedStrict strict) = False
      | tag <- (lookupInfo env arg)
      -- banged args need to be strict, or require eval
      = not (isTaggedInfo tag)

    flatten_arg_tag (TagTagged) = TagProper
    flatten_arg_tag (TagProper ) = TagProper
    flatten_arg_tag (TagTuple _) = panic "inferConTag: Impossible - should have been unarised"
    flatten_arg_tag (TagDunno) = TagDunno

