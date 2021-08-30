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
  = (info, StgApp noEnterInfo fun args)
  where
    info | Just (TagSig arity res_info) <- lookupSig env fun
         , arity == length args  -- Saturated
         = res_info
         | otherwise
         = --pprTrace "inferAppUnknown" (ppr fun) $
           TagDunno

inferTagExpr env (StgConApp con cn args tys)
  = (info, StgConApp con cn args tys)
  where
    info | isUnboxedTupleDataCon con
         = TagTuple (map (lookupInfo env) args)
         | otherwise
         = TagDunno

inferTagExpr _ (StgLit l)
  = (TagDunno, StgLit l)

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
  -- , pprTrace "scrut info:" (ppr infos $$ ppr scrut $$ ppr bndrs) True
  , let bndrs' = zipWithEqual "inferTagExpr" mk_bndr bndrs infos
        mk_bndr :: BinderP p -> TagInfo -> (Id, TagSig)
        mk_bndr tup_bndr tup_info =
            --  pprTrace "mk_ubx_bndr_info" ( ppr bndr <+> ppr info ) $
            (getBinderId in_env tup_bndr, TagSig 0 tup_info)
        -- no case binder in alt_env here, unboxed tuple binders are dead after unarise
        alt_env = extendSigEnv in_env bndrs'
        (info, rhs') = inferTagExpr alt_env rhs
  = -- pprTrace "inferCase1" (ppr scrut $$ ppr bndr $$ ppr infos $$ ppr bndrs') $
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
                  , let (info, rhs') = inferTagExpr case_env rhs
                        bndrs' = addAltBndrInfo in_env con bndrs ]
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
addAltBndrInfo :: TagEnv p -> AltCon -> [BinderP p] -> [BinderP 'InferTaggedBinders]
addAltBndrInfo env (DataAlt con) bndrs
  = -- pprTrace "addAltBndrInfo" (ppr con $$ ppr out_bndrs) $
    out_bndrs

  where
    out_bndrs = zipWithEqual "inferTagAlt" mk_bndr bndrs marks
    mk_bndr bndr mark
      | isUnliftedType (idType id) || isMarkedStrict mark
      = (id, TagSig (idArity id) TagProper)
      | otherwise
      = noSig env bndr
        where
          id = getBinderId env bndr
    marks
      | isUnboxedSumDataCon con || isUnboxedTupleDataCon con
      = replicate (length bndrs) NotMarkedStrict
      | otherwise = (dataConRuntimeRepStrictness con)

addAltBndrInfo env _ bndrs = map (noSig env) bndrs

-----------------------------
inferTagBind :: OutputableInferPass p
  => TopLevelFlag -> TagEnv p -> GenStgBinding p -> (TagEnv p, GenStgBinding 'InferTaggedBinders)
inferTagBind top in_env (StgNonRec bndr rhs)
  = (env', StgNonRec (id, sig) rhs')
  where
    id   = getBinderId in_env bndr
    env' = extendSigEnv in_env [(id, sig)]
    (sig,rhs') = inferTagRhs top id in_env rhs

inferTagBind top in_env (StgRec pairs)
  = (in_env { te_env = out_env }, StgRec pairs')
  where
    (bndrs, rhss)     = unzip pairs
    in_ids            = map (getBinderId in_env) bndrs
    init_sigs         = map initSig rhss
    (out_env, pairs') = go in_env init_sigs rhss

    go :: forall q. OutputableInferPass q => TagEnv q -> [TagSig] -> [GenStgRhs q]
                 -> (TagSigEnv, [((Id,TagSig), GenStgRhs 'InferTaggedBinders)])
    go go_env in_sigs go_rhss
      --  | pprTrace "go" (ppr ids $$ ppr sigs $$ ppr sigs') False
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
initSig (StgRhsCon {})                = TagSig 0              TagProper
initSig (StgRhsClosure _ _ _ bndrs _) = TagSig (length bndrs) TagTagged

-----------------------------
inferTagRhs :: forall p.
     OutputableInferPass p
  => TopLevelFlag -- ^
  -> Id -- ^ Id we are binding to.
  -> TagEnv p -- ^
  -> GenStgRhs p -- ^
  -> (TagSig, GenStgRhs 'InferTaggedBinders)
inferTagRhs _top bnd_id in_env (StgRhsClosure ext cc upd bndrs body)
  = --pprTrace "inferTagRhsClosure" (ppr (_top, _grp_ids, env,info')) $
    (TagSig arity info', StgRhsClosure ext' cc upd out_bndrs body')
  where
    out_bndrs
      | Just marks <- idCbvMarks_maybe bnd_id
      = assert (length out_bndrs == length bndrs) $
        zipWithEqual "inferTagRhs" (mkArgSig) bndrs marks
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
    let
        strictArgs = zipEqual "inferTagRhs" args (dataConRuntimeRepStrictness con)
        -- argInfo = [(lookupInfo env (StgVarArg v)) | StgVarArg v <- args ]
        strictUntaggedIds = [v | (StgVarArg v, MarkedStrict) <- strictArgs
                            , not (isTaggedInfo (lookupInfo env (StgVarArg v))) ] :: [Id]

        mkResult x =
          -- pprTrace "inferTagRhsCon"
          --   ( ppr _grp_ids <+> ppr x <+> ppr _rhs $$
          --     ppr strictArgs $$
          --     ppr strictUntaggedIds $$
          --     ppr argInfo $$
          --     text "con:" <> ppr con
          --     ) $
            (TagSig 0 x, StgRhsCon cc con cn ticks args)
    in case () of
          -- All fields tagged or non-strict
        _ | null strictUntaggedIds -> mkResult TagProper
          | otherwise -> mkResult TagDunno
