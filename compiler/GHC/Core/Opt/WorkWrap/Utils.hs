{-
(c) The GRASP/AQUA Project, Glasgow University, 1993-1998

A library for the ``worker\/wrapper'' back-end to the strictness analyser
-}


{-# LANGUAGE ViewPatterns #-}

module GHC.Core.Opt.WorkWrap.Utils
   ( WwOpts(..), initWwOpts, mkWwBodies, mkWWstr, mkWWstr_one
   , needsVoidWorkerArg, addVoidWorkerArg
   , DataConPatContext(..)
   , UnboxingDecision(..), wantToUnboxArg
   , findTypeShape, IsRecDataConResult(..), isRecDataCon
   , mkAbsentFiller
   , isWorkerSmallEnough, dubiousDataConInstArgTys
   , isGoodWorker, badWorker , goodWorker
   )
where

import GHC.Prelude

import GHC.Driver.Session
import GHC.Driver.Config (initSimpleOpts)

import GHC.Core
import GHC.Core.Utils
import GHC.Core.DataCon
import GHC.Core.Make
import GHC.Core.Subst
import GHC.Core.Type
import GHC.Core.Multiplicity
import GHC.Core.Coercion
import GHC.Core.Reduction
import GHC.Core.FamInstEnv
import GHC.Core.TyCon
import GHC.Core.TyCon.Set
import GHC.Core.TyCon.RecWalk
import GHC.Core.SimpleOpt( SimpleOpts )

import GHC.Types.Id
import GHC.Types.Id.Info
import GHC.Types.Demand
import GHC.Types.Cpr
import GHC.Types.Id.Make ( voidArgId, voidPrimId )
import GHC.Types.Var.Env
import GHC.Types.Basic
import GHC.Types.Unique.Supply
import GHC.Types.Name ( getOccFS )

import GHC.Data.FastString
import GHC.Data.OrdList
import GHC.Data.List.SetOps

import GHC.Builtin.Types ( tupleDataCon )

import GHC.Utils.Misc
import GHC.Utils.Outputable
import GHC.Utils.Panic
import GHC.Utils.Panic.Plain
import GHC.Utils.Trace

import Control.Applicative ( (<|>) )
import Control.Monad ( zipWithM )
import Data.List ( unzip4 )

import GHC.Types.RepType
import GHC.Unit.Types

{-
************************************************************************
*                                                                      *
\subsection[mkWrapperAndWorker]{@mkWrapperAndWorker@}
*                                                                      *
************************************************************************

Here's an example.  The original function is:

\begin{verbatim}
g :: forall a . Int -> [a] -> a

g = \/\ a -> \ x ys ->
        case x of
          0 -> head ys
          _ -> head (tail ys)
\end{verbatim}

From this, we want to produce:
\begin{verbatim}
-- wrapper (an unfolding)
g :: forall a . Int -> [a] -> a

g = \/\ a -> \ x ys ->
        case x of
          I# x# -> $wg a x# ys
            -- call the worker; don't forget the type args!

-- worker
$wg :: forall a . Int# -> [a] -> a

$wg = \/\ a -> \ x# ys ->
        let
            x = I# x#
        in
            case x of               -- note: body of g moved intact
              0 -> head ys
              _ -> head (tail ys)
\end{verbatim}

Something we have to be careful about:  Here's an example:

\begin{verbatim}
-- "f" strictness: U(P)U(P)
f (I# a) (I# b) = a +# b

g = f   -- "g" strictness same as "f"
\end{verbatim}

\tr{f} will get a worker all nice and friendly-like; that's good.
{\em But we don't want a worker for \tr{g}}, even though it has the
same strictness as \tr{f}.  Doing so could break laziness, at best.

Consequently, we insist that the number of strictness-info items is
exactly the same as the number of lambda-bound arguments.  (This is
probably slightly paranoid, but OK in practice.)  If it isn't the
same, we ``revise'' the strictness info, so that we won't propagate
the unusable strictness-info into the interfaces.


************************************************************************
*                                                                      *
\subsection{The worker wrapper core}
*                                                                      *
************************************************************************

@mkWwBodies@ is called when doing the worker\/wrapper split inside a module.
-}

data WwOpts
  = MkWwOpts
  { wo_fam_envs          :: !FamInstEnvs
  , wo_simple_opts       :: !SimpleOpts
  , wo_cpr_anal          :: !Bool

  -- Used for absent argument error message
  , wo_module            :: !Module
  , wo_unlift_strict     :: !Bool -- Generate workers even if the only effect is some args
                                  -- get passed unlifted.
                                  -- See Note [WW for calling convention]
  }

initWwOpts :: Module -> DynFlags -> FamInstEnvs -> WwOpts
initWwOpts this_mod dflags fam_envs = MkWwOpts
  { wo_fam_envs          = fam_envs
  , wo_simple_opts       = initSimpleOpts dflags
  , wo_cpr_anal          = gopt Opt_CprAnal dflags
  , wo_module            = this_mod
  , wo_unlift_strict     = gopt Opt_WorkerWrapperUnlift dflags
  }

type WwResult
  = ([Demand],              -- Demands for worker (value) args
     [CbvMark],             -- Cbv semantics for worker (value) args
     JoinArity,             -- Number of worker (type OR value) args
     Id -> CoreExpr,        -- Wrapper body, lacking only the worker Id
     CoreExpr -> CoreExpr)  -- Worker body, lacking the original function rhs

nop_fn :: CoreExpr -> CoreExpr
nop_fn body = body


mkWwBodies :: WwOpts
           -> Id             -- ^ The original function
           -> [Var]          -- ^ Manifest args of original function
           -> Type           -- ^ Result type of the original function,
                             --   after being stripped of args
           -> [Demand]       -- ^ Strictness of original function
           -> Cpr            -- ^ Info about function result
           -> UniqSM (Maybe WwResult)
-- ^ Given a function definition
--
-- > data T = MkT Int Bool Char
-- > f :: (a, b) -> Int -> T
-- > f = \x y -> E
--
-- @mkWwBodies _ 'f' ['x::(a,b)','y::Int'] '(a,b)' ['1P(L,L)', '1P(L)'] '1'@
-- returns
--
--   * The wrapper body context for the call to the worker function, lacking
--     only the 'Id' for the worker function:
--
--     > W[_] :: Id -> CoreExpr
--     > W[work_fn] = \x y ->          -- args of the wrapper    (cloned_arg_vars)
--     >   case x of (a, b) ->         -- unbox wrapper args     (wrap_fn_str)
--     >   case y of I# n ->           --
--     >   case <work_fn> a b n of     -- call to the worker fun (call_work)
--     >   (# i, b, c #) -> MkT i b c  -- rebox result           (wrap_fn_cpr)
--
--   * The worker body context that wraps around its hole reboxing defns for x
--     and y, as well as returning CPR transit variables of the unboxed MkT
--     result in an unboxed tuple:
--
--     > w[_] :: CoreExpr -> CoreExpr
--     > w[fn_rhs] = \a b n ->              -- args of the worker       (work_lam_args)
--     >   let { y = I# n; x = (a, b) } in  -- reboxing wrapper args    (work_fn_str)
--     >   case <fn_rhs> x y of             -- call to the original RHS (call_rhs)
--     >   MkT i b c -> (# i, b, c #)       -- return CPR transit vars  (work_fn_cpr)
--
--     NB: The wrap_rhs hole is to be filled with the original wrapper RHS
--     @\x y -> E@. This is so that we can also use @w@ to transform stable
--     unfoldings, the lambda args of which may be different than x and y.
--
--   * Id details for the worker function like demands on arguments and its join
--     arity.
--
-- All without looking at E (except for beta reduction, see Note [Join points
-- and beta-redexes]), which allows us to apply the same split to function body
-- and its unfolding(s) alike.
--
mkWwBodies opts fun_id arg_vars res_ty demands res_cpr
  = do  { massertPpr (filter isId arg_vars `equalLength` demands)
                     (text "wrong wrapper arity" $$ ppr fun_id $$ ppr arg_vars $$ ppr res_ty $$ ppr demands)

        -- Clone and prepare arg_vars of the original fun RHS
        -- See Note [Freshen WW arguments]
        -- and Note [Zap IdInfo on worker args]
        ; uniq_supply <- getUniqueSupplyM
        ; let args_free_tcvs = tyCoVarsOfTypes (res_ty : map varType arg_vars)
              empty_subst = mkEmptySubst (mkInScopeSet args_free_tcvs)
              zapped_arg_vars = map zap_var arg_vars
              (subst, cloned_arg_vars) = cloneBndrs empty_subst uniq_supply zapped_arg_vars
              res_ty' = GHC.Core.Subst.substTy subst res_ty
              init_cbv_marks = map (const NotMarkedCbv) cloned_arg_vars

        ; (useful1, work_args_cbv, wrap_fn_str, fn_args)
             <- mkWWstr opts cloned_arg_vars init_cbv_marks

        ; let (work_args, work_marks) = unzip work_args_cbv

        -- Do CPR w/w.  See Note [Always do CPR w/w]
        ; (useful2, wrap_fn_cpr, work_fn_cpr)
              <- mkWWcpr_entry opts res_ty' res_cpr

        ; let (work_lam_args, work_call_args, work_call_cbv)
                | needsVoidWorkerArg fun_id arg_vars work_args
                = addVoidWorkerArg work_args work_marks
                | otherwise
                = (work_args, work_args, work_marks)

              call_work work_fn  = mkVarApps (Var work_fn) work_call_args
              call_rhs fn_rhs = mkAppsBeta fn_rhs fn_args
                                  -- See Note [Join points and beta-redexes]
              wrapper_body = mkLams cloned_arg_vars . wrap_fn_cpr . wrap_fn_str . call_work
              worker_body = mkLams work_lam_args . work_fn_cpr . call_rhs
              (worker_args_dmds, work_val_cbvs)= unzip [(idDemandInfo v,cbv) | (v,cbv) <- zipEqual "mkWwBodies" work_call_args work_call_cbv, isId v]

        ; if ((useful1 && not only_one_void_argument) || useful2)
          then return (Just (worker_args_dmds, work_val_cbvs, length work_call_args,
                       wrapper_body, worker_body))
          else return Nothing
        }
        -- We use an INLINE unconditionally, even if the wrapper turns out to be
        -- something trivial like
        --      fw = ...
        --      f = __inline__ (coerce T fw)
        -- The point is to propagate the coerce to f's call sites, so even though
        -- f's RHS is now trivial (size 1) we still want the __inline__ to prevent
        -- fw from being inlined into f's RHS
  where
    zap_var v | isTyVar v = v
              | otherwise = modifyIdInfo zap_info v
    zap_info info -- See Note [Zap IdInfo on worker args]
      = info `setOccInfo`       noOccInfo

    -- Note [Do not split void functions]
    only_one_void_argument
      | [d] <- demands
      , [v] <- filter isId arg_vars
      , isAbsDmd d && isZeroBitTy (idType v)
      = True
      | otherwise
      = False

-- | Version of 'GHC.Core.mkApps' that does beta reduction on-the-fly.
-- PRECONDITION: The arg expressions are not free in any of the lambdas binders.
mkAppsBeta :: CoreExpr -> [CoreArg] -> CoreExpr
-- The precondition holds for our call site in mkWwBodies, because all the FVs
-- of as are either cloned_arg_vars (and thus fresh) or fresh worker args.
mkAppsBeta (Lam b body) (a:as) = bindNonRec b a $! mkAppsBeta body as
mkAppsBeta f            as     = mkApps f as

-- See Note [Limit w/w arity]
isWorkerSmallEnough :: Int -> Int -> [Var] -> Bool
isWorkerSmallEnough max_worker_args old_n_args vars
  = count isId vars <= max old_n_args max_worker_args
    -- We count only Free variables (isId) to skip Type, Kind
    -- variables which have no runtime representation.
    -- Also if the function took 82 arguments before (old_n_args), it's fine if
    -- it takes <= 82 arguments afterwards.

{-
Note [Always do CPR w/w]
~~~~~~~~~~~~~~~~~~~~~~~~
At one time we refrained from doing CPR w/w for thunks, on the grounds that
we might duplicate work.  But that is already handled by the demand analyser,
which doesn't give the CPR property if w/w might waste work: see
Note [CPR for thunks] in GHC.Core.Opt.DmdAnal.

And if something *has* been given the CPR property and we don't w/w, it's
a disaster, because then the enclosing function might say it has the CPR
property, but now doesn't and there a cascade of disaster.  A good example
is #5920.

Note [Limit w/w arity]
~~~~~~~~~~~~~~~~~~~~~~~~
Guard against high worker arity as it generates a lot of stack traffic.
A simplified example is #11565#comment:6

Current strategy is very simple: don't perform w/w transformation at all
if the result produces a wrapper with arity higher than -fmax-worker-args
and the number arguments before w/w (see #18122).

It is a bit all or nothing, consider

        f (x,y) (a,b,c,d,e ... , z) = rhs

Currently we will remove all w/w ness entirely. But actually we could
w/w on the (x,y) pair... it's the huge product that is the problem.

Could we instead refrain from w/w on an arg-by-arg basis? Yes, that'd
solve f. But we can get a lot of args from deeply-nested products:

        g (a, (b, (c, (d, ...)))) = rhs

This is harder to spot on an arg-by-arg basis. Previously mkWwStr was
given some "fuel" saying how many arguments it could add; when we ran
out of fuel it would stop w/wing.

Still not very clever because it had a left-right bias.

Note [Zap IdInfo on worker args]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We have to zap the following IdInfo when re-using arg variables of the original
function for the worker:

  * OccInfo: Dead wrapper args now occur in Apps of the worker's call to the
    original fun body. Those occurrences will quickly cancel away with the lambdas
    of the fun body in the next run of the Simplifier, but CoreLint will complain
    in the meantime, so zap it.

We zap in mkWwBodies because we need the zapped variables when binding them in
mkWWstr (mkAbsentFiller, specifically).

Note [Do not split void functions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider this rather common form of binding:
        $j = \x:Void# -> ...no use of x...

Since x is not used it'll be marked as absent.  But there is no point
in w/w-ing because we'll simply add (\y:Void#), see addVoidWorkerArg.

If x has a more interesting type (eg Int, or Int#), there *is* a point
in w/w so that we don't pass the argument at all.

************************************************************************
*                                                                      *
\subsection{Making wrapper args}
*                                                                      *
************************************************************************

During worker-wrapper stuff we may end up with an unlifted thing
which we want to let-bind without losing laziness.  So we
add a void argument.  E.g.

        f = /\a -> \x y z -> E::Int#    -- E does not mention x,y,z
==>
        fw = /\ a -> \void -> E
        f  = /\ a -> \x y z -> fw realworld

We use the state-token type which generates no code.
-}

-- | Whether the worker needs an additional `Void#` arg as per
-- Note [Protecting the last value argument] or
-- Note [Preserving float barriers].
needsVoidWorkerArg :: Id -> [Var] -> [Var] -> Bool
needsVoidWorkerArg fn_id wrap_args work_args
  =  not (isJoinId fn_id) && no_value_arg -- See Note [Protecting the last value argument]
  || needs_float_barrier                  -- See Note [Preserving float barriers]
  where
    no_value_arg        = all (not . isId) work_args
    is_float_barrier v  = isId v && hasNoOneShotInfo (idOneShotInfo v)
    wrap_had_barrier    = any is_float_barrier wrap_args
    work_has_barrier    = any is_float_barrier work_args
    needs_float_barrier = wrap_had_barrier && not work_has_barrier

-- | Inserts a `Void#` arg before the first argument.
--
-- Why as the first argument? See Note [SpecConst needs to add void args first]
-- in SpecConstr.
addVoidWorkerArg :: [Var] -> [CbvMark]
                 -> ([Var],     -- Lambda bound args
                     [Var],     -- Args at call site
                     [CbvMark]) -- cbv semantics for the worker args.
addVoidWorkerArg work_args cbv_marks
  = (voidArgId : work_args, voidPrimId:work_args, NotMarkedCbv:cbv_marks)

{-
Note [Protecting the last value argument]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If the user writes (\_ -> E), they might be intentionally disallowing
the sharing of E. Since absence analysis and worker-wrapper are keen
to remove such unused arguments, we add in a void argument to prevent
the function from becoming a thunk.  Three reasons why turning a function
into a thunk might be bad:

1) It can create a space leak. e.g.
      f x = let y () = [1..x]
            in (sum (y ()) + length (y ()))
   As written it'll calculate [1..x] twice, and avoid keeping a big
   list around.  (Of course let-floating may introduce the leak; but
   at least w/w doesn't.)

2) It can prevent inlining *under a lambda*. e.g.
       g = \y. [1..100]
       f = \t. g ()
   Here we can inline g under the \t.  But we won't if we remove the \y.

3) It can create an unlifted binding.  E.g.
       g :: Int -> Int#
       g = \x. 30#
   Removing the \x would leave an unlifted binding.

NB: none of these apply to a join point.

Note [Preserving float barriers]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider
```
let
  t = sum [0..x]
  f a{os} b[Dmd=A] c{os} = ... t ...
in f 1 2 3 + f 4 5 6
```
Here, we would like to drop the argument `b` because it's absent. But doing so
leaves behind only one-shot lambdas, `$wf a{os} c{os} = ...`, and then the
Simplifier will inline `t` into `$wf`, because `$wf` says "I'm only called
once". That's bad, because we lost sharing of `t`! Similarly, FloatIn would
happily float `t` into `$wf`, see Note [Floating in past a lambda group].

Why does floating happen after dropping `b` but not before? Because `b` was the
only non-one-shot value lambda left, acting as our "float barrier".

Definition:  A float barrier is a non-one-shot value lambda.
Key insight: If `f` had a float barrier, `$wf` has to have one, too.

To this end, in `needsVoidWorkerArg`, we check whether the wrapper had a float
barrier and if the worker has none so far. If that is the case, we add a `Void#`
argument at the end as an artificial float barrier.

The issue is tracked in #21150. It came up when compiling GHC itself, in
GHC.Tc.Gen.Bind.mkEdges. There the key_map thunk was inlined after WW dropped a
leading absent non-one-shot arg. Here are some example wrapper arguments of
which some are absent or one-shot and the resulting worker arguments:

  * \a{Abs}.\b{os}.\c{os}... ==> \b{os}.\c{os}.\(_::Void#)...
    Wrapper arg `a` was the only float barrier and had been dropped. Hence Void#
  * \a{Abs,os}.\b{os}.\c... ==> \b{os}.\c...
    Worker arg `c` is a float barrier.
  * \a.\b{Abs}.\c{os}... ==> \a.\c{os}...
    Worker arg `a` is a float barrier.
  * \a{os}.\b{Abs,os}.\c{os}... ==> \a{os}.\c{os}...
    Wrapper didn't have a float barrier, no need for Void#.
  * \a{Abs,os}.... ==> ... (no value lambda left)
    This examples simply demonstrates that preserving float barriers is not
    enough to subsume Note [Protecting the last value argument].

Executable examples in T21150.

Note [Join points and beta-redexes]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Originally, the worker would invoke the original function by calling it with
arguments, thus producing a beta-redex for the simplifier to munch away:

  \x y z -> e => (\x y z -> e) wx wy wz

Now that we have special rules about join points, however, this is Not Good if
the original function is itself a join point, as then it may contain invocations
of other join points:

  join j1 x = ...
  join j2 y = if y == 0 then 0 else j1 y

  =>

  join j1 x = ...
  join $wj2 y# = let wy = I# y# in (\y -> if y == 0 then 0 else jump j1 y) wy
  join j2 y = case y of I# y# -> jump $wj2 y#

There can't be an intervening lambda between a join point's declaration and its
occurrences, so $wj2 here is wrong. But of course, this is easy enough to fix:

  ...
  let join $wj2 y# = let wy = I# y# in let y = wy in if y == 0 then 0 else j1 y
  ...

Hence we simply do the beta-reduction here. (This would be harder if we had to
worry about hygiene, but luckily wy is freshly generated.)

Note [Freshen WW arguments]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
When we do a worker/wrapper split, we must freshen the arg vars of the original
fun RHS because they might shadow each other. E.g.

  f :: forall a. Maybe a -> forall a. Maybe a -> Int -> Int
  f @a x @a y z = case x <|> y of
    Nothing -> z
    Just _  -> z + 1

  ==> {WW split unboxing the Int}

  $wf :: forall a. Maybe a -> forall a. Maybe a -> Int# -> Int
  $wf @a x @a y wz = (\@a x @a y z -> case x <|> y of ...) ??? x @a y (I# wz)

(Notice that the code we actually emit will sort-of ANF-ise the lambda args,
leading to even more shadowing issues. The above demonstrates that even if we
try harder we'll still get shadowing issues.)

What should we put in place for ??? ? Certainly not @a, because that would
reference the wrong, inner a. A similar situation occurred in #12562, we even
saw a type variable in the worker shadowing an outer term-variable binding.

We avoid the issue by freshening the argument variables from the original fun
RHS through 'cloneBndrs', which will also take care of subsitution in binder
types. Fortunately, it's sufficient to pick the FVs of the arg vars as in-scope
set, so that we don't need to do a FV traversal over the whole body of the
original function.

At the moment, #12562 has no regression test. As such, this Note is not covered
by any test logic or when bootstrapping the compiler. Yet we clearly want to
freshen the binders, as the example above demonstrates.
Adding a Core pass that maximises shadowing for testing purposes might help,
see #17478.
-}

{-
************************************************************************
*                                                                      *
\subsection{Unboxing Decision for Strictness and CPR}
*                                                                      *
************************************************************************
-}

-- | The information needed to build a pattern for a DataCon to be unboxed.
-- The pattern can be generated from 'dcpc_dc' and 'dcpc_tc_args' via
-- 'GHC.Core.Utils.dataConRepInstPat'. The coercion 'dcpc_co' is for newtype
-- wrappers.
--
-- If we get @DataConPatContext dc tys co@ for some type @ty@
-- and @dataConRepInstPat ... dc tys = (exs, flds)@, then
--
--   * @dc @exs flds :: T tys@
--   * @co :: T tys ~ ty@
data DataConPatContext
  = DataConPatContext
  { dcpc_dc      :: !DataCon
  , dcpc_tc_args :: ![Type]
  , dcpc_co      :: !Coercion
  }

-- | Describes the outer shape of an argument to be unboxed or left as-is
-- Depending on how @s@ is instantiated (e.g., 'Demand' or 'Cpr').
data UnboxingDecision s
  = StopUnboxing
  -- ^ We ran out of strictness info. Leave untouched.
  | DropAbsent
  -- ^ The argument/field was absent. Drop it.
  | Unbox !DataConPatContext [s]
  -- ^ The argument is used strictly or the returned product was constructed, so
  -- unbox it.
  -- The 'DataConPatContext' carries the bits necessary for
  -- instantiation with 'dataConRepInstPat'.
  -- The @[s]@ carries the bits of information with which we can continue
  -- unboxing, e.g. @s@ will be 'Demand' or 'Cpr'.
  | Unlift
  -- ^ The argument can't be unboxed, but we want it to be passed evaluated to the worker.

-- Do we want to create workers just for unlifting?
wwForUnlifting :: WwOpts -> Bool
wwForUnlifting !opts
    -- Always unlift if possible
    | wo_unlift_strict opts = goodWorker
    -- Don't unlift  it would cause additional W/W splits.
    | otherwise = badWorker

badWorker :: Bool
badWorker = False

goodWorker :: Bool
goodWorker = True

isGoodWorker :: Bool -> Bool
isGoodWorker = id


-- | Unwraps the 'Boxity' decision encoded in the given 'SubDemand' and returns
-- a 'DataConPatContext' as well the nested demands on fields of the 'DataCon'
-- to unbox.
wantToUnboxArg
  :: Bool                -- ^ Consider unlifting
  -> FamInstEnvs
  -> Type                -- ^ Type of the argument
  -> Demand              -- ^ How the arg was used
  -> UnboxingDecision Demand
-- See Note [Which types are unboxed?]
wantToUnboxArg do_unlifting fam_envs ty dmd@(n :* sd)
  | isAbs n
  = DropAbsent

  | Just (tc, tc_args, co) <- normSplitTyConApp_maybe fam_envs ty
  , Just dc <- tyConSingleAlgDataCon_maybe tc
  , let arity = dataConRepArity dc
  , Just (Unboxed, ds) <- viewProd arity sd -- See Note [Boxity analysis]
  -- NB: No strictness or evaluatedness checks for unboxing here.
  -- That is done by 'finaliseArgBoxities'!
  = Unbox (DataConPatContext dc tc_args co) ds

  -- See Note [Strict Worker Ids]
  | do_unlifting
  , isStrUsedDmd dmd
  , not (isFunTy ty)
  , not (isUnliftedType ty) -- Already unlifted!
    -- NB: function arguments have a fixed RuntimeRep, so it's OK to call isUnliftedType here
  = Unlift

  | otherwise
  = StopUnboxing


-- | Unboxing strategy for constructed results.
wantToUnboxResult :: FamInstEnvs -> Type -> Cpr -> UnboxingDecision Cpr
-- See Note [Which types are unboxed?]
wantToUnboxResult fam_envs ty cpr
  | Just (con_tag, arg_cprs) <- asConCpr cpr
  , Just (tc, tc_args, co) <- normSplitTyConApp_maybe fam_envs ty
  , Just dcs <- tyConAlgDataCons_maybe tc <|> open_body_ty_warning
  , dcs `lengthAtLeast` con_tag -- This might not be true if we import the
                                -- type constructor via a .hs-boot file (#8743)
  , let dc = dcs `getNth` (con_tag - fIRST_TAG)
  , null (dataConExTyCoVars dc) -- no existentials;
                                -- See Note [Which types are unboxed?]
                                -- and GHC.Core.Opt.CprAnal.argCprType
                                -- where we also check this.
  , all isLinear (dataConInstArgTys dc tc_args)
  -- Deactivates CPR worker/wrapper splits on constructors with non-linear
  -- arguments, for the moment, because they require unboxed tuple with variable
  -- multiplicity fields.
  = Unbox (DataConPatContext dc tc_args co) arg_cprs

  | otherwise
  = StopUnboxing

  where
    -- See Note [non-algebraic or open body type warning]
    open_body_ty_warning = warnPprTrace True "wantToUnboxResult: non-algebraic or open body type" (ppr ty) Nothing

isLinear :: Scaled a -> Bool
isLinear (Scaled w _ ) =
  case w of
    One -> True
    _ -> False


{- Note [Which types are unboxed?]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Worker/wrapper will unbox

  1. A strict data type argument, that
       * is an algebraic data type (not a newtype)
       * is not recursive (as per 'isRecDataCon')
       * has a single constructor (thus is a "product")
       * that may bind existentials
     We can transform
     > data D a = forall b. D a b
     > f (D @ex a b) = e
     to
     > $wf @ex a b = e
     via 'mkWWstr'.

  2. The constructed result of a function, if
       * its type is an algebraic data type (not a newtype)
       * is not recursive (as per 'isRecDataCon')
       * (might have multiple constructors, in contrast to (1))
       * the applied data constructor *does not* bind existentials
     We can transform
     > f x y = let ... in D a b
     to
     > $wf x y = let ... in (# a, b #)
     via 'mkWWcpr'.

     NB: We don't allow existentials for CPR W/W, because we don't have unboxed
     dependent tuples (yet?). Otherwise, we could transform
     > f x y = let ... in D @ex (a :: ..ex..) (b :: ..ex..)
     to
     > $wf x y = let ... in (# @ex, (a :: ..ex..), (b :: ..ex..) #)

The respective tests are in 'wantToUnboxArg' and
'wantToUnboxResult', respectively.

Note that the data constructor /can/ have evidence arguments: equality
constraints, type classes etc.  So it can be GADT.  These evidence
arguments are simply value arguments, and should not get in the way.

Note [mkWWstr and unsafeCoerce]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
By using unsafeCoerce, it is possible to make the number of demands fail to
match the number of constructor arguments; this happened in #8037.
If so, the worker/wrapper split doesn't work right and we get a Core Lint
bug.  The fix here is simply to decline to do w/w if that happens.

Note [non-algebraic or open body type warning]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
There are a few cases where the W/W transformation is told that something
returns a constructor, but the type at hand doesn't really match this. One
real-world example involves unsafeCoerce:
  foo = IO a
  foo = unsafeCoerce c_exit
  foreign import ccall "c_exit" c_exit :: IO ()
Here CPR will tell you that `foo` returns a () constructor for sure, but trying
to create a worker/wrapper for type `a` obviously fails.
(This was a real example until ee8e792  in libraries/base.)

It does not seem feasible to avoid all such cases already in the analyser (and
after all, the analysis is not really wrong), so we simply do nothing here in
mkWWcpr. But we still want to emit warning with -DDEBUG, to hopefully catch
other cases where something went avoidably wrong.

This warning also triggers for the stream fusion library within `text`.
We can'easily W/W constructed results like `Stream` because we have no simple
way to express existential types in the worker's type signature.

Note [WW for calling convention]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If we know a function f will always evaluate a particular argument
we might decide that it should rather get evaluated by the caller.
We call this "unlifting" the argument.
Sometimes the caller knows that the argument is already evaluated,
so we won't generate any code to enter/evaluate the argument.
This evaluation avoidance can be quite beneficial.
Especially for recursive functions who pass the same lifted argument
along on each iteration or walk over strict data structures.

One way to achieve this is to do a W/W split, where the wrapper does
the evaluation, and the worker can treat its arguments as unlifted.
The wrapper is small and will be inlined at almost all call sites and
the evaluation code in the wrapper can then cancel out with evaluation
done by the calling context if the argument is evaluated there.
Same idea as W/W to avoid allocation really, just for a different kind
of work.

Performing W/W might not always be a win. In particular it's easy to break
(badly written, but common) rule frameworks by doing additional W/W splits.
See #20364 for a more detailed explaination.

Hence we have the following strategies with different trade-offs:
A) Never do W/W *just* for unlifting of arguments.
  + Very conservative - doesn't break any rules
  - Lot's of performance left on the table
B) Do W/W on just about anything where it might be
  beneficial.
  + Exploits pretty much every oppertunity for unlifting.
  - A bit of compile time/code size cost for all the wrappers.
  - Can break rules which would otherwise fire. See #20364.
C) Unlift *any* (non-boot exported) functions arguments if they are strict.
  That is instead of creating a Worker with the new calling convention we
  change the calling convention of the binding itself.
  + Exploits every opportunity for unlifting.
  + Maybe less bad interactions with rules.
  - Requires tracking of boot-exported definitions.
  - Requires either:
    ~ Eta-expansion at *all* call sites in order to generate
      an impedance matcher function. Leading to massive code bloat.
      Essentially we end up creating a imprompto wrapper function
      wherever we wouldn't inline the wrapper with a W/W approach.
    ~ There is the option of achieving this without eta-expansion if we instead expand
      the partial application code to check for demands on the calling convention and
      for it to evaluate the arguments. The main downsides there would be the complexity
      of the implementation and that it carries a certain overhead even for functions who
      don't take advantage of this functionality. I haven't tried this approach because it's
      not trivial to implement and doing W/W splits seems to work well enough.

Currently we use the first approach A) by default, with a flag that allows users to fall back to the
more aggressive approach B).
I also tried the third approach C) using eta-expansion at call sites to avoid modifying the PAP-handling
code which wasn't fruitful. See https://gitlab.haskell.org/ghc/ghc/-/merge_requests/5614#note_389903.
We could still try to do C) in the future by having PAP calls which will evaluate the required arguments
before calling the partially applied function. But this would be neither a small nor simple change so we
stick with A) and a flag for B) for now.
See also Note [Tag Inference] and Note [Strict Worker Ids]
-}

{-
************************************************************************
*                                                                      *
\subsection{Worker/wrapper for Strictness and Absence}
*                                                                      *
************************************************************************
-}

mkWWstr :: WwOpts
        -> [Var]                         -- Wrapper args; have their demand info on them
                                         --  *Includes type variables*
        -> [CbvMark]                     -- cbv info for arguments
        -> UniqSM (Bool,                 -- Will this result in a useful worker
                   [(Var,CbvMark)],      -- Worker args/their call-by-value semantics.
                   CoreExpr -> CoreExpr, -- Wrapper body, lacking the worker call
                                         -- and without its lambdas
                                         -- This fn adds the unboxing
                   [CoreExpr])           -- Reboxed args for the call to the
                                         -- original RHS. Corresponds one-to-one
                                         -- with the wrapper arg vars
mkWWstr opts args cbv_info
  = go args cbv_info
  where
    go_one arg cbv = mkWWstr_one opts arg cbv

    go []           _ = return (badWorker, [], nop_fn, [])
    go (arg : args) (cbv:cbvs)
      =               do { (useful1, args1, wrap_fn1, wrap_arg)  <- go_one arg cbv
                         ; (useful2, args2, wrap_fn2, wrap_args) <- go args cbvs
                         ; return ( useful1 || useful2
                                  , args1 ++ args2
                                  , wrap_fn1 . wrap_fn2
                                  , wrap_arg:wrap_args ) }
    go _ _ = panic "mkWWstr: Impossible - cbv/arg length missmatch"

----------------------
-- mkWWstr_one wrap_var = (useful, work_args, wrap_fn, wrap_arg)
--   *  wrap_fn assumes wrap_var is in scope,
--        brings into scope work_args (via cases)
--   * wrap_arg assumes work_args are in scope, and builds a ConApp that
--        reconstructs the RHS of wrap_var that we pass to the original RHS
-- See Note [Worker/wrapper for Strictness and Absence]
mkWWstr_one :: WwOpts
            -> Var
            -> CbvMark
            -> UniqSM (Bool, [(Var,CbvMark)], CoreExpr -> CoreExpr, CoreExpr)
mkWWstr_one opts arg marked_cbv =
  case wantToUnboxArg True fam_envs arg_ty arg_dmd of
    _ | isTyVar arg -> do_nothing

    DropAbsent
      | Just absent_filler <- mkAbsentFiller opts arg
         -- Absent case.  Dropt the argument from the worker.
         -- We can't always handle absence for arbitrary
         -- unlifted types, so we need to choose just the cases we can
         -- (that's what mkAbsentFiller does)
      -> return (goodWorker, [], nop_fn, absent_filler)

    Unbox dcpc ds -> unbox_one_arg opts arg ds dcpc marked_cbv

    Unlift -> return  ( wwForUnlifting opts
                      , [(setIdUnfolding arg evaldUnfolding, MarkedCbv)]
                      , nop_fn
                      , varToCoreExpr arg)

    _ -> do_nothing -- Other cases, like StopUnboxing

  where
    fam_envs   = wo_fam_envs opts
    arg_ty     = idType arg
    arg_dmd    = idDemandInfo arg
    -- Type args don't get cbv marks
    arg_cbv    = if isTyVar arg then NotMarkedCbv else marked_cbv
    do_nothing = return (badWorker, [(arg,arg_cbv)], nop_fn, varToCoreExpr arg)

unbox_one_arg :: WwOpts
          -> Var
          -> [Demand]
          -> DataConPatContext
          -> CbvMark
          -> UniqSM (Bool, [(Var,CbvMark)], CoreExpr -> CoreExpr, CoreExpr)
unbox_one_arg opts arg_var ds
          DataConPatContext { dcpc_dc = dc, dcpc_tc_args = tc_args
                            , dcpc_co = co }
          _marked_cbv
  = do { pat_bndrs_uniqs <- getUniquesM
       ; let ex_name_fss = map getOccFS $ dataConExTyCoVars dc
             -- Create new arguments we get when unboxing dc
             (ex_tvs', arg_ids) =
               dataConRepFSInstPat (ex_name_fss ++ repeat ww_prefix) pat_bndrs_uniqs (idMult arg_var) dc tc_args
             -- Apply str info to new args.
             arg_ids' = zipWithEqual "unbox_one_arg" setIdDemandInfo arg_ids ds
             unbox_fn = mkUnpackCase (Var arg_var) co (idMult arg_var)
                                     dc (ex_tvs' ++ arg_ids')
             -- Mark arguments coming out of strict fields as evaluated and give them cbv semantics. See Note [Strict Worker Ids]
             cbv_arg_marks = zipWithEqual "unbox_one_arg" bangToMark (dataConRepStrictness dc) arg_ids'
             unf_args = zipWith setEvald arg_ids' cbv_arg_marks
             cbv_marks = (map (const NotMarkedCbv) ex_tvs') ++ cbv_arg_marks
       ; (_sub_args_quality, worker_args, wrap_fn, wrap_args) <- mkWWstr opts (ex_tvs' ++ unf_args) cbv_marks
       ; let wrap_arg = mkConApp dc (map Type tc_args ++ wrap_args) `mkCast` mkSymCo co
       ; return (goodWorker, worker_args, unbox_fn . wrap_fn, wrap_arg) }
                          -- Don't pass the arg, rebox instead
    where bangToMark :: StrictnessMark -> Id -> CbvMark
          bangToMark NotMarkedStrict _ = NotMarkedCbv
          bangToMark MarkedStrict v
            | isUnliftedType (idType v) = NotMarkedCbv
            | otherwise                 = MarkedCbv
          setEvald var NotMarkedCbv  = var
          setEvald var MarkedCbv     = setIdUnfolding var evaldUnfolding

-- | Tries to find a suitable absent filler to bind the given absent identifier
-- to. See Note [Absent fillers].
--
-- If @mkAbsentFiller _ id == Just e@, then @e@ is an absent filler with the
-- same type as @id@. Otherwise, no suitable filler could be found.
mkAbsentFiller :: WwOpts -> Id -> Maybe CoreExpr
mkAbsentFiller opts arg
  -- The lifted case: Bind 'absentError' for a nice panic message if we are
  -- wrong (like we were in #11126). See (1) in Note [Absent fillers]
  | mightBeLiftedType arg_ty
  , not is_strict, not is_evald -- See (2) in Note [Absent fillers]
  = Just (mkAbsentErrorApp arg_ty msg)

  -- The default case for mono rep: Bind `RUBBISH[rr] arg_ty`
  -- See Note [Absent fillers], the main part
  | otherwise
  = mkLitRubbish arg_ty

  where
    arg_ty    = idType arg
    is_strict = isStrictDmd (idDemandInfo arg)
    is_evald  = isEvaldUnfolding $ idUnfolding arg

    msg = renderWithContext
            (defaultSDocContext { sdocSuppressUniques = True })
            (vcat
              [ text "Arg:" <+> ppr arg
              , text "Type:" <+> ppr arg_ty
              , file_msg ])
              -- We need to suppress uniques here because otherwise they'd
              -- end up in the generated code as strings. This is bad for
              -- determinism, because with different uniques the strings
              -- will have different lengths and hence different costs for
              -- the inliner leading to different inlining.
              -- See also Note [Unique Determinism] in GHC.Types.Unique
    file_msg = text "In module" <+> quotes (ppr $ wo_module opts)

{- Note [Worker/wrapper for Strictness and Absence]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The worker/wrapper transformation, mkWWstr_one, takes concrete action
based on the 'UnboxingDescision' returned by 'wantToUnboxArg'.
The latter takes into account several possibilities to decide if the
function is worthy for splitting:

1. If an argument is absent, it would be silly to pass it to
   the worker.  Hence the DropAbsent case.  This case must come
   first because the bottom demand B is also strict.
   E.g. B comes from a function like
       f x = error "urk"
   and the absent demand A can come from Note [Unboxing evaluated arguments]
   in GHC.Core.Opt.DmdAnal.

2. If the argument is evaluated strictly (or known to be eval'd),
   we can take a view into the product demand ('viewProd'). In accordance
   with Note [Boxity analysis], 'wantToUnboxArg' will say 'Unbox'.
   'mkWWstr_one' then follows suit it and recurses into the fields of the
   product demand. For example

     f :: (Int, Int) -> Int
     f p = (case p of (a,b) -> a) + 1
   is split to
     f :: (Int, Int) -> Int
     f p = case p of (a,b) -> $wf a

     $wf :: Int -> Int
     $wf a = a + 1

   and
     g :: Bool -> (Int, Int) -> Int
     g c p = case p of (a,b) ->
                if c then a else b
   is split to
     g c p = case p of (a,b) -> $gw c a b
     $gw c a b = if c then a else b

2a But do /not/ unbox if Boxity Analysis said "Boxed".
   In this case, 'wantToUnboxArg' returns 'StopUnboxing'.
   Otherwise we risk decomposing and reboxing a massive
   tuple which is barely used. Example:

        f :: ((Int,Int) -> String) -> (Int,Int) -> a
        f g pr = error (g pr)

        main = print (f fst (1, error "no"))

   Here, f does not take 'pr' apart, and it's stupid to do so.
   Imagine that it had millions of fields. This actually happened
   in GHC itself where the tuple was DynFlags

2b But if e.g. a large tuple or product type is always demanded we might
   decide to "unlift" it. That is tighten the calling convention for that
   argument to require it to be passed as a pointer to the value itself.
   See Note [WW for calling convention].

3. In all other cases (e.g., lazy, used demand and not eval'd),
   'finaliseArgBoxities' will have cleared the Boxity flag to 'Boxed'
   (see Note [Finalising boxity for demand signatures] in GHC.Core.Opt.DmdAnal)
   and 'wantToUnboxArg' returns 'StopUnboxing' so that 'mkWWstr_one'
   stops unboxing.

Note [Worker/wrapper for bottoming functions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We used not to split if the result is bottom.
[Justification:  there's no efficiency to be gained.]

But it's sometimes bad not to make a wrapper.  Consider
        fw = \x# -> let x = I# x# in case e of
                                        p1 -> error_fn x
                                        p2 -> error_fn x
                                        p3 -> the real stuff
The re-boxing code won't go away unless error_fn gets a wrapper too.
[We don't do reboxing now, but in general it's better to pass an
unboxed thing to f, and have it reboxed in the error cases....]

Note [Record evaluated-ness in worker/wrapper]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Suppose we have

   data T = MkT !Int Int

   f :: T -> T
   f x = e

and f's is strict, and has the CPR property.  The we are going to generate
this w/w split

   f x = case x of
           MkT x1 x2 -> case $wf x1 x2 of
                           (# r1, r2 #) -> MkT r1 r2

   $wfw x1 x2 = let x = MkT x1 x2 in
                case e of
                  MkT r1 r2 -> (# r1, r2 #)

Note that

* In the worker $wf, inside 'e' we can be sure that x1 will be
  evaluated (it came from unpacking the argument MkT.  But that's no
  immediately apparent in $wf

* In the wrapper 'f', which we'll inline at call sites, we can be sure
  that 'r1' has been evaluated (because it came from unpacking the result
  MkT.  But that is not immediately apparent from the wrapper code.

Missing these facts isn't unsound, but it loses possible future
opportunities for optimisation.

Solution: use setCaseBndrEvald when creating
 (A) The arg binders x1,x2 in mkWstr_one via mkUnpackCase
         See #13077, test T13077
 (B) The result binders r1,r2 in mkWWcpr_entry
         See Trace #13077, test T13077a
         And #13027 comment:20, item (4)
to record that the relevant binder is evaluated.

Note [Absent fillers]
~~~~~~~~~~~~~~~~~~~~~
Consider

  data T = MkT [Int] [Int] ![Int]  -- NB: last field is strict
  f :: T -> Int# -> blah
  f ps w = case ps of MkT xs ys zs -> <body mentioning xs>

Then f gets a strictness sig of <S(L,A,A)><A>. We make a worker $wf thus:

  $wf :: [Int] -> blah
  $wf xs = case ps of MkT xs _ _ -> <body mentioning xs>
    where
      ys = absentError "ys :: [Int]"
      zs = RUBBISH[LiftedRep] @[Int]
      ps = MkT xs ys zs
      w  = RUBBISH[IntRep] @Int#

The absent arguments 'ys', 'zs' and 'w' aren't even passed to the worker.
And neither should they! They are never used, their value is irrelevant (hence
they are *dead code*) and they are probably discarded after the next run of the
Simplifier (when they are in fact *unreachable code*). Yet, we have to come up
with "filler" values that we bind the absent arg Ids to.

That is exactly what Note [Rubbish literals] are for: A convenient way to
conjure filler values at any type (and any representation or levity!).

Needless to say, there are some wrinkles:

  1. In case we have a absent, /lazy/, and /lifted/ arg, we use an error-thunk
     instead. If absence analysis was wrong (e.g., #11126) and the binding
     in fact is used, then we get a nice panic message instead of undefined
     runtime behavior (See Modes of failure from Note [Rubbish literals]).

     Obviously, we can't use an error-thunk if the value is of unlifted rep
     (like 'Int#' or 'MutVar#'), because we'd immediately evaluate the panic.

  2. We also mustn't put an error-thunk (that fills in for an absent value of
     lifted rep) in a strict field, because #16970 establishes the invariant
     that strict fields are always evaluated, by (re-)evaluating what is put in
     a strict field. That's the reason why 'zs' binds a rubbish literal instead
     of an error-thunk, see #19133.

     How do we detect when we are about to put an error-thunk in a strict field?
     Ideally, we'd just look at the 'StrictnessMark' of the DataCon's field, but
     it's quite nasty to thread the marks though 'mkWWstr' and 'mkWWstr_one'.
     So we rather look out for a necessary condition for strict fields:
     Note [Unboxing evaluated arguments] in DmdAnal makes it so that the demand on
     'zs' is absent and /strict/: It will get cardinality 'C_10', the empty
     interval, rather than 'C_00'. Hence the 'isStrictDmd' check: It guarantees
     we never fill in an error-thunk for an absent strict field.
     But that also means we emit a rubbish lit for other args that have
     cardinality 'C_10' (say, the arg to a bottoming function) where we could've
     used an error-thunk, but that's a small price to pay for simplicity.

     In #19766, we discovered that even if the binder has eval cardinality
     'C_00', it may end up in a strict field, with no surrounding seq
     whatsoever! That happens if the calling code has already evaluated
     said lambda binder, which will then have an evaluated unfolding
     ('isEvaldUnfolding'). That in turn tells the Simplifier it is free to drop
     the seq. So we better don't fill in an error-thunk for eval'd arguments
     either, just in case it ends up in a strict field!

  3. We can only emit a LitRubbish if the arg's type @arg_ty@ is mono-rep, e.g.
     of the form @TYPE rep@ where @rep@ is not (and doesn't contain) a variable.
     Why? Because if we don't know its representation (e.g. size in memory,
     register class), we don't know what or how much rubbish to emit in codegen.
     'mkLitRubbish' returns 'Nothing' in this case and we simply fall
     back to passing the original parameter to the worker.

     Note that currently this case should not occur, because binders always
     have to be representation monomorphic. But in the future, we might allow
     levity polymorphism, e.g. a polymorphic levity variable in 'BoxedRep'.

While (1) and (2) are simply an optimisation in terms of compiler debugging
experience, (3) should be irrelevant in most programs, if not all.

Historical note: I did try the experiment of using an error thunk for unlifted
things too, relying on the simplifier to drop it as dead code.  But this is
fragile

 - It fails when profiling is on, which disables various optimisations

 - It fails when reboxing happens. E.g.
      data T = MkT Int Int#
      f p@(MkT a _) = ...g p....
   where g is /lazy/ in 'p', but only uses the first component.  Then
   'f' is /strict/ in 'p', and only uses the first component.  So we only
   pass that component to the worker for 'f', which reconstructs 'p' to
   pass it to 'g'.  Alas we can't say
       ...f (MkT a (absentError Int# "blah"))...
   because `MkT` is strict in its Int# argument, so we get an absentError
   exception when we shouldn't.  Very annoying!

************************************************************************
*                                                                      *
         Type scrutiny that is specific to demand analysis
*                                                                      *
************************************************************************
-}

-- | Exactly 'dataConInstArgTys', but lacks the (ASSERT'ed) precondition that
-- the 'DataCon' may not have existentials. The lack of cloning the existentials
-- compared to 'dataConInstExAndArgVars' makes this function \"dubious\";
-- only use it where type variables aren't substituted for!
dubiousDataConInstArgTys :: DataCon -> [Type] -> [Type]
dubiousDataConInstArgTys dc tc_args = arg_tys
  where
    univ_tvs = dataConUnivTyVars dc
    ex_tvs   = dataConExTyCoVars dc
    subst    = extendTCvInScopeList (zipTvSubst univ_tvs tc_args) ex_tvs
    arg_tys  = map (GHC.Core.Type.substTy subst . scaledThing) (dataConRepArgTys dc)

findTypeShape :: FamInstEnvs -> Type -> TypeShape
-- Uncover the arrow and product shape of a type
-- The data type TypeShape is defined in GHC.Types.Demand
-- See Note [Trimming a demand to a type] in GHC.Core.Opt.DmdAnal
findTypeShape fam_envs ty
  = go (setRecTcMaxBound 2 initRecTc) ty
       -- You might think this bound of 2 is low, but actually
       -- I think even 1 would be fine.  This only bites for recursive
       -- product types, which are rare, and we really don't want
       -- to look deep into such products -- see #18034
  where
    go rec_tc ty
       | Just (_, _, res) <- splitFunTy_maybe ty
       = TsFun (go rec_tc res)

       | Just (tc, tc_args)  <- splitTyConApp_maybe ty
       = go_tc rec_tc tc tc_args

       | Just (_, ty') <- splitForAllTyCoVar_maybe ty
       = go rec_tc ty'

       | otherwise
       = TsUnk

    go_tc rec_tc tc tc_args
       | Just (HetReduction (Reduction _ rhs) _) <- topReduceTyFamApp_maybe fam_envs tc tc_args
       = go rec_tc rhs

       | Just con <- tyConSingleAlgDataCon_maybe tc
       , Just rec_tc <- if isTupleTyCon tc
                        then Just rec_tc
                        else checkRecTc rec_tc tc
         -- We treat tuples specially because they can't cause loops.
         -- Maybe we should do so in checkRecTc.
         -- The use of 'dubiousDataConInstArgTys' is OK, since this
         -- function performs no substitution at all, hence the uniques
         -- don't matter.
         -- We really do encounter existentials here, see
         -- Note [Which types are unboxed?] for an example.
       = TsProd (map (go rec_tc) (dubiousDataConInstArgTys con tc_args))

       | Just (ty', _) <- instNewTyCon_maybe tc tc_args
       , Just rec_tc <- checkRecTc rec_tc tc
       = go rec_tc ty'

       | otherwise
       = TsUnk

-- | Returned by 'isRecDataCon'.
-- See also Note [Detecting recursive data constructors].
data IsRecDataConResult
  = DefinitelyRecursive  -- ^ The algorithm detected a loop
  | NonRecursiveOrUnsure -- ^ The algorithm detected no loop, went out of fuel
                         -- or hit an .hs-boot file
  deriving (Eq, Show)

instance Outputable IsRecDataConResult where
  ppr = text . show

combineIRDCR :: IsRecDataConResult -> IsRecDataConResult -> IsRecDataConResult
combineIRDCR DefinitelyRecursive _                   = DefinitelyRecursive
combineIRDCR _                   DefinitelyRecursive = DefinitelyRecursive
combineIRDCR _                   _                   = NonRecursiveOrUnsure

combineIRDCRs :: [IsRecDataConResult] -> IsRecDataConResult
combineIRDCRs = foldl' combineIRDCR NonRecursiveOrUnsure
{-# INLINE combineIRDCRs #-}

-- | @isRecDataCon _ fuel dc@, where @tc = dataConTyCon dc@ returns
--
--   * @DefinitelyRecursive@ if the analysis found that @tc@ is reachable
--     through one of @dc@'s @arg_tys@.
--   * @NonRecursiveOrUnsure@ if the analysis found that @tc@ is not reachable
--     through one of @dc@'s fields (so surely non-recursive).
--   * @NonRecursiveOrUnsure@ when @fuel /= Infinity@
--     and @fuel@ expansions of nested data TyCons were not enough to prove
--     non-recursivenss, nor arrive at an occurrence of @tc@ thus proving
--     recursiveness. (So not sure if non-recursive.)
--   * @NonRecursiveOrUnsure@ when we hit an abstract TyCon (one without
--     visible DataCons), such as those imported from .hs-boot files.
--     Similarly for stuck type and data families.
--
-- If @fuel = 'Infinity'@ and there are no boot files involved, then the result
-- is never @Nothing@ and the analysis is a depth-first search. If @fuel = 'Int'
-- f@, then the analysis behaves like a depth-limited DFS and returns @Nothing@
-- if the search was inconclusive.
--
-- See Note [Detecting recursive data constructors] for which recursive DataCons
-- we want to flag.
isRecDataCon :: FamInstEnvs -> IntWithInf -> DataCon -> IsRecDataConResult
isRecDataCon fam_envs fuel orig_dc
  | isTupleDataCon orig_dc || isUnboxedSumDataCon orig_dc
  = NonRecursiveOrUnsure
  | otherwise
  = -- pprTraceWith "isRecDataCon" (\answer -> ppr dc <+> dcolon <+> ppr (dataConRepType dc) $$ ppr fuel $$ ppr answer) $
    go_dc fuel emptyTyConSet orig_dc
  where
    go_dc :: IntWithInf -> TyConSet -> DataCon -> IsRecDataConResult
    go_dc fuel visited_tcs dc =
      combineIRDCRs [ go_arg_ty fuel visited_tcs arg_ty
                    | arg_ty <- map scaledThing (dataConRepArgTys dc) ]

    go_arg_ty :: IntWithInf -> TyConSet -> Type -> IsRecDataConResult
    go_arg_ty fuel visited_tcs ty
      --- | pprTrace "arg_ty" (ppr ty) False = undefined

      | Just (_tcv, ty') <- splitForAllTyCoVar_maybe ty
      = go_arg_ty fuel visited_tcs ty'
          -- See Note [Detecting recursive data constructors], point (A)

      | Just (tc, tc_args) <- splitTyConApp_maybe ty
      = go_tc_app fuel visited_tcs tc tc_args

      | otherwise
      = NonRecursiveOrUnsure

    go_tc_app :: IntWithInf -> TyConSet -> TyCon -> [Type] -> IsRecDataConResult
    go_tc_app fuel visited_tcs tc tc_args =
      case tyConDataCons_maybe tc of
      --- | pprTrace "tc_app" (vcat [ppr tc, ppr tc_args]) False = undefined
        _ | Just (HetReduction (Reduction _ rhs) _) <- topReduceTyFamApp_maybe fam_envs tc tc_args
          -- This is the only place where we look at tc_args, which might have
          -- See Note [Detecting recursive data constructors], point (C) and (5)
          -> go_arg_ty fuel visited_tcs rhs

        _ | tc == dataConTyCon orig_dc
          -> DefinitelyRecursive -- loop found!

        Just dcs
          | DefinitelyRecursive <- combineIRDCRs [ go_arg_ty fuel visited_tcs' ty | ty <- tc_args ]
              -- Check tc_args, See Note [Detecting recursive data constructors], point (5)
              -- The new visited_tcs', so that we don't recursively check tc,
              -- promising that we will check it below.
              -- Do the tc_args check *before* the dcs check below, otherwise
              -- we might miss an obvious rec occ in tc_args when we run out of
              -- fuel and respond NonRecursiveOrUnsure instead
          -> DefinitelyRecursive

          | fuel >= 0
              -- See Note [Detecting recursive data constructors], point (4)
          , not (tc `elemTyConSet` visited_tcs)
              -- only need to check tc if we haven't visited it already. NB: original visited_tcs
          -> combineIRDCRs [ go_dc (subWithInf fuel 1) visited_tcs' dc | dc <- dcs ]
              -- Finally: check ds

        _ -> NonRecursiveOrUnsure
        where
          visited_tcs' = extendTyConSet visited_tcs tc

{-
************************************************************************
*                                                                      *
\subsection{Worker/wrapper for CPR}
*                                                                      *
************************************************************************
See Note [Worker/wrapper for CPR] for an overview.
-}

mkWWcpr_entry
  :: WwOpts
  -> Type                              -- function body
  -> Cpr                               -- CPR analysis results
  -> UniqSM (Bool,            -- Is w/w'ing useful?
             CoreExpr -> CoreExpr,     -- New wrapper. 'nop_fn' if not useful
             CoreExpr -> CoreExpr)     -- New worker.  'nop_fn' if not useful
-- ^ Entrypoint to CPR W/W. See Note [Worker/wrapper for CPR] for an overview.
mkWWcpr_entry opts body_ty body_cpr
  | not (wo_cpr_anal opts) = return (badWorker, nop_fn, nop_fn)
  | otherwise = do
    -- Part (1)
    res_bndr <- mk_res_bndr body_ty
    let bind_res_bndr body scope = mkDefaultCase body res_bndr scope

    -- Part (2)
    (useful, fromOL -> transit_vars, rebuilt_result, work_unpack_res) <-
      mkWWcpr_one opts res_bndr body_cpr

    -- Part (3)
    let (unbox_transit_tup, transit_tup) = move_transit_vars transit_vars

    -- Stacking unboxer (work_fn) and builder (wrap_fn) together
    let wrap_fn      = unbox_transit_tup rebuilt_result                 -- 3 2
        work_fn body = bind_res_bndr body (work_unpack_res transit_tup) -- 1 2 3
    return $ if not useful
                then (badWorker, nop_fn, nop_fn)
                else (goodWorker, wrap_fn, work_fn)

-- | Part (1) of Note [Worker/wrapper for CPR].
mk_res_bndr :: Type -> UniqSM Id
mk_res_bndr body_ty = do
  -- See Note [Linear types and CPR]
  bndr <- mkSysLocalOrCoVarM ww_prefix cprCaseBndrMult body_ty
  -- See Note [Record evaluated-ness in worker/wrapper]
  pure (setCaseBndrEvald MarkedStrict bndr)

-- | What part (2) of Note [Worker/wrapper for CPR] collects.
--
--   1. A Bool capturing whether the transformation did anything useful.
--   2. The list of transit variables (see the Note).
--   3. The result builder expression for the wrapper.  The original case binder if not useful.
--   4. The result unpacking expression for the worker. 'nop_fn' if not useful.
type CprWwResultOne  = (Bool, OrdList Var,  CoreExpr , CoreExpr -> CoreExpr)
type CprWwResultMany = (Bool, OrdList Var, [CoreExpr], CoreExpr -> CoreExpr)

mkWWcpr :: WwOpts -> [Id] -> [Cpr] -> UniqSM CprWwResultMany
mkWWcpr _opts vars []   =
  -- special case: No CPRs means all top (for example from FlatConCpr),
  -- hence stop WW.
  return (badWorker, toOL vars, map varToCoreExpr vars, nop_fn)
mkWWcpr opts  vars cprs = do
  -- No existentials in 'vars'. 'wantToUnboxResult' should have checked that.
  massertPpr (not (any isTyVar vars)) (ppr vars $$ ppr cprs)
  massertPpr (equalLength vars cprs) (ppr vars $$ ppr cprs)
  (usefuls, varss, rebuilt_results, work_unpack_ress) <-
    unzip4 <$> zipWithM (mkWWcpr_one opts) vars cprs
  return ( or usefuls
         , concatOL varss
         , rebuilt_results
         , foldl' (.) nop_fn work_unpack_ress )

mkWWcpr_one :: WwOpts -> Id -> Cpr -> UniqSM CprWwResultOne
-- ^ See if we want to unbox the result and hand off to 'unbox_one_result'.
mkWWcpr_one opts res_bndr cpr
  | assert (not (isTyVar res_bndr) ) True
  , Unbox dcpc arg_cprs <- wantToUnboxResult (wo_fam_envs opts) (idType res_bndr) cpr
  = unbox_one_result opts res_bndr arg_cprs dcpc
  | otherwise
  = return (badWorker, unitOL res_bndr, varToCoreExpr res_bndr, nop_fn)

unbox_one_result
  :: WwOpts -> Id -> [Cpr] -> DataConPatContext -> UniqSM CprWwResultOne
-- ^ Implements the main bits of part (2) of Note [Worker/wrapper for CPR]
unbox_one_result opts res_bndr arg_cprs
                 DataConPatContext { dcpc_dc = dc, dcpc_tc_args = tc_args
                                   , dcpc_co = co } = do
  -- unboxer (free in `res_bndr`):       |   builder (where <i> builds what was
  --   ( case res_bndr of (i, j) -> )    |            bound to i)
  --   ( case i of I# a ->          )    |
  --   ( case j of I# b ->          )    |     (      (<i>, <j>)      )
  --   ( <hole>                     )    |
  pat_bndrs_uniqs <- getUniquesM
  let (_exs, arg_ids) =
        dataConRepFSInstPat (repeat ww_prefix) pat_bndrs_uniqs cprCaseBndrMult dc tc_args
  massert (null _exs) -- Should have been caught by wantToUnboxResult

  (nested_useful, transit_vars, con_args, work_unbox_res) <-
    mkWWcpr opts arg_ids arg_cprs

  let -- rebuilt_result = (C a b |> sym co)
      rebuilt_result = mkConApp dc (map Type tc_args ++ con_args) `mkCast` mkSymCo co
      -- this_work_unbox_res alt = (case res_bndr |> co of C a b -> <alt>[a,b])
      this_work_unbox_res = mkUnpackCase (Var res_bndr) co cprCaseBndrMult dc arg_ids

  -- Don't try to WW an unboxed tuple return type when there's nothing inside
  -- to unbox further.
  return $ if isUnboxedTupleDataCon dc && not nested_useful
              then ( badWorker, unitOL res_bndr, Var res_bndr, nop_fn )
              else ( goodWorker
                   , transit_vars
                   , rebuilt_result
                   , this_work_unbox_res . work_unbox_res
                   )

-- | Implements part (3) of Note [Worker/wrapper for CPR].
--
-- If `move_transit_vars [a,b] = (unbox, tup)` then
--     * `a` and `b` are the *transit vars* to be returned from the worker
--       to the wrapper
--     * `unbox scrut alt = (case <scrut> of (# a, b #) -> <alt>)`
--     * `tup = (# a, b #)`
-- There is a special case for when there's 1 transit var,
-- see Note [No unboxed tuple for single, unlifted transit var].
move_transit_vars :: [Id] -> (CoreExpr -> CoreExpr -> CoreExpr, CoreExpr)
move_transit_vars vars
  | [var] <- vars
  , let var_ty = idType var
  , isUnliftedType var_ty || exprIsHNF (Var var)
  -- See Note [No unboxed tuple for single, unlifted transit var]
  --   * Wrapper: `unbox scrut alt = (case <scrut> of a -> <alt>)`
  --   * Worker:  `tup = a`
  = ( \build_res wkr_call -> mkDefaultCase wkr_call var build_res
    , varToCoreExpr var ) -- varToCoreExpr important here: var can be a coercion
                          -- Lacking this caused #10658
  | otherwise
  -- The general case: Just return an unboxed tuple from the worker
  --   * Wrapper: `unbox scrut alt = (case <scrut> of (# a, b #) -> <alt>)`
  --   * Worker:  `tup = (# a, b #)`
  = ( \build_res wkr_call -> mkSingleAltCase wkr_call case_bndr
                                    (DataAlt tup_con) vars build_res
    , ubx_tup_app )
   where
    ubx_tup_app = mkCoreUbxTup (map idType vars) (map varToCoreExpr vars)
    tup_con     = tupleDataCon Unboxed (length vars)
    -- See also Note [Linear types and CPR]
    case_bndr   = mkWildValBinder cprCaseBndrMult (exprType ubx_tup_app)


{- Note [Worker/wrapper for CPR]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
'mkWWcpr_entry' is the entry-point to the worker/wrapper transformation that
exploits CPR info. Here's an example:
```
  f :: ... -> (Int, Int)
  f ... = <body>
```
Let's assume the CPR info `body_cpr` for the body of `f` says
"unbox the pair and its components" and `body_ty` is the type of the function
body `body` (i.e., `(Int, Int)`). Then `mkWWcpr_entry body_ty body_cpr` returns

  * A result-unpacking expression for the worker, with a hole for the fun body:
    ```
      unpack body = ( case <body> of r __DEFAULT -> )    -- (1)
                    ( case r of (i, j) ->           )    -- (2)
                    ( case i of I# a ->             )    -- (2)
                    ( case j of I# b ->             )    -- (2)
                    ( (# a, b #)                    )    -- (3)
    ```
  * A result-building expression for the wrapper, with a hole for the worker call:
    ```
      build wkr_call = ( case <wkr_call> of (# a, b #) -> )    -- (3)
                       ( (I# a, I# b)                     )    -- (2)
    ```
  * The result type of the worker, e.g., `(# Int#, Int# #)` above.

To achieve said transformation, 'mkWWcpr_entry'

  1. First allocates a fresh result binder `r`, giving a name to the `body`
     expression and contributing part (1) of the unpacker and builder.
  2. Then it delegates to 'mkWWcpr_one', which recurses into all result fields
     to unbox, contributing the parts marked with (2). Crucially, it knows
     what belongs in the case scrutinee of the unpacker through the communicated
     Id `r`: The unpacking expression will be free in that variable.
     (This is a similar contract as that of 'mkWWstr_one' for strict args.)
  3. 'mkWWstr_one' produces a bunch of *transit vars*: Those result variables
     that have to be transferred from the worker to the wrapper, where the
     constructed result can be rebuilt, `a` and `b` above. Part (3) is
     responsible for tupling them up in the worker and taking the tuple apart
     in the wrapper. This is implemented in 'move_transit_vars'.

Note [No unboxed tuple for single, unlifted transit var]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When there's only a single, unlifted transit var (Note [Worker/wrapper for CPR]),
we don't wrap an unboxed singleton tuple around it (which otherwise would be
needed to suspend evaluation) and return the unlifted thing directly. E.g.
```
  f :: Int -> Int
  f x = x+1
```
We certainly want `$wf :: Int# -> Int#`, not `$wf :: Int# -> (# Int# #)`.
This is OK as long as we know that evaluation of the returned thing terminates
quickly, as is the case for fields of unlifted type like `Int#`.

But more generally, this should also be true for *lifted* types that terminate
quickly! Consider from `T18109`:
```
  data F = F (Int -> Int)
  f :: Int -> F
  f n = F (+n)

  data T = T (Int, Int)
  g :: T -> T
  g t@(T p) = p `seq` t

  data U = U ![Int]
  h :: Int -> U
  h n = U [0..n]
```
All of the nested fields are actually ok-for-speculation and thus OK to
return unboxed instead of in an unboxed singleton tuple:

 1. The field of `F` is a HNF.
    We want `$wf :: Int -> Int -> Int`.
    We get  `$wf :: Int -> (# Int -> Int #)`.
 2. The field of `T` is `seq`'d in `g`.
    We want `$wg :: (Int, Int) -> (Int, Int)`.
    We get  `$wg :: (Int, Int) -> (# (Int, Int) #)`.
 3. The field of `U` is strict and thus always evaluated.
    We want  `$wh :: Int# -> [Int]`.
    We'd get `$wh :: Int# -> (# [Int] #)`.

By considering vars as unlifted that satsify 'exprIsHNF', we catch (3).
Why not check for 'exprOkForSpeculation'? Quite perplexingly, evaluated vars
are not ok-for-spec, see Note [exprOkForSpeculation and evaluated variables].
For (1) and (2) we would have to look at the term. WW only looks at the
type and the CPR signature, so the only way to fix (1) and (2) would be to
have a nested termination signature, like in MR !1866.

Note [Linear types and CPR]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
Remark on linearity: in both the case of the wrapper and the worker,
we build a linear case to unpack constructed products. All the
multiplicity information is kept in the constructors (both C and (#, #)).
In particular (#,#) is parametrised by the multiplicity of its fields.
Specifically, in this instance, the multiplicity of the fields of (#,#)
is chosen to be the same as those of C.


************************************************************************
*                                                                      *
\subsection{Utilities}
*                                                                      *
************************************************************************
-}

mkUnpackCase ::  CoreExpr -> Coercion -> Mult -> DataCon -> [Id] -> CoreExpr -> CoreExpr
-- (mkUnpackCase e co Con args body)
--      returns
-- case e |> co of _dead { Con args -> body }
mkUnpackCase (Tick tickish e) co mult con args body   -- See Note [Profiling and unpacking]
  = Tick tickish (mkUnpackCase e co mult con args body)
mkUnpackCase scrut co mult boxing_con unpk_args body
  = mkSingleAltCase casted_scrut bndr
                    (DataAlt boxing_con) unpk_args body
  where
    casted_scrut = scrut `mkCast` co
    bndr = mkWildValBinder mult (exprType casted_scrut)

-- | The multiplicity of a case binder unboxing a constructed result.
-- See Note [Linear types and CPR]
cprCaseBndrMult :: Mult
cprCaseBndrMult = One

ww_prefix :: FastString
ww_prefix = fsLit "ww"

{- Note [Profiling and unpacking]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If the original function looked like
        f = \ x -> {-# SCC "foo" #-} E

then we want the CPR'd worker to look like
        \ x -> {-# SCC "foo" #-} (case E of I# x -> x)
and definitely not
        \ x -> case ({-# SCC "foo" #-} E) of I# x -> x)

This transform doesn't move work or allocation
from one cost centre to another.

Later [SDM]: presumably this is because we want the simplifier to
eliminate the case, and the scc would get in the way?  I'm ok with
including the case itself in the cost centre, since it is morally
part of the function (post transformation) anyway.
-}
