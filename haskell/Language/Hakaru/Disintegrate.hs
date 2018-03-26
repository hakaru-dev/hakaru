{-# LANGUAGE CPP
           , GADTs
           , EmptyCase
           , KindSignatures
           , DataKinds
           , PolyKinds
           , TypeOperators
           , ScopedTypeVariables
           , Rank2Types
           , MultiParamTypeClasses
           , TypeSynonymInstances
           , FlexibleInstances
           , FlexibleContexts
           , UndecidableInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.06.29
-- |
-- Module      :  Language.Hakaru.Disintegrate
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Disintegration via lazy partial evaluation.
--
-- N.B., the forward direction of disintegration is /not/ just
-- partial evaluation! In the version discussed in the paper we
-- must also ensure that no heap-bound variables occur in the result,
-- which requires using HNFs rather than WHNFs. That condition is
-- sound, but a bit too strict; we could generalize this to handle
-- cases where there may be heap-bound variables remaining in neutral
-- terms, provided we (a) don't end up trying to go both forward
-- and backward on the same variable, and (more importantly) (b)
-- end up with the proper Jacobian. The paper version is rigged to
-- ensure that whenever we recurse into two subexpressions (e.g.,
-- the arguments to addition) one of them has a Jacobian of zero,
-- thus when going from @x*y@ to @dx*y + x*dy@ one of the terms
-- cancels out.
--
-- /Developer's Note:/ To help keep the code clean, we use the
-- worker\/wrapper transform. However, due to complexities in
-- typechecking GADTs, this often confuses GHC if you don't give
-- just the right type signature on definitions. This confusion
-- shows up whenever you get error messages about an \"ambiguous\"
-- choice of 'ABT' instance, or certain types of \"couldn't match
-- @a@ with @a1@\" error messages. To eliminate these issues we use
-- @-XScopedTypeVariables@. In particular, the @abt@ type variable
-- must be bound by the wrapper (i.e., the top-level definition),
-- and the workers should just refer to that same type variable
-- rather than quantifying over abother @abt@ type. In addition,
-- whatever other type variables there are (e.g., the @xs@ and @a@
-- of an @abt xs a@ argument) should be polymorphic in the workers
-- and should /not/ reuse the other analogous type variables bound
-- by the wrapper.
--
-- /Developer's Note:/ In general, we'd like to emit weights and
-- guards \"as early as possible\"; however, determining when that
-- actually is can be tricky. If we emit them way-too-early then
-- we'll get hygiene errors because bindings for the variables they
-- use have not yet been emitted. We can fix these hygiene erors
-- by calling 'atomize', to ensure that all the necessary bindings
-- have already been emitted. But that may still emit things too
-- early, because emitting th variable-binding statements now means
-- that we can't go forward\/backward on them later on; which may
-- cause us to bot unnecessarily. One way to avoid this bot issue
-- is to emit guards\/weights later than necessary, by actually
-- pushing them onto the context (and then emitting them whenever
-- we residualize the context). This guarantees we don't emit too
-- early; but the tradeoff is we may end up generating duplicate
-- code by emitting too late. One possible (currently unimplemented)
-- solution to that code duplication issue is to let these statements
-- be emitted too late, but then have a post-processing step to
-- lift guards\/weights up as high as they can go. To avoid problems
-- about testing programs\/expressions for equality, we can use a
-- hash-consing trick so we keep track of the identity of guard\/weight
-- statements, then we can simply compare those identities and only
-- after the lifting do we replace the identity hash with the actual
-- statement.
----------------------------------------------------------------
module Language.Hakaru.Disintegrate
    ( lam_
    -- * the Hakaru API
    , disintegrateWithVar
    , disintegrate, disintegrateInCtx
    , densityWithVar
    , density, densityInCtx
    , observe, observeInCtx
    , determine
    
    -- * Implementation details
    , perform
    , atomize
    , constrainValue
    , constrainOutcome
    ) where

#if __GLASGOW_HASKELL__ < 710
import           Data.Functor         ((<$>))
import           Data.Foldable        (Foldable, foldMap)
import           Data.Traversable     (Traversable)
import           Control.Applicative  (Applicative(..))
#endif
import           Control.Applicative  (Alternative(..))
import           Control.Monad        ((<=<), guard)
import           Data.Functor.Compose (Compose(..))
import qualified Data.Traversable     as T
import           Data.List.NonEmpty   (NonEmpty(..))
import qualified Data.List.NonEmpty   as L
import qualified Data.Text            as Text
import qualified Data.IntMap          as IM
import           Data.Sequence        (Seq)
import qualified Data.Sequence        as S
import           Data.Proxy           (KProxy(..))
import           Data.Maybe           (fromMaybe, fromJust)

import Language.Hakaru.Syntax.IClasses
import Data.Number.Natural
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing
import qualified Language.Hakaru.Types.Coercion as C
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Syntax.TypeOf
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.DatumCase (DatumEvaluator, MatchResult(..), matchBranches)
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.Transform (TransformCtx(..), minimalCtx)
import Language.Hakaru.Evaluation.Types
import Language.Hakaru.Evaluation.Lazy
import Language.Hakaru.Evaluation.DisintegrationMonad
import qualified Language.Hakaru.Syntax.Prelude as P
import qualified Language.Hakaru.Expect         as E

#ifdef __TRACE_DISINTEGRATE__
import qualified Text.PrettyPrint     as PP
import Language.Hakaru.Pretty.Haskell
import Debug.Trace                    (trace, traceM)
#endif


----------------------------------------------------------------

lam_ :: (ABT Term abt) => Variable a -> abt '[] b -> abt '[] (a ':-> b)
lam_ x e = syn (Lam_ :$ bind x e :* End)


-- | Disintegrate a measure over pairs with respect to the lebesgue
-- measure on the first component. That is, for each measure kernel
-- @n <- disintegrate m@ we have that @m == bindx lebesgue n@. The
-- first two arguments give the hint and type of the lambda-bound
-- variable in the result. If you want to automatically fill those
-- in, then see 'disintegrate'.
--
-- N.B., the resulting functions from @a@ to @'HMeasure b@ are
-- indeed measurable, thus it is safe\/appropriate to use Hakaru's
-- @(':->)@ rather than Haskell's @(->)@.
--
-- BUG: Actually, disintegration is with respect to the /Borel/
-- measure on the first component of the pair! Alas, we don't really
-- have a clean way of describing this since we've no primitive
-- 'MeasureOp' for Borel measures.
--
-- /Developer's Note:/ This function fills the role that the old
-- @runDisintegrate@ did (as opposed to the old function called
-- @disintegrate@). [Once people are familiar enough with the new
-- code base and no longer recall what the old code base was doing,
-- this note should be deleted.]
disintegrateWithVar
    :: (ABT Term abt)
    => TransformCtx
    -> Text.Text
    -> Sing a
    -> abt '[] ('HMeasure (HPair a b))
    -> [abt '[] (a ':-> 'HMeasure b)]
disintegrateWithVar ctx hint typ m =
    let x = Variable hint (nextFreeOrBind m) typ
    in map (lam_ x) . flip (runDisInCtx ctx) [Some2 m, Some2 (var x)] $ do
        ab <- perform m
#ifdef __TRACE_DISINTEGRATE__
        ss <- getStatements
        trace ("-- disintegrate: finished perform\n"
            ++ show (pretty_Statements ss PP.$+$ PP.sep(prettyPrec_ 11 ab))
            ++ "\n") $ return ()
#endif
        (a,b) <- emitUnpair ab
#ifdef __TRACE_DISINTEGRATE__
        trace ("-- disintegrate: finished emitUnpair: "
            ++ show (pretty a, pretty b)) $ return ()
#endif
        constrainValue (var x) a
#ifdef __TRACE_DISINTEGRATE__
        ss <- getStatements
        extras <- getExtras
        traceM ("-- disintegrate: finished constrainValue\n"
                ++ show (pretty_Statements ss) ++ "\n"
                ++ show (prettyExtras extras)
               )
#endif
        return b


-- | A variant of 'disintegrateWithVar' which automatically computes
-- the type via 'typeOf'.
disintegrateInCtx
    :: (ABT Term abt)
    => TransformCtx
    -> abt '[] ('HMeasure (HPair a b))
    -> [abt '[] (a ':-> 'HMeasure b)]
disintegrateInCtx ctx m =
    disintegrateWithVar
        ctx
        Text.empty
        (fst . sUnPair . sUnMeasure $ typeOf m) -- TODO: change the exception thrown form 'typeOf' so that we know it comes from here
        m

-- | A variant of 'disintegrateInCtx' which takes the context to be the minimal
-- one. Calling this function is only really valid on top-level programs, or
-- subprograms in which the enclosing program doesn't bind any variables.
disintegrate
    :: (ABT Term abt)
    => abt '[] ('HMeasure (HPair a b))
    -> [abt '[] (a ':-> 'HMeasure b)]
disintegrate = disintegrateInCtx minimalCtx

-- | Return the density function for a given measure. The first two
-- arguments give the hint and type of the lambda-bound variable
-- in the result. If you want to automatically fill those in, then
-- see 'density'.
--
-- TODO: is the resulting function guaranteed to be measurable? If
-- so, update this documentation to reflect that fact; if not, then
-- we should make it into a Haskell function instead.
densityWithVar
    :: (ABT Term abt)
    => TransformCtx
    -> Text.Text
    -> Sing a
    -> abt '[] ('HMeasure a)
    -> [abt '[] (a ':-> 'HProb)]
densityWithVar ctx hint typ m =
    let x = Variable hint (nextFree m `max` nextBind m) typ
    in (lam_ x . E.total) <$> observeInCtx ctx m (var x)


-- | A variant of 'densityWithVar' which automatically computes the
-- type via 'typeOf'.
densityInCtx
    :: (ABT Term abt)
    => TransformCtx
    -> abt '[] ('HMeasure a)
    -> [abt '[] (a ':-> 'HProb)]
densityInCtx ctx m =
    densityWithVar
        ctx
        Text.empty
        (sUnMeasure $ typeOf m)
        m

density
    :: (ABT Term abt)
    => abt '[] ('HMeasure a)
    -> [abt '[] (a ':-> 'HProb)]
density = densityInCtx minimalCtx

-- | Constrain a measure such that it must return the observed
-- value. In other words, the resulting measure returns the observed
-- value with weight according to its density in the original
-- measure, and gives all other values weight zero.
observeInCtx
    :: (ABT Term abt)
    => TransformCtx
    -> abt '[] ('HMeasure a)
    -> abt '[] a
    -> [abt '[] ('HMeasure a)]
observeInCtx ctx m x =
    runDisInCtx ctx (constrainOutcome x m >> return x) [Some2 m, Some2 x]

observe
    :: (ABT Term abt)
    => abt '[] ('HMeasure a)
    -> abt '[] a
    -> [abt '[] ('HMeasure a)]
observe = observeInCtx minimalCtx

-- | Arbitrarily choose one of the possible alternatives. In the
-- future, this function should be replaced by a better one that
-- takes some sort of strategy for deciding which alternative to
-- choose.
determine :: (ABT Term abt) => [abt '[] a] -> Maybe (abt '[] a)
determine []    = Nothing
determine (m:_) = Just m


----------------------------------------------------------------
----------------------------------------------------------------

-- N.B., forward disintegration is not identical to partial evaluation,
-- as noted at the top of the file. For correctness we need to
-- ensure the result is emissible (i.e., has no heap-bound variables).
-- More specifically, we need to ensure emissibility in the places
-- where we call 'emitMBind'
evaluate_ :: (ABT Term abt) => TermEvaluator abt (Dis abt)
evaluate_ = evaluate perform

evaluateDatum :: (ABT Term abt) => DatumEvaluator (abt '[]) (Dis abt)
evaluateDatum e = viewWhnfDatum <$> evaluate_ e

-- | Simulate performing 'HMeasure' actions by simply emitting code
-- for those actions, returning the bound variable.
--
-- This is the function called @(|>>)@ in the disintegration paper.
perform :: forall abt. (ABT Term abt) => MeasureEvaluator abt (Dis abt)
perform = \e0 ->
#ifdef __TRACE_DISINTEGRATE__
    getStatements >>= \ss ->
    getExtras >>= \extras ->
    getIndices >>= \inds ->
    trace ("\n-- perform --\n"
        ++ "at " ++ show (ppInds inds) ++ "\n"
        ++ show (prettyExtras extras) ++ "\n"
        ++ show (pretty_Statements_withTerm ss e0)
        ++ "\n") $
#endif
    caseVarSyn e0 performVar performTerm
    where
    performTerm :: forall a. Term abt ('HMeasure a) -> Dis abt (Whnf abt a)
    performTerm (Dirac :$ e1 :* End)       = evaluate_ e1
    performTerm (MeasureOp_ o :$ es)       = performMeasureOp o es
    performTerm (MBind :$ e1 :* e2 :* End) =
        caseBind e2 $ \x e2' -> do
            inds <- getIndices
            push (SBind x (Thunk e1) inds) e2' >>= perform

    performTerm (Plate :$ e1 :* e2 :* End) =  do
      x1 <- pushPlate e1 e2
      return $ fromJust (toWhnf x1)

    performTerm (Superpose_ pes) = do
        inds <- getIndices
        if not (null inds) && L.length pes > 1 then bot else
          emitFork_ (P.superpose . fmap ((,) P.one))
                    (fmap (\(p,e) -> push (SWeight (Thunk p) inds) e >>= perform)
                          pes)

    -- Avoid falling through to the @performWhnf <=< evaluate_@ case
    performTerm (Let_ :$ e1 :* e2 :* End) =
        caseBind e2 $ \x e2' -> do
            inds <- getIndices
            push (SLet x (Thunk e1) inds) e2' >>= perform

    -- TODO: we could optimize this by calling some @evaluateTerm@
    -- directly, rather than calling 'syn' to rebuild @e0@ from
    -- @t0@ and then calling 'evaluate_' (which will just use
    -- 'caseVarSyn' to get the @t0@ back out from the @e0@).
    performTerm t0 = do
        w <- evaluate_ (syn t0)
#ifdef __TRACE_DISINTEGRATE__
        trace ("-- perform: finished evaluate, with:\n" ++ show (PP.sep(prettyPrec_ 11 w))) $ return ()
#endif
        performWhnf w


    performVar :: forall a. Variable ('HMeasure a) -> Dis abt (Whnf abt a)
    performVar = performWhnf <=< evaluateVar perform evaluate_

    performWhnf
        :: forall a. Whnf abt ('HMeasure a) -> Dis abt (Whnf abt a)
    performWhnf (Head_   v) = perform $ fromHead v
    performWhnf (Neutral e) = (Neutral . var) <$>
                              (emitMBind . fromWhnf =<< atomize e)


    -- TODO: right now we do the simplest thing. However, for better
    -- coverage and cleaner produced code we'll need to handle each
    -- of the ops separately. (For example, see how 'Uniform' is
    -- handled in the old code; how it has two options for what to
    -- do.)
    performMeasureOp
        :: forall typs args a
        .  (typs ~ UnLCs args, args ~ LCs typs)
        => MeasureOp typs a
        -> SArgs abt args
        -> Dis abt (Whnf abt a)
    performMeasureOp = \o es -> nice o es <|> complete o es
        where
        -- Try to generate nice pretty output.
        nice
            :: MeasureOp typs a
            -> SArgs abt args
            -> Dis abt (Whnf abt a)
        nice o es = do
            es' <- traverse21 atomizeCore es
            x   <- emitMBind2 $ syn (MeasureOp_ o :$ es')
            -- return (Neutral $ var x)
            return (Neutral x)

        -- Try to be as complete as possible (i.e., 'bot' as little as
        -- possible), no matter how ugly the output code gets.
        complete
            :: MeasureOp typs a
            -> SArgs abt args
            -> Dis abt (Whnf abt a)
        complete Normal = \(mu :* sd :* End) -> do
            x <- var <$> emitMBind P.lebesgue
            pushWeight (P.densityNormal mu sd x)
            return (Neutral x)
        complete Uniform = \(lo :* hi :* End) -> do
            x <- var <$> emitMBind P.lebesgue
            pushGuard (lo P.< x P.&& x P.< hi)
            pushWeight (P.densityUniform lo hi x)
            return (Neutral x)
        complete _ = \_ -> bot
                               

-- | The goal of this function is to ensure the correctness criterion
-- that given any term to be emitted, the resulting term is
-- semantically equivalent but contains no heap-bound variables.
-- That correctness criterion is necessary to ensure hygiene\/scoping.
--
-- This particular implementation calls 'evaluate' recursively,
-- giving us something similar to full-beta reduction. However,
-- that is considered an implementation detail rather than part of
-- the specification of what the function should do. Also, it's a
-- gross hack and prolly a big part of why we keep running into
-- infinite looping issues.
--
-- This name is taken from the old finally tagless code, where
-- \"atomic\" terms are (among other things) emissible; i.e., contain
-- no heap-bound variables.
--
-- BUG: this function infinitely loops in certain circumstances
-- (namely when dealing with neutral terms)
atomize :: (ABT Term abt) => TermEvaluator abt (Dis abt)
atomize e =
#ifdef __TRACE_DISINTEGRATE__
    trace ("\n-- atomize --\n" ++ show (pretty e)) $
#endif
    do whnf <- evaluate_ e
       case whnf of
         Head_ v   -> Head_ <$> traverse21 atomizeCore v
         Neutral e -> Neutral . unviewABT <$>
                      traverse12 (traverse21 atomizeCore) (viewABT e)             


-- | A variant of 'atomize' which is polymorphic in the locally
-- bound variables @xs@ (whereas 'atomize' requires @xs ~ '[]@).
-- We factored this out because we often want this more polymorphic
-- variant when using our indexed @TraversableMN@ classes.
atomizeCore :: (ABT Term abt) => abt xs a -> Dis abt (abt xs a)
atomizeCore e =
    -- HACK: this check for 'disjointVarSet' is sufficient to catch
    -- the particular infinite loops we were encountering, but it
    -- will not catch all of them. If the call to 'evaluate_' in
    -- 'atomize' returns a neutral term which contains heap-bound
    -- variables, then we'll still loop forever since we don't
    -- traverse\/fmap over the top-level term constructor of neutral
    -- terms.    
 do xs <- getHeapVars
    vs <- extFreeVars e
    if disjointVarSet xs vs
        then return e
        else
            let (ys, e') = caseBinds e
            in
#ifdef __TRACE_DISINTEGRATE__
               trace ("\n-- atomizeCore --\n" ++ show (pretty e')) $
#endif
               (binds_ ys . fromWhnf) <$> atomize e'
    where
    -- TODO: does @IM.null . IM.intersection@ fuse correctly?
    disjointVarSet xs ys =
        IM.null (IM.intersection (unVarSet xs) (unVarSet ys))

-- HACK: if we really want to go through with this approach, then
-- we should memoize the set of heap-bound variables in the
-- 'ListContext' itself rather than recomputing it every time!
getHeapVars :: Dis abt (VarSet ('KProxy :: KProxy Hakaru))
getHeapVars =
    Dis $ \_ c h -> c (foldMap statementVars (statements h)) h

----------------------------------------------------------------
-- | Given an emissible term @v0@ (the first argument) and another
-- term @e0@ (the second argument), compute the constraints such
-- that @e0@ must evaluate to @v0@. This is the function called
-- @(<|)@ in the disintegration paper, though notably we swap the
-- argument order so that the \"value\" is the first argument.
--
-- N.B., this function assumes (and does not verify) that the first
-- argument is emissible. So callers (including recursive calls)
-- must guarantee this invariant, by calling 'atomize' as necessary.
--
-- TODO: capture the emissibility requirement on the first argument
-- in the types, to help avoid accidentally passing the arguments
-- in the wrong order!
constrainValue :: (ABT Term abt) => abt '[] a -> abt '[] a -> Dis abt ()
constrainValue v0 e0 =
#ifdef __TRACE_DISINTEGRATE__
    getStatements >>= \ss ->
    getExtras >>= \extras ->
    getIndices >>= \inds ->
    trace ("\n-- constrainValue: " ++ show (pretty v0) ++ "\n"           
        ++ show (pretty_Statements_withTerm ss e0) ++ "\n"
        ++ "at " ++ show (ppInds inds) ++ "\n"
        ++ show (prettyExtras extras) ++ "\n"
          ) $
#endif
    caseVarSyn e0 (constrainVariable v0) $ \t ->
        case t of
        -- There's a bunch of stuff we don't even bother trying to handle
        Empty_   _               -> error "TODO: disintegrate empty arrays"
        Array_   n e             ->
            caseBind e $ \x body -> do j <- freshInd n
                                       let x'    = indVar j
                                       body' <- extSubst x (var x') body
                                       inds  <- getIndices
                                       withIndices (extendIndices j inds) $
                                                   constrainValue (v0 P.! (var x')) body'
                                                   -- TODO use meta-index
        ArrayLiteral_ _          -> error "TODO: disintegrate literal arrays"
        ArrayOp_ o :$ args       -> constrainValueArrayOp v0 o args
        Lam_  :$ _  :* End       -> error "TODO: disintegrate lambdas"
        App_  :$ _  :* _ :* End  -> error "TODO: disintegrate lambdas"
        Integrate :$ _ :* _ :* _ :* End ->
            error "TODO: disintegrate integration"
        Summate _ _ :$ _ :* _ :* _ :* End ->
            error "TODO: disintegrate integration"


        -- N.B., the semantically correct definition is:
        --
        -- > Literal_ v
        -- >     | "dirac v has a density wrt the ambient measure" -> ...
        -- >     | otherwise -> bot
        --
        -- For the case where the ambient measure is Lebesgue, dirac
        -- doesn't have a density, so we return 'bot'. However, we
        -- will need to generalize this when we start handling other
        -- ambient measures.
        Literal_ v               -> bot -- unsolvable. (kinda; see note)
        Datum_   d               -> constrainDatum v0 d
        Dirac :$ _ :* End        -> bot -- giving up.
        MBind :$ _ :* _ :* End   -> bot -- giving up.
        MeasureOp_ o :$ es       -> constrainValueMeasureOp v0 o es
        Superpose_ pes           -> bot -- giving up.
        Reject_ _                -> bot -- giving up.
        Let_ :$ e1 :* e2 :* End ->
            caseBind e2 $ \x e2' ->
                push (SLet x (Thunk e1) []) e2' >>= constrainValue v0

        CoerceTo_   c :$ e1 :* End ->
            -- TODO: we need to insert some kind of guard that says
            -- @v0@ is in the range of @coerceTo c@, or equivalently
            -- that @unsafeFrom c v0@ will always succeed. We need
            -- to emit this guard (for correctness of the generated
            -- program) because if @v0@ isn't in the range of the
            -- coercion, then there's no possible way the program
            -- @e1@ could in fact be observed at @v0@. The only
            -- question is how to perform that check; for the
            -- 'Signed' coercions it's easy enough, but for the
            -- 'Continuous' coercions it's not really clear.
            constrainValue (P.unsafeFrom_ c v0) e1
        UnsafeFrom_ c :$ e1 :* End ->
            -- TODO: to avoid returning garbage, we'd need to place
            -- some constraint on @e1@ so that if the original
            -- program would've crashed due to a bad unsafe-coercion,
            -- then we won't return a disintegrated program (since
            -- it too should always crash). Avoiding this check is
            -- sound (i.e., if the input program is well-formed
            -- then the output program is a well-formed disintegration),
            -- it just overgeneralizes.
            constrainValue  (P.coerceTo_ c v0) e1
        NaryOp_     o    es        -> constrainNaryOp v0 o es
        PrimOp_     o :$ es        -> constrainPrimOp v0 o es

        Transform_ t :$ _            -> error $
          concat["constrainValue{", show t, "}"
                ,": cannot yet disintegrate transforms; expand them first"]

        Case_ e bs ->
            -- First we try going forward on the scrutinee, to make
            -- pretty resulting programs; but if that doesn't work
            -- out, we fall back to just constraining the branches.
            do  match <- matchBranches evaluateDatum e bs
                case match of
                    Nothing ->
                        -- If desired, we could return the Hakaru program
                        -- that always crashes, instead of throwing a
                        -- Haskell error.
                        error "constrainValue{Case_}: nothing matched!"
                    Just GotStuck ->
                        constrainBranches v0 e bs
                    Just (Matched rho body) ->
                        pushes (toVarStatements rho) body >>= constrainValue v0
            <|> constrainBranches v0 e bs

        _ :$ _ -> error "constrainValue: the impossible happened"


-- | The default way of doing 'constrainValue' on a 'Case_' expression:
-- by constraining each branch. To do this we rely on the fact that
-- we're in a 'HMeasure' context (i.e., the continuation produces
-- programs of 'HMeasure' type). For each branch we first assert the
-- branch's pattern holds (via 'SGuard') and then call 'constrainValue'
-- on the body of the branch; and the final program is the superposition
-- of all these branches.
--
-- TODO: how can we avoid duplicating the scrutinee expression?
-- Would pushing a 'SLet' statement before the superpose be sufficient
-- to achieve maximal sharing?
constrainBranches
    :: (ABT Term abt)
    => abt '[] a
    -> abt '[] b
    -> [Branch b abt a]
    -> Dis abt ()
constrainBranches v0 e = choose . map constrainBranch
    where
    constrainBranch (Branch pat body) =
        let (vars,body') = caseBinds body
        in push (SGuard vars pat (Thunk e) []) body'
               >>= constrainValue v0


constrainDatum
    :: (ABT Term abt) => abt '[] a -> Datum (abt '[]) a -> Dis abt ()
constrainDatum v0 d =
    case patternOfDatum d of
    PatternOfDatum pat es -> do
        xs <- freshVars $ fmap11 (Hint Text.empty . typeOf) es
        emit_ $ \body ->
            syn $ Case_ v0
                [ Branch pat (binds_ xs body)
                , Branch PWild (P.reject $ (typeOf body))
                ]
        constrainValues xs es

constrainValues
    :: (ABT Term abt)
    => List1 Variable  xs
    -> List1 (abt '[]) xs
    -> Dis abt ()
constrainValues (Cons1 x xs) (Cons1 e es) =
    constrainValue (var x) e >> constrainValues xs es
constrainValues Nil1 Nil1 = return ()
constrainValues _ _ = error "constrainValues: the impossible happened"


data PatternOfDatum (ast :: Hakaru -> *) (a :: Hakaru) =
    forall xs. PatternOfDatum
        !(Pattern xs a)
        !(List1 ast xs)

-- | Given a datum, return the pattern which will match it along
-- with the subexpressions which would be bound to patter-variables.
patternOfDatum :: Datum ast a -> PatternOfDatum ast a
patternOfDatum =
    \(Datum hint _typ d) ->
        podCode d $ \p es ->
        PatternOfDatum (PDatum hint p) es
    where
    podCode
        :: DatumCode xss ast a
        -> (forall bs. PDatumCode xss bs a -> List1 ast bs -> r)
        -> r
    podCode (Inr d) k = podCode   d $ \ p es -> k (PInr p) es
    podCode (Inl d) k = podStruct d $ \ p es -> k (PInl p) es

    podStruct
        :: DatumStruct xs ast a
        -> (forall bs. PDatumStruct xs bs a -> List1 ast bs -> r)
        -> r
    podStruct (Et d1 d2) k =
        podFun    d1 $ \p1 es1 ->
        podStruct d2 $ \p2 es2 ->
        k (PEt p1 p2) (es1 `append1` es2)
    podStruct Done k = k PDone Nil1

    podFun
        :: DatumFun x ast a
        -> (forall bs. PDatumFun x bs a -> List1 ast bs -> r)
        -> r
    podFun (Konst e) k = k (PKonst PVar) (Cons1 e Nil1)
    podFun (Ident e) k = k (PIdent PVar) (Cons1 e Nil1)


----------------------------------------------------------------
-- | N.B., as with 'constrainValue', we assume that the first
-- argument is emissible. So it is the caller's responsibility to
-- ensure this (by calling 'atomize' as appropriate).
--
-- TODO: capture the emissibility requirement on the first argument
-- in the types.
constrainVariable
    :: (ABT Term abt) => abt '[] a -> Variable a -> Dis abt ()
constrainVariable v0 x =
    do extras <- getExtras
    -- If we get 'Nothing', then it turns out @x@ is a free variable.
    -- If @x@ is a free variable, then it's a neutral term; and we
    -- return 'bot' for neutral terms
       maybe bot lookForLoc (lookupAssoc x extras)
    where lookForLoc (Loc      l jxs) =
              -- If we get 'Nothing', then it turns out @l@ is a free
              -- location. This is an error because of the
              -- invariant:
              --   if there exists an 'Assoc x (Loc l _)' inside @extras@
              --   then there must be a statement on the 'ListContext' that binds @l@
              (maybe (freeLocError l) return =<<) . select l $ \s ->
                  case s of
                    SBind l' e ixs -> do
                           Refl <- locEq l l'
                           guard (length ixs == length jxs) -- will error otherwise
                           Just $ do
                             inds <- getIndices
                             guard (jxs `permutes` inds) -- will bot otherwise
                             e' <- apply ixs inds (fromLazy e)
                             constrainOutcome v0 e'
                             unsafePush (SLet l (Whnf_ (Neutral v0)) inds)
                    SLet  l' e ixs -> do
                           Refl <- locEq l l'
                           guard (length ixs == length jxs) -- will error otherwise
                           Just $ do
                             inds <- getIndices
                             guard (jxs `permutes` inds) -- will bot otherwise
                             e' <- apply ixs inds (fromLazy e)
                             constrainValue v0 e'
                             unsafePush (SLet l (Whnf_ (Neutral v0)) inds)
                    SWeight _ _ -> Nothing
                    SGuard ls' pat scrutinee i -> error "TODO: constrainVariable{SGuard}"

----------------------------------------------------------------
-- | N.B., as with 'constrainValue', we assume that the first
-- argument is emissible. So it is the caller's responsibility to
-- ensure this (by calling 'atomize' as appropriate).
--
-- TODO: capture the emissibility requirement on the first argument
-- in the types.
constrainValueArrayOp
    :: forall abt typs args a
    .  (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => abt '[] a
    -> ArrayOp typs a
    -> SArgs abt args
    -> Dis abt ()
constrainValueArrayOp v0 = go
    where
      go :: ArrayOp typs a -> SArgs abt args -> Dis abt ()
      go (Index  _) (e1 :* e2 :* End) = do
        w1 <- evaluate_ e1
        case w1 of
          Neutral e1' -> bot
          Head_ (WArray _ b) -> caseBind b $ \x body ->
                                extSubst x e2 body >>= constrainValue v0
          Head_ (WEmpty _) -> bot -- TODO: check this
          Head_ a@(WArrayLiteral _) -> constrainValueIdxArrLit v0 e2 a
          _ -> error "constrainValue {ArrayOp Index}: uknown whnf of array type"
      go (Size   _) _ = error "TODO: disintegrate {ArrayOp Size}"
      go (Reduce _) _ = error "TODO: disintegrate {ArrayOp Reduce}"
      go _ _ = error "constrainValueArrayOp: unknown arrayOp"


-- | Special case for [true,false] ! i, and [false, true] ! i
-- This helps us disintegrate bern                                                    
constrainValueIdxArrLit
     :: forall abt a
     .  (ABT Term abt)
     => abt '[] a
     -> abt '[] 'HNat
     -> Head abt ('HArray a)
     -> Dis abt ()
constrainValueIdxArrLit v0 e2 = go
    where
      go :: Head abt ('HArray a) -> Dis abt ()
      go (WArrayLiteral [a1,a2]) =
          case (jmEq1 (typeOf v0) sBool) of
            Just Refl ->
                let constrainInd = flip constrainValue e2
                in case (isLitBool a1, isLitBool a2) of
                     (Just b1, Just b2)
                         | isLitTrue b1 && isLitFalse b2 ->
                             constrainInd $ P.if_ v0 (P.nat_ 0) (P.nat_ 1) 
                         | isLitTrue b2 && isLitFalse b1 ->
                             constrainInd $ P.if_ v0 (P.nat_ 1) (P.nat_ 0)
                         | otherwise -> error "constrainValue: cannot invert (Index [b,b] i)"
                     _ -> error "TODO: constrainValue (Index [b1,b2] i)"
            Nothing -> error "TODO: constrainValue (Index [a1,a2] i)"
      go (WArrayLiteral _) = bot
      go _ = error "constrainValueIdxArrLit: unknown ArrayLiteral form"

-- | Helpers for disintegrating bern             
isLitBool :: (ABT Term abt) => abt '[] a -> Maybe (Datum (abt '[]) HBool)
isLitBool e = caseVarSyn e (const Nothing) $ \b ->
                  case b of
                    Datum_ d@(Datum _ typ _) -> case (jmEq1 typ sBool) of
                                                  Just Refl -> Just d
                                                  Nothing   -> Nothing
                    _ -> Nothing

isLitTrue :: (ABT Term abt) => Datum (abt '[]) HBool -> Bool
isLitTrue (Datum tdTrue sBool (Inl Done)) = True
isLitTrue _                               = False

isLitFalse :: (ABT Term abt) => Datum (abt '[]) HBool -> Bool
isLitFalse (Datum tdFalse sBool (Inr (Inl Done))) = True
isLitFalse _                                      = False             

----------------------------------------------------------------
-- | N.B., as with 'constrainValue', we assume that the first
-- argument is emissible. So it is the caller's responsibility to
-- ensure this (by calling 'atomize' as appropriate).
--
-- TODO: capture the emissibility requirement on the first argument
-- in the types.
constrainValueMeasureOp
    :: forall abt typs args a
    .  (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => abt '[] ('HMeasure a)
    -> MeasureOp typs a
    -> SArgs abt args
    -> Dis abt ()
constrainValueMeasureOp v0 = go
    where
    -- TODO: for Lebesgue and Counting we use @bot@ because that's
    -- what the old finally-tagless code seems to have been doing.
    -- But is that right, or should they really be @return ()@?
    go :: MeasureOp typs a -> SArgs abt args -> Dis abt ()
    go Lebesgue    = \(e1 :* e2 :* End) ->
        constrainValue v0 (P.lebesgue' e1 e2)
    go Counting    = \End               -> bot -- TODO: see note above
    go Categorical = \(e1 :* End)       ->
        constrainValue v0 (P.categorical e1)
    go Uniform     = \(e1 :* e2 :* End) ->
        constrainValue v0 (P.uniform' e1 e2)
    go Normal      = \(e1 :* e2 :* End) ->
        constrainValue v0 (P.normal'  e1 e2)
    go Poisson     = \(e1 :* End)       ->
        constrainValue v0 (P.poisson' e1)
    go Gamma       = \(e1 :* e2 :* End) ->
        constrainValue v0 (P.gamma'   e1 e2)
    go Beta        = \(e1 :* e2 :* End) ->
        constrainValue v0 (P.beta'    e1 e2)

----------------------------------------------------------------
-- | N.B., We assume that the first argument, @v0@, is already
-- atomized. So, this must be ensured before recursing, but we can
-- assume it's already been done by the IH.
--
-- N.B., we also rely on the fact that our 'HSemiring' instances
-- are actually all /commutative/ semirings. If that ever becomes
-- not the case, then we'll need to fix things here.
--
-- As written, this will do a lot of redundant work in atomizing
-- the subterms other than the one we choose to go backward on.
-- Because evaluation has side-effects on the heap and is heap
-- dependent, it seems like there may not be a way around that
-- issue. (I.e., we could use dynamic programming to efficiently
-- build up the 'M' computations, but not to evaluate them.) Of
-- course, really we shouldn't be relying on the structure of the
-- program here; really we should be looking at the heap-bound
-- variables in the term: choosing each @x@ to go backward on, treat
-- the term as a function of @x@, atomize that function (hence going
-- forward on the rest of the variables), and then invert it and
-- get the Jacobian.
--
-- TODO: find some way to capture in the type that the first argument
-- must be emissible.
constrainNaryOp
    :: (ABT Term abt)
    => abt '[] a
    -> NaryOp a
    -> Seq (abt '[] a)
    -> Dis abt ()
constrainNaryOp v0 o =
    case o of
    Sum theSemi ->
        lubSeq $ \es1 e es2 -> do
            u <- atomize $ syn (NaryOp_ (Sum theSemi) (es1 S.>< es2))
            v <- evaluate_ $ P.unsafeMinus_ theSemi v0 (fromWhnf u)
            constrainValue (fromWhnf v) e
    Prod theSemi ->
        lubSeq $ \es1 e es2 -> do
            u <- atomize $ syn (NaryOp_ (Prod theSemi) (es1 S.>< es2))
            let u' = fromWhnf u -- TODO: emitLet?
            emitWeight $ P.recip (toProb_abs theSemi u')
            v <- evaluate_ $ P.unsafeDiv_ theSemi v0 u'
            constrainValue (fromWhnf v) e
    Max theOrd ->
        chooseSeq $ \es1 e es2 -> do
            u <- atomize $ syn (NaryOp_ (Max theOrd) (es1 S.>< es2))
            emitGuard $ P.primOp2_ (Less theOrd) (fromWhnf u) v0
            constrainValue v0 e
    _ -> error $ "TODO: constrainNaryOp{" ++ show o ++ "}"


-- TODO: if this function (or the component @toProb@ and @semiringAbs@
-- parts) turn out to be useful elsewhere, then we should move it
-- to the Prelude.
toProb_abs :: (ABT Term abt) => HSemiring a -> abt '[] a -> abt '[] 'HProb
toProb_abs HSemiring_Nat  = P.nat2prob
toProb_abs HSemiring_Int  = P.nat2prob . P.abs_
toProb_abs HSemiring_Prob = id
toProb_abs HSemiring_Real = P.abs_


-- TODO: is there any way to optimise the zippering over the Seq, a la
-- 'S.inits' or 'S.tails'?
-- TODO: really we want a dynamic programming
-- approach to avoid unnecessary repetition of calling @evaluateNaryOp
-- evaluate_@ on the two subsequences...
lubSeq :: (Alternative m) => (Seq a -> a -> Seq a -> m b) -> Seq a -> m b
lubSeq f = go S.empty
    where
    go xs ys =
        case S.viewl ys of
        S.EmptyL   -> empty
        y S.:< ys' -> f xs y ys' <|> go (xs S.|> y) ys'

chooseSeq :: (ABT Term abt)
          => (Seq a -> a -> Seq a -> Dis abt b)
          -> Seq a
          -> Dis abt b
chooseSeq f = choose  . go S.empty
    where
    go xs ys =
        case S.viewl ys of
        S.EmptyL   -> []
        y S.:< ys' -> f xs y ys' : go (xs S.|> y) ys'


----------------------------------------------------------------
-- HACK: for a lot of these, we can't use the prelude functions
-- because Haskell can't figure out our polymorphism, so we have
-- to define our own versions for manually passing dictionaries
-- around.
--
-- | N.B., We assume that the first argument, @v0@, is already
-- atomized. So, this must be ensured before recursing, but we can
-- assume it's already been done by the IH.
--
-- TODO: find some way to capture in the type that the first argument
-- must be emissible.
constrainPrimOp
    :: forall abt typs args a
    .  (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => abt '[] a
    -> PrimOp typs a
    -> SArgs abt args
    -> Dis abt ()
constrainPrimOp v0 = go
    where
    error_TODO op = error $ "TODO: constrainPrimOp{" ++ op ++"}"

    go :: PrimOp typs a -> SArgs abt args -> Dis abt ()
    go Not  = \(e1 :* End)       -> error_TODO "Not"
    go Impl = \(e1 :* e2 :* End) -> error_TODO "Impl"
    go Diff = \(e1 :* e2 :* End) -> error_TODO "Diff"
    go Nand = \(e1 :* e2 :* End) -> error_TODO "Nand"
    go Nor  = \(e1 :* e2 :* End) -> error_TODO "Nor"

    go Pi = \End -> bot -- because @dirac pi@ has no density wrt lebesgue

    go Sin = \(e1 :* End) -> do
        x0 <- emitLet' v0
        n  <- var <$> emitMBind P.counting
        let tau_n = P.real_ 2 P.* P.fromInt n P.* P.pi -- TODO: emitLet?
        emitGuard (P.negate P.one P.< x0 P.&& x0 P.< P.one)
        v  <- var <$> emitSuperpose
            [ P.dirac (tau_n P.+ P.asin x0)
            , P.dirac (tau_n P.+ P.pi P.- P.asin x0)
            ]
        emitWeight
            . P.recip
            . P.sqrt
            . P.unsafeProb
            $ (P.one P.- x0 P.^ P.nat_ 2)
        constrainValue v e1

    go Cos = \(e1 :* End) -> do
        x0 <- emitLet' v0
        n  <- var <$> emitMBind P.counting
        let tau_n = P.real_ 2 P.* P.fromInt n P.* P.pi
        emitGuard (P.negate P.one P.< x0 P.&& x0 P.< P.one)
        r  <- emitLet' (tau_n P.+ P.acos x0)
        v  <- var <$> emitSuperpose [P.dirac r, P.dirac (r P.+ P.pi)]
        emitWeight
            . P.recip
            . P.sqrt
            . P.unsafeProb
            $ (P.one P.- x0 P.^ P.nat_ 2)
        constrainValue v e1

    go Tan = \(e1 :* End) -> do
        x0 <- emitLet' v0
        n  <- var <$> emitMBind P.counting
        r  <- emitLet' (P.fromInt n P.* P.pi P.+ P.atan x0)
        emitWeight $ P.recip (P.one P.+ P.square x0)
        constrainValue r e1

    go Asin = \(e1 :* End) -> do
        x0 <- emitLet' v0
        emitWeight $ P.unsafeProb (P.cos x0)
        -- TODO: bounds check for -pi/2 <= v0 < pi/2
        constrainValue (P.sin x0) e1

    go Acos = \(e1 :* End) -> do
        x0 <- emitLet' v0
        emitWeight $ P.unsafeProb (P.sin x0)
        constrainValue (P.cos x0) e1

    go Atan = \(e1 :* End) -> do
        x0 <- emitLet' v0
        emitWeight $ P.recip (P.unsafeProb (P.cos x0 P.^ P.nat_ 2))
        constrainValue (P.tan x0) e1

    go Sinh      = \(e1 :* End)       -> error_TODO "Sinh"
    go Cosh      = \(e1 :* End)       -> error_TODO "Cosh"
    go Tanh      = \(e1 :* End)       -> error_TODO "Tanh"
    go Asinh     = \(e1 :* End)       -> error_TODO "Asinh"
    go Acosh     = \(e1 :* End)       -> error_TODO "Acosh"
    go Atanh     = \(e1 :* End)       -> error_TODO "Atanh"
    go Choose    = \(e1 :* e2 :* End) -> error_TODO "Choose"
    go Floor     = \(e1 :* End)       -> error_TODO "Floor"
    go RealPow   = \(e1 :* e2 :* End) ->
        -- TODO: There's a discrepancy between @(**)@ and @pow_@ in
        -- the old code...
        do
            -- TODO: if @v1@ is 0 or 1 then bot. Maybe the @log v1@ in
            -- @w@ takes care of the 0 case?
            u <- emitLet' v0
            -- either this from @(**)@:
            --   emitGuard  $ P.zero P.< u
            --   w <- atomize $ P.recip (P.abs (v0 P.* P.log v1))
            --   emitWeight $ P.unsafeProb (fromWhnf w)
            --   constrainValue (P.logBase v1 v0) e2
            -- or this from @pow_@:
            let w = P.recip (u P.* P.unsafeProb (P.abs (P.log e1)))
            emitWeight w
            constrainValue (P.log u P./ P.log e1) e2
            -- end.
        <|> do
            -- TODO: if @v2@ is 0 then bot. Maybe the weight @w@ takes
            -- care of this case?
            u <- emitLet' v0
            let ex = v0 P.** P.recip e2
            -- either this from @(**)@:
            --   emitGuard $ P.zero P.< u
            --   w <- atomize $ abs (ex / (v2 * v0))
            -- or this from @pow_@:
            let w = P.abs (P.fromProb ex P./ (e2 P.* P.fromProb u))
            -- end.
            emitWeight $ P.unsafeProb w
            constrainValue ex e1
    go Exp = \(e1 :* End) -> do
        x0 <- emitLet' v0
        -- TODO: do we still want\/need the @emitGuard (0 < x0)@ which
        -- is now equivalent to @emitGuard (0 /= x0)@ thanks to the
        -- types?
        emitWeight (P.recip x0)
        constrainValue (P.log x0) e1

    go Log = \(e1 :* End) -> do
        exp_x0 <- emitLet' (P.exp v0)
        emitWeight exp_x0
        constrainValue exp_x0 e1

    go (Infinity _)     = \End               -> error_TODO "Infinity" -- scalar0
    go GammaFunc        = \(e1 :* End)       -> error_TODO "GammaFunc" -- scalar1
    go BetaFunc         = \(e1 :* e2 :* End) -> error_TODO "BetaFunc" -- scalar2
    go (Equal  theOrd)  = \(e1 :* e2 :* End) -> error_TODO "Equal"
    go (Less   theOrd)  = \(e1 :* e2 :* End) -> error_TODO "Less"
    go (NatPow theSemi) = \(e1 :* e2 :* End) -> error_TODO "NatPow"
    go (Negate theRing) = \(e1 :* End) ->
        -- TODO: figure out how to merge this implementation of @rr1
        -- negate@ with the one in 'evaluatePrimOp' to DRY
        -- TODO: just
        -- emitLet the @v0@ and pass the neutral term to the recursive
        -- call?
        let negate_v0 = syn (PrimOp_ (Negate theRing) :$ v0 :* End)
                -- case v0 of
                -- Neutral e ->
                --     Neutral $ syn (PrimOp_ (Negate theRing) :$ e :* End)
                -- Head_ v ->
                --     case theRing of
                --     HRing_Int  -> Head_ . reflect . negate $ reify v
                --     HRing_Real -> Head_ . reflect . negate $ reify v
        in constrainValue negate_v0 e1

    go (Abs theRing) = \(e1 :* End) -> do
        let theSemi = hSemiring_HRing theRing
            theOrd  =
                case theRing of
                HRing_Int  -> HOrd_Int
                HRing_Real -> HOrd_Real
            theEq   = hEq_HOrd theOrd
            signed  = C.singletonCoercion (C.Signed theRing)
            zero    = P.zero_ theSemi
            lt      = P.primOp2_ $ Less   theOrd
            eq      = P.primOp2_ $ Equal  theEq
            neg     = P.primOp1_ $ Negate theRing

        x0 <- emitLet' (P.coerceTo_ signed v0)
        v  <- var <$> emitMBind
            (P.if_ (lt zero x0)
                (P.dirac x0 P.<|> P.dirac (neg x0))
                (P.if_ (eq zero x0)
                    (P.dirac zero)
                    (P.reject . SMeasure $ typeOf zero)))
        constrainValue v e1

    go (Signum theRing) = \(e1 :* End) ->
        case theRing of
        HRing_Real -> bot
        HRing_Int  -> do
            x <- var <$> emitMBind P.counting
            emitGuard $ P.signum x P.== v0
            constrainValue x e1

    go (Recip theFractional) = \(e1 :* End) -> do
        x0 <- emitLet' v0
        emitWeight
            . P.recip
            . P.unsafeProbFraction_ theFractional
            -- TODO: define a dictionary-passing variant of 'P.square'
            -- instead, to include the coercion in there explicitly...
            $ square (hSemiring_HFractional theFractional) x0
        constrainValue (P.primOp1_ (Recip theFractional) x0) e1

    go (NatRoot theRadical) = \(e1 :* e2 :* End) ->
        case theRadical of
        HRadical_Prob -> do
            x0 <- emitLet' v0
            u2 <- fromWhnf <$> atomize e2
            emitWeight (P.nat2prob u2 P.* x0)
            constrainValue (x0 P.^ u2) e1

    go (Erf theContinuous) = \(e1 :* End) ->
        error "TODO: constrainPrimOp: need InvErf to disintegrate Erf"


-- HACK: can't use @(P.^)@ because Haskell can't figure out our polymorphism
square :: (ABT Term abt) => HSemiring a -> abt '[] a -> abt '[] a
square theSemiring e =
    syn (PrimOp_ (NatPow theSemiring) :$ e :* P.nat_ 2 :* End)


----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: do we really want the first argument to be a term at all,
-- or do we want something more general like patters for capturing
-- measurable events?
--
-- | This is a helper function for 'constrainValue' to handle 'SBind'
-- statements (just as the 'perform' argument to 'evaluate' is a
-- helper for handling 'SBind' statements).
--
-- N.B., We assume that the first argument, @v0@, is already
-- atomized. So, this must be ensured before recursing, but we can
-- assume it's already been done by the IH. Technically, we con't
-- care whether the first argument is in normal form or not, just
-- so long as it doesn't contain any heap-bound variables.
--
-- This is the function called @(<<|)@ in the paper, though notably
-- we swap the argument order.
--
-- TODO: find some way to capture in the type that the first argument
-- must be emissible, to help avoid accidentally passing the arguments
-- in the wrong order!
--
-- TODO: under what circumstances is @constrainOutcome x m@ different
-- from @constrainValue x =<< perform m@? If they're always the
-- same, then we should just use that as the definition in order
-- to avoid repeating ourselves
constrainOutcome
    :: forall abt a
    .  (ABT Term abt)
    => abt '[] a
    -> abt '[] ('HMeasure a)
    -> Dis abt ()
constrainOutcome v0 e0 =
#ifdef __TRACE_DISINTEGRATE__
    getExtras >>= \extras ->
    getIndices >>= \inds ->
    trace (
        let s = "-- constrainOutcome"
        in "\n" ++ s ++ ": "
            ++ show (pretty v0)
            ++ "\n" ++ replicate (length s) ' ' ++ ": "
            ++ show (pretty e0) ++ "\n"
            ++ "at " ++  show (ppInds inds) ++ "\n"
            ++ show (prettyExtras extras)
          ) $
#endif
    do  w0 <- evaluate_ e0
        case w0 of
            Neutral _ -> bot
            Head_   v -> go v
    where
    impossible = error "constrainOutcome: the impossible happened"

    go :: Head abt ('HMeasure a) -> Dis abt ()
    go (WLiteral _)          = impossible
    -- go (WDatum _)         = impossible
    -- go (WEmpty _)         = impossible
    -- go (WArray _ _)       = impossible
    -- go (WLam _)           = impossible
    -- go (WIntegrate _ _ _) = impossible
    -- go (WSummate   _ _ _) = impossible
    go (WCoerceTo   _ _)     = impossible
    go (WUnsafeFrom _ _)     = impossible
    go (WMeasureOp o es)     = constrainOutcomeMeasureOp v0 o es
    go (WDirac e1)           = constrainValue v0 e1
    go (WMBind e1 e2)        =
        caseBind e2 $ \x e2' -> do
            i <- getIndices
            push (SBind x (Thunk e1) i) e2' >>= constrainOutcome v0
    go (WPlate e1 e2)        = do
        x' <- pushPlate e1 e2
        constrainValue v0 x'

    go (WChain e1 e2 e3)     = error "TODO: constrainOutcome{Chain}"
    go (WReject typ)         = emit_ $ \m -> P.reject (typeOf m)
    go (WSuperpose pes) = do
        i <- getIndices
        if not (null i) && L.length pes > 1 then bot else
          emitFork_ (P.superpose . fmap ((,) P.one))
                    (fmap (\(p,e) -> push (SWeight (Thunk p) i) e >>= constrainOutcome v0)
                          pes)

-- TODO: should this really be different from 'constrainValueMeasureOp'?
--
-- TODO: find some way to capture in the type that the first argument
-- must be emissible.
constrainOutcomeMeasureOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => abt '[] a
    -> MeasureOp typs a
    -> SArgs abt args
    -> Dis abt ()
constrainOutcomeMeasureOp v0 = go
    where
    go Lebesgue = \(lo :* hi :* End) -> do
        -- TODO: optimize the cases where lo is -∞ or hi is ∞
        v0' <- emitLet' v0
        pushGuard (lo P.<= v0' P.&& v0' P.<= hi)

    -- TODO: I think, based on Hakaru v0.2.0
    go Counting = \End -> return ()

    go Categorical = \(e1 :* End) -> do
        -- TODO: check that v0' is < then length of e1
        pushWeight (P.densityCategorical e1 v0)

    -- Per the paper
    go Uniform = \(lo :* hi :* End) -> do
        v0' <- emitLet' v0
        pushGuard (lo P.<= v0' P.&& v0' P.<= hi)
        pushWeight (P.densityUniform lo hi v0')

    -- TODO: Add fallback handling of Normal that does not atomize mu,sd.
    -- This fallback is as if Normal were defined in terms of Lebesgue
    -- and a density Weight.  This fallback is present in Hakaru v0.2.0
    -- in order to disintegrate a program such as
    --  x <~ normal(0,1)
    --  y <~ normal(x,1)
    --  return ((x+(y+y),x)::pair(real,real))
    go Normal = \(mu :* sd :* End) -> do
        -- N.B., if\/when extending this to higher dimensions, the
        -- real equation is
        -- @recip (sqrt (2*pi*sd^2) ^ n) *
        --  exp (negate (norm_n (v0 - mu) ^ 2) /
        --  (2*sd^2))@
        -- for @Real^n@.
        pushWeight (P.densityNormal mu sd v0)

    go Poisson = \(e1 :* End) -> do
        v0' <- emitLet' v0
        pushGuard (P.nat_ 0 P.<= v0' P.&& P.prob_ 0 P.< e1)
        pushWeight (P.densityPoisson e1 v0')

    go Gamma = \(e1 :* e2 :* End) -> do
        v0' <- emitLet' v0
        pushGuard (P.prob_ 0 P.< v0' P.&&
                   P.prob_ 0 P.< e1  P.&&
                   P.prob_ 0 P.< e2)
        pushWeight (P.densityGamma e1 e2 v0')
    go Beta = \(e1 :* e2 :* End) -> do
        v0' <- emitLet' v0
        pushGuard (P.prob_ 0 P.<= v0' P.&&
                   P.prob_ 1 P.>= v0' P.&&
                   P.prob_ 0 P.< e1   P.&&
                   P.prob_ 0 P.< e2)
        pushWeight (P.densityBeta e1 e2 v0')

----------------------------------------------------------------
----------------------------------------------------------- fin.
