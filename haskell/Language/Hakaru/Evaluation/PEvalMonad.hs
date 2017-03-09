{-# LANGUAGE CPP
           , GADTs
           , KindSignatures
           , DataKinds
           , TypeOperators
           , Rank2Types
           , BangPatterns
           , FlexibleContexts
           , MultiParamTypeClasses
           , FunctionalDependencies
           , FlexibleInstances
           , UndecidableInstances
           , EmptyCase
           , ScopedTypeVariables
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.05.24
-- |
-- Module      :  Language.Hakaru.Evaluation.PEvalMonad
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- A unified 'EvaluationMonad' for pure evaluation, expect, and
-- disintegrate.
----------------------------------------------------------------
module Language.Hakaru.Evaluation.PEvalMonad
    (
    -- * The unified 'PEval' monad
    -- ** List-based version
      ListContext(..), PAns, PEval(..)
    , runPureEval, runImpureEval, runExpectEval
    -- ** TODO: IntMap-based version
    
    -- * Operators on the disintegration monad
    -- ** The \"zero\" and \"one\"
    , bot
    --, reject
    -- ** Emitting code
    , emit
    , emitMBind
    , emitLet
    , emitLet'
    , emitUnpair
    -- TODO: emitUneither
    -- emitCaseWith
    , emit_
    , emitMBind_
    , emitGuard
    , emitWeight
    , emitFork_
    , emitSuperpose
    , choose
    ) where

import           Prelude              hiding (id, (.))
import           Control.Category     (Category(..))
#if __GLASGOW_HASKELL__ < 710
import           Data.Monoid          (Monoid(..))
import           Data.Functor         ((<$>))
import           Control.Applicative  (Applicative(..))
#endif
import qualified Data.Foldable        as F
import qualified Data.Traversable     as T
import qualified Data.List.NonEmpty   as NE
import           Control.Applicative  (Alternative(..))
import           Control.Monad        (MonadPlus(..))
import           Data.Text            (Text)
import qualified Data.Text            as Text

import Language.Hakaru.Syntax.IClasses
import Data.Number.Nat
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing    (Sing, sUnMeasure, sUnPair)
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.TypeOf
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.DatumABT
import qualified Language.Hakaru.Syntax.Prelude as P
import Language.Hakaru.Evaluation.Types
import Language.Hakaru.Evaluation.Lazy (reifyPair)

#ifdef __TRACE_DISINTEGRATE__
import Debug.Trace (trace)
#endif

----------------------------------------------------------------
----------------------------------------------------------------
-- | An ordered collection of statements representing the context
-- surrounding the current focus of our program transformation.
-- That is, since some transformations work from the bottom up, we
-- need to keep track of the statements we passed along the way
-- when reaching for the bottom.
--
-- The tail of the list takes scope over the head of the list. Thus,
-- the back\/end of the list is towards the top of the program,
-- whereas the front of the list is towards the bottom.
--
-- This type was formerly called @Heap@ (presumably due to the
-- 'Statement' type being called @Binding@) but that seems like a
-- misnomer to me since this really has nothing to do with allocation.
-- However, it is still like a heap inasmuch as it's a dependency
-- graph and we may wish to change the topological sorting or remove
-- \"garbage\" (subject to correctness criteria).
--
-- TODO: Figure out what to do with 'SWeight', 'SGuard', 'SStuff',
-- etc, so that we can use an @IntMap (Statement abt)@ in order to
-- speed up the lookup times in 'select'. (Assuming callers don't
-- use 'unsafePush' unsafely: we can recover the order things were
-- inserted from their 'varID' since we've freshened them all and
-- therefore their IDs are monotonic in the insertion order.)
data ListContext (abt :: [Hakaru] -> Hakaru -> *) (p :: Purity) =
    ListContext
    { nextFreshNat :: {-# UNPACK #-} !Nat
    , statements   :: [Statement abt p]
    }


-- HACK: we can't use a type family and do @abt xs (P p a)@ because
-- of non-injectivity. So we make this a GADT instead. Because it's
-- a GADT, there's a bunch of ugly rewrapping required; but everything
-- seems to work out just fine...
data P :: Purity -> ([Hakaru] -> Hakaru -> *) -> [Hakaru] -> Hakaru -> *
    where
    PPure   :: !(abt xs a)             -> P 'Pure    abt xs a
    PImpure :: !(abt xs ('HMeasure a)) -> P 'Impure  abt xs a
    PExpect :: !(abt xs 'HProb)        -> P 'ExpectP abt xs a

unPPure :: P 'Pure abt xs a -> abt xs a
unPPure (PPure e) = e

unPImpure :: P 'Impure abt xs a -> abt xs ('HMeasure a)
unPImpure (PImpure e) = e

unPExpect :: P 'ExpectP abt xs a -> abt xs 'HProb
unPExpect (PExpect e) = e

mapPPure :: (abt xs a -> abt ys b) -> P 'Pure abt xs a -> P 'Pure abt ys b
mapPPure f (PPure e) = PPure (f e)

mapPImpure
    :: (abt xs ('HMeasure a) -> abt ys ('HMeasure b))
    -> P 'Impure abt xs a
    -> P 'Impure abt ys b
mapPImpure f (PImpure e) = PImpure (f e)

mapPExpect
    :: (abt xs 'HProb -> abt ys 'HProb)
    -> P 'ExpectP abt xs a
    -> P 'ExpectP abt ys b
mapPExpect f (PExpect e) = PExpect (f e)

mapP
    :: (forall a. abt xs a -> abt ys a)
    -> P p abt xs b
    -> P p abt ys b
mapP f (PPure   e) = PPure   $ f e
mapP f (PImpure e) = PImpure $ f e
mapP f (PExpect e) = PExpect $ f e

-- | Plug a term into a context. That is, the 'statements' of the
-- context specifies a program with a hole in it; so we plug the
-- given term into that hole, returning the complete program.
residualizeListContext
    :: forall abt p a
    .  (ABT Term abt)
    => ListContext abt p
    -> P p abt '[] a
    -> P p abt '[] a
residualizeListContext =
    -- N.B., we use a left fold because the head of the list of
    -- statements is the one closest to the hole.
    \ss e0 -> foldl (flip step) e0 (statements ss)
    where
    step
        :: Statement abt p
        -> P p abt '[] a
        -> P p abt '[] a
    step (SLet  (Location x) body _)  = mapP $ residualizeLet x body
    step (SBind (Location x) body _) = mapPImpure $ \e ->
        -- TODO: if @body@ is dirac, then treat as 'SLet'
        syn (MBind :$ fromLazy body :* bind x e :* End)
    step (SGuard xs pat scrutinee _) = mapPImpure $ \e ->
        -- TODO: avoid adding the 'PWild' branch if we know @pat@ covers the type
        syn $ Case_ (fromLazy scrutinee)
            [ Branch pat   $ binds_ (fromLocations1 xs) e
            , Branch PWild $ P.reject (typeOf e)
            ]
    step (SWeight body _) = mapPImpure $ P.withWeight (fromLazy body)
    step (SStuff0    f _) = mapPExpect f
    step (SStuff1 _x f _) = mapPExpect f


-- TODO: move this to Prelude? Is there anyone else that actually needs these smarts?
residualizeLet
    :: (ABT Term abt) => Variable a -> Lazy abt a -> abt '[] b -> abt '[] b
residualizeLet x body scope
    -- Drop unused bindings
    | not (x `memberVarSet` freeVars scope) = scope
    -- TODO: if used exactly once in @e@, then inline.
    | otherwise =
        case getLazyVariable body of
        Just y  -> subst x (var y) scope
        Nothing ->
            case getLazyLiteral body of
            Just v  -> subst x (syn $ Literal_ v) scope
            Nothing ->
                syn (Let_ :$ fromLazy body :* bind x scope :* End)

----------------------------------------------------------------
type PAns p abt m a = ListContext abt p -> m (P p abt '[] a)


----------------------------------------------------------------
-- TODO: defunctionalize the continuation. In particular, the only
-- heap modifications we need are 'push' and a variant of 'update'
-- for finding\/replacing a binding once we have the value in hand;
-- and the only 'freshNat' modifications are to allocate new 'Nat'.
-- We could defunctionalize the second arrow too by relying on the
-- @Codensity (ReaderT e m) ~= StateT e (Codensity m)@ isomorphism,
-- which makes explicit that the only thing other than 'ListContext'
-- updates is emitting something like @[Statement]@ to serve as the
-- beginning of the final result.
--
-- | TODO: give this a better, more informative name!
newtype PEval abt p m x =
    PEval { unPEval :: forall a. (x -> PAns p abt m a) -> PAns p abt m a }
    -- == Codensity (PAns p abt m)


-- | Run an 'Impure' computation in the 'PEval' monad, residualizing
-- out all the statements in the final evaluation context. The
-- second argument should include all the terms altered by the
-- 'PEval' expression; this is necessary to ensure proper hygiene;
-- for example(s):
--
-- > runPEval (perform e) [Some2 e]
-- > runPEval (constrainOutcome e v) [Some2 e, Some2 v]
--
-- We use 'Some2' on the inputs because it doesn't matter what their
-- type or locally-bound variables are, so we want to allow @f@ to
-- contain terms with different indices.
runImpureEval
    :: (ABT Term abt, Applicative m, F.Foldable f)
    => PEval abt 'Impure m (abt '[] a)
    -> f (Some2 abt)
    -> m (abt '[] ('HMeasure a))
runImpureEval m es =
    unPImpure <$> unPEval m c0 h0
    where
    i0      = maxNextFree es -- TODO: is maxNextFreeOrBind better here?
    h0      = ListContext i0 []
    -- TODO: we only use dirac because 'residualizeListContext'
    -- requires it to already be a measure; unfortunately this can
    -- result in an extraneous @(>>= \x -> dirac x)@ redex at the
    -- end of the program. In principle, we should be able to
    -- eliminate that redex by changing the type of
    -- 'residualizeListContext'...
    c0 e ss =
        pure
        . residualizeListContext ss
        . PImpure
        $ syn(Dirac :$ e :* End)

runPureEval
    :: (ABT Term abt, Applicative m, F.Foldable f)
    => PEval abt 'Pure m (abt '[] a)
    -> f (Some2 abt)
    -> m (abt '[] a)
runPureEval m es =
    unPPure <$> unPEval m c0 h0
    where
    i0      = maxNextFree es -- TODO: is maxNextFreeOrBind better here?
    h0      = ListContext i0 []
    c0 e ss = pure . residualizeListContext ss $ PPure e

runExpectEval
    :: (ABT Term abt, Applicative m, F.Foldable f)
    => PEval abt 'ExpectP m (abt '[] a)
    -> abt '[a] 'HProb
    -> f (Some2 abt)
    -> m (abt '[] 'HProb)
runExpectEval m f es =
    unPExpect <$> unPEval m c0 h0
    where
    i0      = nextFreeOrBind f `max` maxNextFreeOrBind es
    h0      = ListContext i0 []
    c0 e ss =
        pure
        . residualizeListContext ss
        . PExpect
        $ caseVarSyn e
            (\x -> caseBind f $ \y f' -> subst y (var x) f')
            (\_ -> syn (Let_ :$ e :* f :* End))
        -- TODO: make this smarter still, to drop the let-binding entirely if it's not used in @f@.


instance Functor (PEval abt p m) where
    fmap f m = PEval $ \c -> unPEval m (c . f)

instance Applicative (PEval abt p m) where
    pure x    = PEval $ \c -> c x
    mf <*> mx = PEval $ \c -> unPEval mf $ \f -> unPEval mx $ \x -> c (f x)

instance Monad (PEval abt p m) where
    return   = pure
    mx >>= k = PEval $ \c -> unPEval mx $ \x -> unPEval (k x) c

instance Alternative m => Alternative (PEval abt p m) where
    empty   = PEval $ \_ _ -> empty
    m <|> n = PEval $ \c h -> unPEval m c h <|> unPEval n c h

instance Alternative m => MonadPlus (PEval abt p m) where
    mzero = empty -- aka "bot"
    mplus = (<|>) -- aka "lub"

instance (ABT Term abt) => EvaluationMonad abt (PEval abt p m) p where
    freshNat =
        PEval $ \c (ListContext i ss) ->
            c i (ListContext (i+1) ss)

    unsafePush s =
        PEval $ \c (ListContext i ss) ->
            c () (ListContext i (s:ss))

    -- N.B., the use of 'reverse' is necessary so that the order
    -- of pushing matches that of 'pushes'
    unsafePushes ss =
        PEval $ \c (ListContext i ss') ->
            c () (ListContext i (reverse ss ++ ss'))

    select x p = loop []
        where
        -- TODO: use a DList to avoid reversing inside 'unsafePushes'
        loop ss = do
            ms <- unsafePop
            case ms of
                Nothing -> do
                    unsafePushes ss
                    return Nothing
                Just s  ->
                    -- Alas, @p@ will have to recheck 'isBoundBy'
                    -- in order to grab the 'Refl' proof we erased;
                    -- but there's nothing to be done for it.
                    case x `isBoundBy` s >> p s of
                    Nothing -> loop (s:ss) -- BUG: we only want to loop if @x@ isn't bound by @s@; if it is bound but @p@ fails (e.g., because @s@ is 'Stuff1'), then we should fail/stop (thus the return type should be @2+r@ to distinguish no-match = free vs failed-match = bound-but-inalterable)
                    Just mr -> do
                        r <- mr
                        unsafePushes ss
                        return (Just r)

-- | Not exported because we only need it for defining 'select' on 'PEval'.
unsafePop :: PEval abt p m (Maybe (Statement abt p))
unsafePop =
    PEval $ \c h@(ListContext i ss) ->
        case ss of
        []    -> c Nothing  h
        s:ss' -> c (Just s) (ListContext i ss')

----------------------------------------------------------------
----------------------------------------------------------------

-- | It is impossible to satisfy the constraints, or at least we
-- give up on trying to do so. This function is identical to 'empty'
-- and 'mzero' for 'PEval'; we just give it its own name since this is
-- the name used in our papers.
--
-- TODO: add some sort of trace information so we can get a better
-- idea what caused a disintegration to fail.
bot :: (ABT Term abt, Alternative m) => PEval abt p m a
bot = empty


{-
-- BUG: no longer typechecks after splitting 'Reject_' out from 'Superpose_'
-- | The empty measure is a solution to the constraints.
reject :: (ABT Term abt) => PEval abt p m a
reject = PEval $ \_ _ -> return . P.reject $ SMeasure sing
-}


-- Something essentially like this function was called @insert_@
-- in the finally-tagless code.
--
-- | Emit some code that binds a variable, and return the variable
-- thus bound. The function says what to wrap the result of the
-- continuation with; i.e., what we're actually emitting.
emit
    :: (ABT Term abt, Functor m)
    => Text
    -> Sing a
    -> (forall r. P p abt '[a] r -> P p abt '[] r)
    -> PEval abt p m (Variable a)
emit hint typ f = do
    x <- freshVar hint typ
    PEval $ \c h -> (f . mapP (bind x)) <$> c x h


-- This function was called @lift@ in the finally-tagless code.
-- | Emit an 'MBind' (i.e., \"@m >>= \x ->@\") and return the
-- variable thus bound (i.e., @x@).
emitMBind
    :: (ABT Term abt, Functor m)
    => abt '[] ('HMeasure a)
    -> PEval abt 'Impure m (Variable a)
emitMBind m =
    emit Text.empty (sUnMeasure $ typeOf m) $ \(PImpure e) ->
        PImpure $ syn (MBind :$ m :* e :* End)


-- | A smart constructor for emitting let-bindings. If the input
-- is already a variable then we just return it; otherwise we emit
-- the let-binding. N.B., this function provides the invariant that
-- the result is in fact a variable; whereas 'emitLet'' does not.
emitLet
    :: (ABT Term abt, Functor m) => abt '[] a -> PEval abt p m (Variable a)
emitLet e =
    caseVarSyn e return $ \_ ->
        -- N.B., must use the second @($)@ here because rank-2 polymorphism
        emit Text.empty (typeOf e) $ mapP $ \m ->
            syn (Let_ :$ e :* m :* End)

-- | A smart constructor for emitting let-bindings. If the input
-- is already a variable or a literal constant, then we just return
-- it; otherwise we emit the let-binding. N.B., this function
-- provides weaker guarantees on the type of the result; if you
-- require the result to always be a variable, then see 'emitLet'
-- instead.
emitLet'
    :: (ABT Term abt, Functor m) => abt '[] a -> PEval abt p m (abt '[] a)
emitLet' e =
    caseVarSyn e (const $ return e) $ \t ->
        case t of
        Literal_ _ -> return e
        _ -> do
            -- N.B., must use the second @($)@ here because rank-2 polymorphism
            x <- emit Text.empty (typeOf e) $ mapP $ \m ->
                syn (Let_ :$ e :* m :* End)
            return (var x)

-- | A smart constructor for emitting \"unpair\". If the input
-- argument is actually a constructor then we project out the two
-- components; otherwise we emit the case-binding and return the
-- two variables.
emitUnpair
    :: (ABT Term abt, Applicative m)
    => Whnf abt (HPair a b)
    -> PEval abt p m (abt '[] a, abt '[] b)
emitUnpair (Head_   w) = return $ reifyPair w
emitUnpair (Neutral e) = do
    let (a,b) = sUnPair (typeOf e)
    x <- freshVar Text.empty a
    y <- freshVar Text.empty b
    emitUnpair_ x y e

emitUnpair_
    :: forall abt p m a b
    .  (ABT Term abt, Applicative m)
    => Variable a
    -> Variable b
    -> abt '[] (HPair a b)
    -> PEval abt p m (abt '[] a, abt '[] b)
emitUnpair_ x y = loop
    where
    done :: abt '[] (HPair a b) -> PEval abt p m (abt '[] a, abt '[] b)
    done e =
#ifdef __TRACE_DISINTEGRATE__
        trace "-- emitUnpair: done (term is not Datum_ nor Case_)" $
#endif
        PEval $ \c h ->
            mapP ( syn
            . Case_ e
            . (:[])
            . Branch (pPair PVar PVar)
            . bind x
            . bind y
            ) <$> c (var x, var y) h

    loop :: abt '[] (HPair a b) -> PEval abt p m (abt '[] a, abt '[] b)
    loop e0 =
        caseVarSyn e0 (done . var) $ \t ->
            case t of
            Datum_ d   -> do
#ifdef __TRACE_DISINTEGRATE__
                trace "-- emitUnpair: found Datum_" $ return ()
#endif
                return $ reifyPair (WDatum d)
            Case_ e bs -> do
#ifdef __TRACE_DISINTEGRATE__
                trace "-- emitUnpair: going under Case_" $ return ()
#endif
                -- TODO: we want this to duplicate the current
                -- continuation for (the evaluation of @loop@ in)
                -- all branches. So far our traces all end up
                -- returning @bot@ on the first branch, and hence
                -- @bot@ for the whole case-expression, so we can't
                -- quite tell whether it does what is intended.
                --
                -- N.B., the only 'PEval'-effects in 'applyBranch'
                -- are to freshen variables; thus this use of
                -- 'traverse' is perfectly sound.
                emitCaseWith loop e bs
            _ -> done e0


-- TODO: emitUneither


-- This function was called @insert_@ in the old finally-tagless code.
-- | Emit some code that doesn't bind any variables. This function
-- provides an optimisation over using 'emit' and then discarding
-- the generated variable.
emit_
    :: (ABT Term abt, Functor m)
    => (forall r. P p abt '[] r -> P p abt '[] r)
    -> PEval abt p m ()
emit_ f = PEval $ \c h -> f <$> c () h


-- | Emit an 'MBind' that discards its result (i.e., \"@m >>@\").
-- We restrict the type of the argument to be 'HUnit' so as to avoid
-- accidentally dropping things.
emitMBind_
    :: (ABT Term abt, Functor m)
    => abt '[] ('HMeasure HUnit)
    -> PEval abt 'Impure m ()
emitMBind_ m = emit_ $ mapPImpure (m P.>>)


-- TODO: if the argument is a value, then we can evaluate the 'P.if_' immediately rather than emitting it.
-- | Emit an assertion that the condition is true.
emitGuard
    :: (ABT Term abt, Functor m)
    => abt '[] HBool
    -> PEval abt 'Impure m ()
emitGuard b = emit_ $ mapPImpure (P.withGuard b)
    -- == emit_ $ \m -> P.if_ b m P.reject

-- TODO: if the argument is the literal 1, then we can avoid emitting anything.
emitWeight
    :: (ABT Term abt, Functor m)
    => abt '[] 'HProb
    -> PEval abt 'Impure m ()
emitWeight w = emit_ $ mapPImpure (P.withWeight w)


-- N.B., this use of 'T.traverse' is definitely correct. It's
-- sequentializing @t [abt '[] ('HMeasure a)]@ into @[t (abt '[]
-- ('HMeasure a))]@ by chosing one of the possibilities at each
-- position in @t@. No heap\/context effects can escape to mess
-- things up. In contrast, using 'T.traverse' to sequentialize @t
-- (PEval abt a)@ as @PEval abt (t a)@ is /wrong/! Doing that would give
-- the conjunctive semantics where we have effects from one position
-- in @t@ escape to affect the other positions. This has to do with
-- the general issue in partial evaluation where we need to duplicate
-- downstream work (as we do by passing the same heap to everyone)
-- because there's no general way to combing the resulting heaps
-- for each branch.
--
-- | Run each of the elements of the traversable using the same
-- heap and continuation for each one, then pass the results to a
-- function for emitting code.
emitFork_
    :: (ABT Term abt, Applicative m, T.Traversable t)
    => (forall r. t (P p abt '[] r) -> P p abt '[] r)
    -> t (PEval abt p m a)
    -> PEval abt p m a
emitFork_ f ms =
    PEval $ \c h -> f <$> T.traverse (\m -> unPEval m c h) ms


-- | Emit a 'Superpose_' of the alternatives, each with unit weight.
emitSuperpose
    :: (ABT Term abt, Functor m)
    => [abt '[] ('HMeasure a)]
    -> PEval abt 'Impure m (Variable a)
emitSuperpose []  = error "BUG: emitSuperpose: can't use Prelude.superpose because it'll throw an error"
emitSuperpose [e] = emitMBind e
emitSuperpose es  =
    emitMBind . P.superpose . fmap ((,) P.one) $ NE.fromList es


-- | Emit a 'Superpose_' of the alternatives, each with unit weight.
choose
    :: (ABT Term abt, Applicative m)
    => [PEval abt 'Impure m a]
    -> PEval abt 'Impure m a
choose []  = error "BUG: choose: can't use Prelude.superpose because it'll throw an error"
choose [m] = m
choose ms  =
    emitFork_
        (PImpure . P.superpose . fmap ((,) P.one . unPImpure) . NE.fromList)
        ms


-- | Given some function we can call on the bodies of the branches,
-- freshen all the pattern-bound variables and then run the function
-- on all the branches in parallel (i.e., with the same continuation
-- and heap) and then emit a case-analysis expression with the
-- results of the continuations as the bodies of the branches. This
-- function is useful for when we really do want to emit a 'Case_'
-- expression, rather than doing the superpose of guard patterns
-- thing that 'constrainValue' does.
--
-- N.B., this function assumes (and does not verify) that the second
-- argument is emissible. So callers must guarantee this invariant,
-- by calling 'atomize' as necessary.
--
-- TODO: capture the emissibility requirement on the second argument
-- in the types.
emitCaseWith
    :: (ABT Term abt, Applicative m)
    => (abt '[] b -> PEval abt p m r)
    -> abt '[] a
    -> [Branch a abt b]
    -> PEval abt p m r
emitCaseWith f e bs = do
    error "TODO: emitCaseWith"
{-
-- BUG: this doesn't typecheck with keeping @p@ polymorphic...
    gms <- T.for bs $ \(Branch pat body) ->
        let (vars, body') = caseBinds body
        in  (\vars' ->
                let rho = toAssocs vars (fmap11 var vars')
                in  GBranch pat vars' (f $ substs rho body')
            ) <$> freshenVars vars
    PEval $ \c h ->
        (syn . Case_ e) <$> T.for gms (\gm ->
            fromGBranch <$> T.for gm (\m ->
                unPEval m c h))
{-# INLINE emitCaseWith #-}
-}


-- HACK: to get the one case we really need to work at least.
emitCaseWith_Impure
    :: (ABT Term abt, Applicative m)
    => (abt '[] b -> PEval abt 'Impure m r)
    -> abt '[] a
    -> [Branch a abt b]
    -> PEval abt 'Impure m r
emitCaseWith_Impure f e bs = do
    gms <- T.for bs $ \(Branch pat body) ->
        let (vars, body') = caseBinds body
        in  (\vars' ->
                let rho = toAssocs1 vars (fmap11 var vars')
                in  GBranch pat vars' (f $ substs rho body')
            ) <$> freshenVars vars
    PEval $ \c h ->
        (PImpure . syn . Case_ e) <$> T.for gms (\gm ->
            fromGBranch <$> T.for gm (\m ->
                unPImpure <$> unPEval m c h))
{-# INLINE emitCaseWith_Impure #-}


----------------------------------------------------------------
----------------------------------------------------------- fin.
