{-# LANGUAGE CPP
           , GADTs
           , KindSignatures
           , DataKinds
           , Rank2Types
           , ScopedTypeVariables
           , MultiParamTypeClasses
           , FlexibleContexts
           , FlexibleInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.05.24
-- |
-- Module      :  Language.Hakaru.Evaluation.EvalMonad
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
--
----------------------------------------------------------------
module Language.Hakaru.Evaluation.EvalMonad
    ( runPureEvaluate
    , pureEvaluate

    -- * The pure-evaluation monad
    -- ** List-based version
    , ListContext(..), PureAns, Eval(..), runEval
    , residualizePureListContext
    -- ** TODO: IntMap-based version
    ) where

import           Prelude              hiding (id, (.))
import           Control.Category     (Category(..))
#if __GLASGOW_HASKELL__ < 710
import           Data.Functor         ((<$>))
import           Control.Applicative  (Applicative(..))
#endif
import qualified Data.Foldable        as F

import Language.Hakaru.Syntax.IClasses (Some2(..))
import Language.Hakaru.Syntax.Variable (memberVarSet)
import Language.Hakaru.Syntax.ABT      (ABT(..), subst, maxNextFree)
import Language.Hakaru.Syntax.DatumABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Evaluation.Types
import Language.Hakaru.Evaluation.Lazy (evaluate)
import Language.Hakaru.Evaluation.PEvalMonad (ListContext(..))


-- The rest of these are just for the emit code, which isn't currently exported.
import           Data.Text             (Text)
import qualified Data.Text             as Text
import qualified Data.Traversable      as T
import Language.Hakaru.Syntax.IClasses (Functor11(..))
import Language.Hakaru.Syntax.Variable (Variable(), toAssocs1)
import Language.Hakaru.Syntax.ABT      (caseVarSyn, caseBinds, substs)
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing      (Sing, sUnPair)
import Language.Hakaru.Syntax.TypeOf   (typeOf)
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Evaluation.Lazy (reifyPair)
#ifdef __TRACE_DISINTEGRATE__
import Debug.Trace                     (trace)
#endif

----------------------------------------------------------------
----------------------------------------------------------------
-- | Call 'evaluate' on a term. This variant returns an @abt@ expression itself so you needn't worry about the 'Eval' monad. For the monadic-version, see 'pureEvaluate'.
--
-- BUG: now that we've indexed 'ListContext' by a 'Purity', does exposing the implementation details still enable clients to break our invariants?
runPureEvaluate :: (ABT Term abt) => abt '[] a -> abt '[] a
runPureEvaluate e = runEval (fromWhnf <$> pureEvaluate e) [Some2 e]


-- 'evaluate' itself can never @lub@ or @bot@, as captured by the
-- fact that it's type doesn't include 'Alternative' nor 'MonadPlus'
-- constraints. So non-singularity of results could only come from
-- calling @perform@. However, we will never call perform because: (a) the initial heap must be 'Pure' so we will never call @perform@ for a statement on the initial heap, and (b) 'evaluate' itself will never push impure statements so we will never call @perform@ for the statements we push either.
--
-- | Call 'evaluate' on a term. This variant returns something in the 'Eval' monad so you can string multiple evaluation calls together. For the non-monadic version, see 'runPureEvaluate'.
pureEvaluate :: (ABT Term abt) => TermEvaluator abt (Eval abt)
pureEvaluate = evaluate (brokenInvariant "perform")


----------------------------------------------------------------
type PureAns abt a = ListContext abt 'Pure -> abt '[] a

newtype Eval abt x =
    Eval { unEval :: forall a. (x -> PureAns abt a) -> PureAns abt a }

brokenInvariant :: String -> a
brokenInvariant loc = error (loc ++ ": Eval's invariant broken")


-- | Run a computation in the 'Eval' monad, residualizing out all the
-- statements in the final evaluation context. The second argument
-- should include all the terms altered by the 'Eval' expression; this
-- is necessary to ensure proper hygiene; for example(s):
--
-- > runEval (pureEvaluate e) [Some2 e]
--
-- We use 'Some2' on the inputs because it doesn't matter what their
-- type or locally-bound variables are, so we want to allow @f@ to
-- contain terms with different indices.
runEval :: (ABT Term abt, F.Foldable f)
    => Eval abt (abt '[] a)
    -> f (Some2 abt)
    -> abt '[] a
runEval (Eval m) es =
    m residualizePureListContext (ListContext (maxNextFree es) [])
    

residualizePureListContext
    :: forall abt a
    .  (ABT Term abt)
    => abt '[] a
    -> ListContext abt 'Pure
    -> abt '[] a
residualizePureListContext e0 =
    foldl step e0 . statements
    where
    -- TODO: make paremetric in the purity, so we can combine 'residualizeListContext' with this function.
    step :: abt '[] a -> Statement abt Location  'Pure -> abt '[] a
    step e s =
        case s of
        SLet (Location x) body _
            | not (x `memberVarSet` freeVars e) -> e
            -- TODO: if used exactly once in @e@, then inline.
            | otherwise ->
                case getLazyVariable body of
                Just y  -> subst x (var y) e
                Nothing ->
                    case getLazyLiteral body of
                    Just v  -> subst x (syn $ Literal_ v) e
                    Nothing ->
                        syn (Let_ :$ fromLazy body :* bind x e :* End)
                

----------------------------------------------------------------
instance Functor (Eval abt) where
    fmap f (Eval m) = Eval $ \c -> m (c . f)

instance Applicative (Eval abt) where
    pure x              = Eval $ \c -> c x
    Eval mf <*> Eval mx = Eval $ \c -> mf $ \f -> mx $ \x -> c (f x)

instance Monad (Eval abt) where
    return       = pure
    Eval m >>= k = Eval $ \c -> m $ \x -> unEval (k x) c

instance (ABT Term abt) => EvaluationMonad abt (Eval abt) 'Pure where
    freshNat =
        Eval $ \c (ListContext i ss) ->
            c i (ListContext (i+1) ss)

    unsafePush s =
        Eval $ \c (ListContext i ss) ->
            c () (ListContext i (s:ss))

    -- N.B., the use of 'reverse' is necessary so that the order
    -- of pushing matches that of 'pushes'
    unsafePushes ss =
        Eval $ \c (ListContext i ss') ->
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
                    Nothing -> loop (s:ss)
                    Just mr -> do
                        r <- mr
                        unsafePushes ss
                        return (Just r)

-- TODO: make parametric in the purity
-- | Not exported because we only need it for defining 'select' on 'Eval'.
unsafePop :: Eval abt (Maybe (Statement abt Location 'Pure))
unsafePop =
    Eval $ \c h@(ListContext i ss) ->
        case ss of
        []    -> c Nothing  h
        s:ss' -> c (Just s) (ListContext i ss')


----------------------------------------------------------------
----------------------------------------------------------------
-- | Emit some code that binds a variable, and return the variable
-- thus bound. The function says what to wrap the result of the
-- continuation with; i.e., what we're actually emitting.
emit
    :: (ABT Term abt)
    => Text
    -> Sing a
    -> (forall r. abt '[a] r -> abt '[] r)
    -> Eval abt (Variable a)
emit hint typ f = do
    x <- freshVar hint typ
    Eval $ \c h -> (f . bind x) $ c x h


-- | A smart constructor for emitting let-bindings. If the input
-- is already a variable then we just return it; otherwise we emit
-- the let-binding. N.B., this function provides the invariant that
-- the result is in fact a variable; whereas 'emitLet'' does not.
emitLet :: (ABT Term abt) => abt '[] a -> Eval abt (Variable a)
emitLet e =
    caseVarSyn e return $ \_ ->
        emit Text.empty (typeOf e) $ \f ->
            syn (Let_ :$ e :* f :* End)

-- | A smart constructor for emitting let-bindings. If the input
-- is already a variable or a literal constant, then we just return
-- it; otherwise we emit the let-binding. N.B., this function
-- provides weaker guarantees on the type of the result; if you
-- require the result to always be a variable, then see 'emitLet'
-- instead.
emitLet' :: (ABT Term abt) => abt '[] a -> Eval abt (abt '[] a)
emitLet' e =
    caseVarSyn e (const $ return e) $ \t ->
        case t of
        Literal_ _ -> return e
        _          -> do
            x <- emit Text.empty (typeOf e) $ \f ->
                syn (Let_ :$ e :* f :* End)
            return (var x)

-- | A smart constructor for emitting \"unpair\". If the input
-- argument is actually a constructor then we project out the two
-- components; otherwise we emit the case-binding and return the
-- two variables.
emitUnpair
    :: (ABT Term abt)
    => Whnf abt (HPair a b)
    -> Eval abt (abt '[] a, abt '[] b)
emitUnpair (Head_   w) = return $ reifyPair w
emitUnpair (Neutral e) = do
    let (a,b) = sUnPair (typeOf e)
    x <- freshVar Text.empty a
    y <- freshVar Text.empty b
    emitUnpair_ x y e

emitUnpair_
    :: forall abt a b
    .  (ABT Term abt)
    => Variable a
    -> Variable b
    -> abt '[] (HPair a b)
    -> Eval abt (abt '[] a, abt '[] b)
emitUnpair_ x y = loop
    where
    done :: abt '[] (HPair a b) -> Eval abt (abt '[] a, abt '[] b)
    done e =
#ifdef __TRACE_DISINTEGRATE__
        trace "-- emitUnpair: done (term is not Datum_ nor Case_)" $
#endif
        Eval $ \c h ->
            ( syn
            . Case_ e
            . (:[])
            . Branch (pPair PVar PVar)
            . bind x
            . bind y
            ) $ c (var x, var y) h

    loop :: abt '[] (HPair a b) -> Eval abt (abt '[] a, abt '[] b)
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
                -- N.B., the only 'Eval'-effects in 'applyBranch'
                -- are to freshen variables; thus this use of
                -- 'traverse' is perfectly sound.
                emitCaseWith loop e bs
            _ -> done e0

-- TODO: emitUneither

-- | Run each of the elements of the traversable using the same
-- heap and continuation for each one, then pass the results to a
-- function for emitting code.
emitFork_
    :: (ABT Term abt, T.Traversable t)
    => (forall r. t (abt '[] r) -> abt '[] r)
    -> t (Eval abt a)
    -> Eval abt a
emitFork_ f ms =
    Eval $ \c h -> f $ fmap (\m -> unEval m c h) ms


emitCaseWith
    :: (ABT Term abt)
    => (abt '[] b -> Eval abt r)
    -> abt '[] a
    -> [Branch a abt b]
    -> Eval abt r
emitCaseWith f e bs = do
    gms <- T.for bs $ \(Branch pat body) ->
        let (vars, body') = caseBinds body
        in  (\vars' ->
                let rho = toAssocs1 vars (fmap11 var vars')
                in  GBranch pat vars' (f $ substs rho body')
            ) <$> freshenVars vars
    Eval $ \c h ->
        syn (Case_ e
            (map (fromGBranch . fmap (\m -> unEval m c h)) gms))
{-# INLINE emitCaseWith #-}

----------------------------------------------------------------
----------------------------------------------------------- fin.
