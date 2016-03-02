{-# LANGUAGE CPP
           , GADTs
           , DataKinds
           , Rank2Types
           , ScopedTypeVariables
           , MultiParamTypeClasses
           , FlexibleContexts
           , FlexibleInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.02.09
-- |
-- Module      :  Language.Hakaru.Evaluation.ConstantPropagation
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
--
----------------------------------------------------------------
module Language.Hakaru.Evaluation.ConstantPropagation
    ( constantPropagation
    , pureEvaluate
    ) where

import           Prelude              hiding (id, (.))
import           Control.Category     (Category(..))
#if __GLASGOW_HASKELL__ < 710
import           Data.Functor         ((<$>))
import           Control.Applicative  (Applicative(..))
#endif
import qualified Data.Foldable        as F

import Language.Hakaru.Syntax.IClasses (Traversable21(..), Some2(..))
import Data.Number.Nat                 (MaxNat(..))
import Language.Hakaru.Syntax.Variable (memberVarSet)
import Language.Hakaru.Syntax.ABT      (View(..), ABT(..), subst, cataABT)
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Evaluation.Types
import Language.Hakaru.Evaluation.Lazy (evaluate, defaultCaseEvaluator)
import Language.Hakaru.Evaluation.DisintegrationMonad (ListContext(..))

----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: try evaluating certain things even if not all their immediate
-- subterms are literals. For example:
-- (1) substitute let-bindings of literals
-- (2) evaluate beta-redexes where the argument is a literal
-- (3) evaluate case-of-constructor if we can
-- (4) handle identity elements for NaryOps
-- N.B., some of these will require performing top-down work to
-- avoid re-traversing subtrees.
--
-- | Perform basic constant propagation.
constantPropagation
    :: forall abt a. (ABT Term abt) => abt '[] a -> abt '[] a
constantPropagation =
    cataABT var bind alg
    where
    getLiteral :: forall xs b. abt xs b -> Maybe (abt xs b)
    getLiteral e =
        case viewABT e of
        Syn (Literal_ _) -> Just e
        _                -> Nothing

    alg :: forall b. Term abt b -> abt '[] b
    alg t =
        case traverse21 getLiteral t of
        Nothing -> syn t
        Just t' -> pureEvaluate (syn t')


-- 'evaluate' itself can never @lub@ or @bot@, as captured by the
-- fact that it's type doesn't include 'Alternative' nor 'MonadPlus'
-- constraints. So non-singularity of results could only come from
-- calling @perform@. However, 'evaluate' itself will never push
-- impure statements. So if the initial heap is pure then the
-- @perform@ function will never be called. And since we start off
-- with the empty heap (by calling 'runEval' directly), we know the
-- heap is pure.
--
-- | Call 'evaluate' on a term. This function will return a 'Whnf',
-- even though the type doesn't capture that invariant. We use this function for implementing 'constantPropagation', and expose it because it's surely helpful in other contexts. We do not, however, expose its implementation details because doing so would enable breaking our invariants.
pureEvaluate :: (ABT Term abt) => abt '[] a -> abt '[] a
pureEvaluate e =
    runEval
        (fromWhnf <$>
            evaluate (brokenInvariant "perform") defaultCaseEvaluator e)
        [Some2 e]


----------------------------------------------------------------
-- 'evaluate' itself can never @lub@ or @bot@, as captured by the
-- fact that it's type doesn't include 'Alternative' nor 'MonadPlus'
-- constraints. So non-singularity of results could only come from
-- calling @perform@; but we never call @perform@.
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
-- > runEval (evaluate_ e) [Some2 e]
--
-- We use 'Some2' on the inputs because it doesn't matter what their
-- type or locally-bound variables are, so we want to allow @f@ to
-- contain terms with different indices.
runEval :: (ABT Term abt, F.Foldable f)
    => Eval abt (abt '[] a)
    -> f (Some2 abt)
    -> abt '[] a
runEval (Eval m) es =
    let i0 = unMaxNat (F.foldMap (\(Some2 e) -> MaxNat $ nextFree e) es)
    in  m residualizePureListContext (ListContext i0 [])
    

residualizePureListContext
    :: forall abt a
    .  (ABT Term abt)
    => abt '[] a
    -> ListContext abt 'Pure
    -> abt '[] a
residualizePureListContext e0 =
    foldl step e0 . statements
    where
    -- TODO: make paremetric in the purity
    step :: abt '[] a -> Statement abt 'Pure -> abt '[] a
    step e s =
        case s of
        SIndex  _ _ _ -> error "TODO: residualizePureListContext{SIndex}"
        SLet x body
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

            
    -- TODO: we might could go one step further in guaranteeing our invariants by checking that the caller isn't trying to push an impure statement. Though that would add administrative overhead...
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

-- TODO: make paremetric in the purity
-- | Not exported because we only need it for defining 'select' on 'Eval'.
unsafePop :: Eval abt (Maybe (Statement abt 'Pure))
unsafePop =
    Eval $ \c h@(ListContext i ss) ->
        case ss of
        []    -> c Nothing  h
        s:ss' -> c (Just s) (ListContext i ss')

----------------------------------------------------------------
----------------------------------------------------------- fin.
