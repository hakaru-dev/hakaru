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
--                                                    2016.03.29
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
import Language.Hakaru.Evaluation.EvalMonad (runPureEvaluate)

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
        Just t' -> runPureEvaluate (syn t')

----------------------------------------------------------------
----------------------------------------------------------- fin.
