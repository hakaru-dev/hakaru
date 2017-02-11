{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE ViewPatterns               #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.04.02
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

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative                  (Applicative (..))
import           Data.Functor                         ((<$>))
#endif

import           Control.Monad.Reader
import           Data.Monoid                          (All (..))
import           Language.Hakaru.Evaluation.EvalMonad (runPureEvaluate)
import           Language.Hakaru.Syntax.ABT           (ABT (..), View (..))
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.IClasses      (Foldable21 (..),
                                                       Traversable21 (..))
import           Language.Hakaru.Syntax.Variable

type Env = Assocs Literal

-- The constant propagation monad. Simply threads through an environment mapping
-- variables to known constant values.
newtype PropM a = PropM { runPropM :: Reader Env a }
  deriving (Functor, Applicative, Monad, MonadReader Env)

----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: try evaluating certain things even if not all their immediate
-- subterms are literals. For example:
-- (1) evaluate beta-redexes where the argument is a literal
-- (2) evaluate case-of-constructor if we can
-- (3) handle identity elements for NaryOps
--
-- | Perform basic constant propagation.
constantPropagation
  :: forall abt a . (ABT Term abt)
  => abt '[] a
  -> abt '[] a
constantPropagation abt = runReader (runPropM $ constantProp' abt) emptyAssocs

constantProp'
  :: forall abt a xs . (ABT Term abt)
  => abt xs a
  -> PropM (abt xs a)
constantProp' = start
  where

    start :: forall b ys . abt ys b -> PropM (abt ys b)
    start = loop . viewABT

    loop :: forall b ys . View (Term abt) ys b -> PropM (abt ys b)
    loop (Var v)    = (maybe (var v) (syn . Literal_) . lookupAssoc v) <$> ask
    loop (Syn s)    = constantPropTerm s
    loop (Bind v b) = bind v <$> loop b

tryEval :: forall abt b . (ABT Term abt) => Term abt b -> abt '[] b
tryEval term
  | isFoldable term = runPureEvaluate (syn term)
  | otherwise       = syn term

isFoldable :: forall abt b . (ABT Term abt) => Term abt b -> Bool
isFoldable = getAll . foldMap21 islit
  where
    islit :: forall a ys . abt ys a -> All
    islit (viewABT -> Syn (Literal_ _)) = All True
    islit _                             = All False

getLiteral :: forall abt ys b. (ABT Term abt) => abt ys b -> Maybe (Literal b)
getLiteral e =
  case viewABT e of
    Syn (Literal_ l) -> Just l
    _                -> Nothing

constantPropTerm
  :: (ABT Term abt)
  => Term abt a
  -> PropM (abt '[] a)
constantPropTerm (Let_ :$ rhs :* body :* End) =
  caseBind body $ \v body' -> do
    rhs' <- constantProp' rhs
    case getLiteral rhs' of
      Just l  -> local (insertAssoc (Assoc v l)) (constantProp' body')
      Nothing -> do
        body'' <- constantProp' body'
        return $ syn (Let_ :$ rhs' :* bind v body'' :* End)

constantPropTerm term = tryEval <$> traverse21 constantProp' term

