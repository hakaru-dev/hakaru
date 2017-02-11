{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}

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
import           Language.Hakaru.Evaluation.EvalMonad (runPureEvaluate)
import           Language.Hakaru.Syntax.ABT           (ABT (..), View (..))
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.IClasses      (Traversable21 (..))
import           Language.Hakaru.Syntax.Variable

type Env = Assocs Literal

newtype PropM a = PropM { runPropM :: Reader Env a }
  deriving (Functor, Applicative, Monad, MonadReader Env)

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
    loop (Syn s)    = constantPropTerm s --alg <$> traverse21 start s
    loop (Bind v b) = bind v <$> loop b


tryEval :: forall abt b . (ABT Term abt) => Term abt b -> abt '[] b
tryEval t =
  case traverse21 getLit t of
    Nothing -> syn t
    Just t' -> runPureEvaluate (syn t')
  where
    getLit :: forall a ys . abt ys a -> Maybe (abt ys a)
    getLit l = case viewABT l of
                 Syn (Literal_ _) -> Just l
                 _                -> Nothing

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

