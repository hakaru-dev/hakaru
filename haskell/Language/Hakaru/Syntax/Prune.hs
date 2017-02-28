{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeOperators              #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2017.02.01
-- |
-- Module      :  Language.Hakaru.Syntax.Prune
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :
-- Stability   :  experimental
-- Portability :  GHC-only
--
--
----------------------------------------------------------------
module Language.Hakaru.Syntax.Prune (prune) where

import           Control.Monad.Reader
import           Data.Maybe

import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.AST.Eq
import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Syntax.Unroll   (renameInEnv)
import           Language.Hakaru.Types.DataKind

-- A Simple pass for pruning the unused let bindings from an AST.

newtype PruneM a = PruneM { runPruneM :: Reader Varmap a }
  deriving (Functor, Applicative, Monad, MonadReader Varmap, MonadFix)

lookupEnv
  :: forall (a :: Hakaru)
  .  Variable a
  -> Varmap
  -> Variable a
lookupEnv v = fromMaybe v . lookupAssoc v

prune
  :: (ABT Term abt)
  => abt '[] a
  -> abt '[] a
prune = flip runReader emptyAssocs . runPruneM . prune'

prune'
  :: forall abt xs a . (ABT Term abt)
  => abt xs a
  -> PruneM (abt xs a)
prune' = loop . viewABT
   where
    loop :: forall (b :: Hakaru) ys . View (Term abt) ys b -> PruneM (abt ys b)
    loop (Var v)    = (var . lookupEnv v) `fmap` ask
    loop (Syn s)    = pruneTerm s
    loop (Bind v b) = renameInEnv v (loop b)

pruneTerm
  :: forall a abt
  .  (ABT Term abt)
  => Term abt a
  -> PruneM (abt '[] a)
pruneTerm (Let_ :$ rhs :* body :* End) =
  caseBind body $ \v body' ->
  let frees     = freeVars body'
      mklet r b = syn (Let_ :$ r :* b :* End)
      doRhs     = prune' rhs
      doBody    = prune' body'
      fullExpr  = mklet <$> doRhs <*> renameInEnv v doBody
  in case viewABT body' of
       Var v' | Just Refl <- varEq v v' -> doRhs
       _      | memberVarSet v frees    -> fullExpr
              | otherwise               -> doBody

pruneTerm term = syn <$> traverse21 prune' term
