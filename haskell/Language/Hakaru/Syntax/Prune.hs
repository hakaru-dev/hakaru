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
module Language.Hakaru.Syntax.Prune where

import           Control.Monad.Reader
import           Data.Maybe

import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.AST.Eq
import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Syntax.Unroll   (renameInEnv)
import           Language.Hakaru.Types.DataKind

-- A Simple pass for pruning the unused let bindings from an AST.

updateEnv :: forall (a :: Hakaru) . Variable a -> Variable a -> Varmap -> Varmap
updateEnv vin vout = insertAssoc (Assoc vin vout)

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
prune' = cataABTM var_ renameInEnv (>>= pruneTerm)
  where
    var_ :: Variable b -> PruneM (abt '[] b)
    var_ v = var . lookupEnv v <$> ask

pruneTerm
  :: (ABT Term abt)
  => Term abt a
  -> PruneM (abt '[] a)
pruneTerm (Let_ :$ rhs :* body :* End) =
  caseBind body $ \v body' ->
  let frees     = freeVars body'
      mklet r b = syn (Let_ :$ r :* b :* End)
  in if memberVarSet v frees
     then mklet <$> prune' rhs <*> renameInEnv v (prune' body')
     else prune' body'

pruneTerm term = syn <$> traverse21 prune' term
