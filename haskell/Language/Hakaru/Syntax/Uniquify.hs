{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2017.02.01
-- |
-- Module      :  Language.Hakaru.Syntax.Uniquify
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Performs renaming of Hakaru expressions to ensure globally unique variable
-- identifiers.
--
----------------------------------------------------------------
module Language.Hakaru.Syntax.Uniquify where

import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Maybe                      (fromMaybe)
import           Data.Number.Nat

import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.AST.Eq   (Varmap)
import           Language.Hakaru.Syntax.IClasses

newtype Uniquifier a = Uniquifier { runUniquifier :: StateT Nat (Reader Varmap) a }
  deriving (Functor, Applicative, Monad, MonadState Nat, MonadReader Varmap)

uniquify :: (ABT Term abt) => abt '[] a -> abt '[] a
uniquify abt = fst $ runReader (runStateT unique seed) emptyAssocs
  where
    unique = runUniquifier (uniquify' abt)
    seed   = nextFreeOrBind abt

genVarID :: Uniquifier Nat
genVarID = do
  vid <- get
  put (succ vid)
  return vid

newVar :: Variable a -> Uniquifier (Variable a)
newVar v = do
  vid <- genVarID
  let fresh = v { varID = vid }
  return fresh

uniquify'
  :: forall abt xs a . (ABT Term abt)
  => abt xs a
  -> Uniquifier (abt xs a)
uniquify' = loop . viewABT
  where
    loop :: View (Term abt) ys a -> Uniquifier (abt ys a)
    loop (Var v)    = uniquifyVar v
    loop (Syn s)    = fmap syn (traverse21 uniquify' s)
    loop (Bind v b) = do
      vid <- genVarID
      let fresh = v { varID = vid }
          assoc = Assoc v fresh
      -- Process the body with the updated Varmap and wrap the
      -- result in a bind form
      bind fresh <$> local (insertAssoc assoc) (loop b)

uniquifyVar
  :: (ABT Term abt)
  => Variable a
  -> Uniquifier (abt '[] a)
uniquifyVar v = (var . fromMaybe v . lookupAssoc v) <$> ask

