{-# LANGUAGE CPP
           , DataKinds
           , EmptyCase
           , ExistentialQuantification
           , FlexibleContexts
           , GADTs
           , GeneralizedNewtypeDeriving
           , KindSignatures
           , MultiParamTypeClasses
           , OverloadedStrings
           , PolyKinds
           , ScopedTypeVariables
           , TypeFamilies
           , TypeOperators
           #-}

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
module Language.Hakaru.Syntax.Uniquify (uniquify) where

import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Maybe                      (fromMaybe)
import           Data.Number.Nat

import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.AST.Eq   (Varmap)
import           Language.Hakaru.Syntax.IClasses
import           Debug.Trace

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative
#endif

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
uniquify' = start
  where
    start :: abt ys b -> Uniquifier (abt ys b)
    start = loop . viewABT

    loop :: View (Term abt) ys b -> Uniquifier (abt ys b)
    loop (Var v)    = uniquifyVar v
    loop (Syn s)    = fmap syn (traverse21 start s)
    loop (Bind v b) = do
      fresh <- newVar v
      let assoc = Assoc v fresh
      -- Process the body with the updated Varmap and wrap the
      -- result in a bind form
      bind fresh <$> local (insertAssoc assoc) (loop b)

uniquifyVar
  :: (ABT Term abt)
  => Variable a
  -> Uniquifier (abt '[] a)
uniquifyVar v = (var . fromMaybe v . lookupAssoc v) <$> ask

