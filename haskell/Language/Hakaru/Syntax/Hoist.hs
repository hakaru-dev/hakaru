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
-- Module      :  Language.Hakaru.Syntax.Hoist
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :
-- Stability   :  experimental
-- Portability :  GHC-only
--
--
----------------------------------------------------------------
module Language.Hakaru.Syntax.Hoist where

import           Control.Monad.Reader
import           Control.Monad.Writer.Strict
import           Data.Maybe

import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.AST.Eq
import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Syntax.TypeOf
import           Language.Hakaru.Types.DataKind

data Entry = forall (a :: Hakaru) (abt :: [Hakaru] -> Hakaru -> *)
           . Entry !(Variable a) !(VarSet (KindOf a)) !(abt '[] a)

newtype HoistM a = HoistM { runHoistM :: ReaderT (VarSet (KindOf Hakaru)) (Writer [Entry]) a }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadReader (VarSet (KindOf Hakaru))
           , MonadWriter [Entry] )

execHoistM :: HoistM a -> a
execHoistM = fst . runWriter . flip runReaderT emptyVarSet . runHoistM

hoist
  :: (ABT Term abt)
  => abt '[] a
  -> abt '[] a
hoist = execHoistM . hoist'

hoist'
  :: forall abt xs a . (ABT Term abt)
  => abt xs a
  -> HoistM (abt xs a)
hoist' = start
  where
    start :: forall ys b . abt ys b -> HoistM (abt ys b)
    start = loop . viewABT

    loop :: forall ys b . View (Term abt) ys b -> HoistM (abt ys b)
    loop (Var v)    = return (var v)
    loop (Syn s)    = hoistTerm s
    loop (Bind v b) = undefined

zapDependencies
  :: forall (a :: Hakaru) b
  .  Variable a
  -> HoistM b
  -> HoistM b
zapDependencies var = censor zap
  where
    zap :: [Entry] -> [Entry]
    zap = filter (\ (Entry _ s _) -> not $ memberVarSet var s)

hoistTerm
  :: (ABT Term abt)
  => Term abt a
  -> HoistM (abt '[] a)
hoistTerm (Let_ :$ rhs :* body :* End) = do
  undefined

hoistTerm term = fmap syn (traverse21 hoist' term)

