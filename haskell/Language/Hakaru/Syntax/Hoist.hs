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

import           Data.Proxy        (KProxy(..))
import           Control.Monad.Reader
import           Control.Monad.Writer.Strict

import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Types.DataKind

data Entry = forall (a :: Hakaru) (abt :: [Hakaru] -> Hakaru -> *)
           . Entry !(Variable a) !(VarSet (KindOf a)) !(abt '[] a)

type HakaruProxy = ('KProxy :: KProxy Hakaru)

-- The @HoistM@ monad makes use of two monadic layers to propagate information
-- both downwards to the leaves and upwards to the root node.
--
-- The Writer layer propagates the live expressions which may be hoisted (i.e.
-- all their data dependencies are currently filled) from each subexpression to
-- their parents.
--
-- The Reader layer propagates the currently bound variables which will be used
-- to decide when to
newtype HoistM a = HoistM { runHoistM :: ReaderT (VarSet HakaruProxy) (Writer [Entry]) a }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadReader (VarSet HakaruProxy)
           , MonadWriter [Entry] )

execHoistM :: HoistM a -> a
execHoistM = fst . runWriter . flip runReaderT emptyVarSet . runHoistM

hoist
  :: (ABT Term abt)
  => abt '[] a
  -> abt '[] a
hoist = execHoistM . hoist'

zapDependencies
  :: forall (a :: Hakaru) b
  .  Variable a
  -> HoistM b
  -> HoistM b
zapDependencies v = censor zap
  where
    zap :: [Entry] -> [Entry]
    zap = filter (\ (Entry _ s _) -> not $ memberVarSet v s)

isolateBinder
  :: Variable (a :: Hakaru)
  -> HoistM b
  -> HoistM (b, [Entry])
isolateBinder v = zapDependencies v . local (insertVarSet v) . listen

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
    loop (Bind v b) = fmap (bind v . fst) (isolateBinder v $ loop b)

introducePotentialBindings
  :: (ABT Term abt)
  => abt '[] a
  -> [Entry]
  -> HoistM (abt '[] a)
introducePotentialBindings body bindings = do
  available <- ask
  undefined

hoistTerm
  :: forall (a :: Hakaru) (abt :: [Hakaru] -> Hakaru -> *) . (ABT Term abt)
  => Term abt a
  -> HoistM (abt '[] a)
hoistTerm (Let_ :$ rhs :* body :* End) = do
  rhs' <- hoist' rhs
  caseBind body $ \ v body' -> do
    (body'', bindings) <- isolateBinder v (hoist' body')
    tell [Entry v (freeVars rhs') rhs']
    return $ syn (Let_ :$ rhs :* bind v body'' :* End)

hoistTerm term = fmap syn (traverse21 hoist' term)

