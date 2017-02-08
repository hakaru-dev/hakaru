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
import           Control.Monad.RWS
import           Data.Proxy                      (KProxy (..))
import           Prelude                         hiding ((+))

import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Syntax.Prelude  hiding (fst, not)
import           Language.Hakaru.Types.DataKind

data Entry (abt :: Hakaru -> *)
  = forall (a :: Hakaru) . Entry
  { varDependencies :: !(VarSet (KindOf a))
  , expression      :: !(abt a)
  , binding         :: !(Maybe (Variable a))
  }

type VarState = Assocs Entry

type HakaruProxy = ('KProxy :: KProxy Hakaru)
type LiveSet = VarSet HakaruProxy

-- The @HoistM@ monad makes use of two monadic layers to propagate information
-- both downwards to the leaves and upwards to the root node.
--
-- The Writer layer propagates the live expressions which may be hoisted (i.e.
-- all their data dependencies are currently filled) from each subexpression to
-- their parents.
--
-- The Reader layer propagates the currently bound variables which will be used
-- to decide when to
newtype HoistM (abt :: [Hakaru] -> Hakaru -> *) a
  = HoistM { runHoistM :: RWS LiveSet [Entry (abt '[])] Int a }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadReader (VarSet HakaruProxy)
           , MonadWriter [Entry (abt '[])] )

example :: TrivialABT Term '[] 'HInt
example = let_ (int_ 0) $ \z ->
          summate (int_ 0) (int_ 1) $ \x ->
          summate (int_ 0) (int_ 1) $ \y ->
          z + int_ 1

execHoistM :: HoistM abt a -> a
execHoistM act = a
  where
    hoisted   = runHoistM act
    (a, _, _) = runRWS hoisted emptyVarSet 0

hoist
  :: (ABT Term abt)
  => abt '[] a
  -> abt '[] a
hoist = execHoistM . hoist'

zapDependencies
  :: forall (a :: Hakaru) b abt
  .  Variable a
  -> HoistM abt b
  -> HoistM abt b
zapDependencies v = censor zap
  where
    zap :: [Entry (abt '[])] -> [Entry (abt '[])]
    zap = filter (\ Entry{varDependencies=d} -> not $ memberVarSet v d)

isolateBinder
  :: Variable (a :: Hakaru)
  -> HoistM abt b
  -> HoistM abt (b, [Entry (abt '[])])
isolateBinder v = zapDependencies v . local (insertVarSet v) . listen

hoist'
  :: forall abt xs a . (ABT Term abt)
  => abt xs a
  -> HoistM abt (abt xs a)
hoist' = start
  where
    start :: forall ys b . abt ys b -> HoistM abt (abt ys b)
    start = loop [] . viewABT

    loop :: forall ys b
         .  [SomeVariable HakaruProxy]
         -> View (Term abt) ys b
         -> HoistM abt (abt ys b)
    loop xs (Var v)    = return (var v)
    loop xs (Syn s)    = hoistTerm s
    loop xs (Bind v b) = do
      let xs' = SomeVariable v : xs
      b' <- zapDependencies v (loop xs' b)
      return (bind v b')

introducePotentialBindings
  :: (ABT Term abt)
  => abt '[] a
  -> [Entry (abt '[])]
  -> (abt '[] a)
introducePotentialBindings = foldl wrap
  where
    wrap acc Entry{expression=e} = let_ e (const acc)

hoistTerm
  :: forall (a :: Hakaru) (abt :: [Hakaru] -> Hakaru -> *) . (ABT Term abt)
  => Term abt a
  -> HoistM abt (abt '[] a)
hoistTerm (Let_ :$ rhs :* body :* End) = do
  rhs' <- hoist' rhs
  caseBind body $ \ v body' -> do
    (body'', bindings) <- isolateBinder v (hoist' body')
    let wrapped = introducePotentialBindings body'' bindings
    return $ syn (Let_ :$ rhs :* bind v wrapped :* End)

hoistTerm term = do
  result <- fmap syn $ traverse21 hoist' term
  tell [Entry (freeVars $ result) result Nothing]
  return result


