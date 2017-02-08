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
import           Control.Monad.RWS
import           Control.Monad.Writer.Strict
import qualified Data.Maybe                      as M
import           Data.Number.Nat
import           Data.Proxy                      (KProxy (..))
import           Prelude                         hiding ((+))

import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Syntax.Prelude  hiding (fst, maybe, not, (<$>), (==))
import           Language.Hakaru.Syntax.TypeOf   (typeOf)
import           Language.Hakaru.Syntax.Variable (varSubSet)
import           Language.Hakaru.Types.DataKind
import           Language.Hakaru.Types.Sing      (Sing)
import Debug.Trace

data Entry (abt :: Hakaru -> *)
  = forall (a :: Hakaru) . Entry
  { varDependencies :: !(VarSet (KindOf a))
  , expression      :: !(abt a)
  , binding         :: !(Maybe (Variable a))
  }

instance Show (Entry a) where
  show (Entry deps _ bindings) = "Entry (" ++ show deps ++ ") (" ++ show bindings ++ ")"

type VarState = Assocs Entry

type HakaruProxy = ('KProxy :: KProxy Hakaru)
type LiveSet = VarSet HakaruProxy

-- The @HoistM@ monad makes use of three monadic layers to propagate information
-- both downwards to the leaves and upwards to the root node.
--
-- The Writer layer propagates the live expressions which may be hoisted (i.e.
-- all their data dependencies are currently filled) from each subexpression to
-- their parents.
--
-- The Reader layer propagates the currently bound variables which will be used
-- to decide when to introduce new bindings.
--
-- The State layer is just to provide a counter in order to gensym new
-- variables, since the process of adding new bindings is a little tricky.
-- What we want is to fully duplicate bindings without altering the original
-- variable identifiers. To do so, all original variable names are preserved and
-- new variables are added outside the range of existing variables.
newtype HoistM (abt :: [Hakaru] -> Hakaru -> *) a
  = HoistM { runHoistM :: RWS LiveSet [Entry (abt '[])] Nat a }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadReader (VarSet HakaruProxy)
           , MonadState Nat
           , MonadWriter [Entry (abt '[])] )

example :: TrivialABT Term '[] 'HInt
example = let_ (int_ 0) $ \z ->
          summate (int_ 0) (int_ 1) $ \x ->
          summate (int_ 0) (int_ 1) $ \y ->
          z + int_ 1

execHoistM :: Nat -> HoistM abt a -> a
execHoistM counter act = a
  where
    hoisted   = runHoistM act
    (a, _, _) = runRWS hoisted emptyVarSet counter

newVar
  :: (ABT Term abt)
  => Sing a
  -> HoistM abt (Variable a)
newVar typ = do
  vid <- gets succ
  put vid
  return $ Variable "" vid typ

hoist
  :: (ABT Term abt)
  => abt '[] a
  -> abt '[] a
hoist abt = execHoistM (nextFreeOrBind abt) $ do
  (abt', w) <- listen $ hoist' abt
  let toplevel = filter (\Entry{varDependencies=d} -> sizeVarSet d == 0) w
  introducePotentialBindings emptyVarSet [] abt' toplevel True

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

    loop [] (Syn s)    = hoistTerm s

    loop xs (Syn s)    = do
      (term, entries) <- listen $ hoistTerm s
      available       <- ask
      introducePotentialBindings available xs term entries False

    loop xs (Bind v b) = do
      let xs' = SomeVariable v : xs
      b' <- zapDependencies v (loop xs' b)
      return (bind v b')

introducePotentialBindings
  :: forall (a :: Hakaru) abt
  .  (ABT Term abt)
  => VarSet HakaruProxy
  -> [SomeVariable HakaruProxy]
  -> abt '[] a
  -> [Entry (abt '[])]
  -> Bool
  -> HoistM abt (abt '[] a)
introducePotentialBindings available init body entries top =
  foldM wrap body resultEntries
  where
    wrap :: abt '[] b -> Entry (abt '[]) -> HoistM abt (abt '[] b)
    wrap acc Entry{expression=e,binding=b} =
      case b of
        Just v  -> return $ syn (Let_ :$ e :* bind v acc :* End)
        Nothing -> do
          v <- newVar (typeOf e)
          return $ syn (Let_ :$ e :* bind v acc :* End)

    toplevel :: [Entry (abt '[])]
    toplevel
      | top       = filter (\Entry{varDependencies=d} -> sizeVarSet d == 0) entries
      | otherwise = []

    topvars = M.mapMaybe (\Entry{binding=b} -> fmap SomeVariable b) toplevel

    resultEntries :: [Entry (abt '[])]
    resultEntries = toplevel ++ loop available (init ++ topvars)

    loop :: VarSet HakaruProxy -> [SomeVariable HakaruProxy] -> [Entry (abt '[])]
    loop avail [] = []
    loop avail (var@(SomeVariable v) : xs)
      | memberVarSet v avail = loop avail xs
      | otherwise            = new ++ loop avail' (vars ++ xs)
      where
        avail' = insertVarSet v avail
        vars   = M.mapMaybe (\Entry{binding=b} -> fmap SomeVariable b) new
        new    = [ e | e@Entry{varDependencies=d} <- entries
                     , memberVarSet v d
                     , varSubSet d avail' ]

-- Let forms should not kill bindings, since we are going to float the rhs of
-- all let expressions. The remaining binding forms are what decide when
-- expressions are removed from the expression pool.
hoistTerm
  :: forall (a :: Hakaru) (abt :: [Hakaru] -> Hakaru -> *) . (ABT Term abt)
  => Term abt a
  -> HoistM abt (abt '[] a)
hoistTerm (Let_ :$ rhs :* body :* End) = do
  rhs' <- hoist' rhs
  caseBind body $ \ v body' -> do
    tell [Entry (freeVars rhs') rhs' (Just v)]
    (body'', bindings) <- isolateBinder v (hoist' body')
    tell [Entry (freeVars body'') body' Nothing]
    available <- ask
    return body''

hoistTerm term = do
  result <- syn <$> traverse21 hoist' term
  tell [Entry (freeVars result) result Nothing]
  return result

