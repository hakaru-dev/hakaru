{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

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
-- Hoist expressions to the point where their data dependencies are met.
-- This pass duplicates *a lot* of work and relies on a the CSE and pruning
-- passes to cleanup the junk (most of which is trivial to do, but we don't know
-- what is junk until after CSE has occured).
--
-- NOTE: This pass assumes globally unique variable ids, as two subterms may
-- otherwise bind the same variable. Those variables would potentially shadow
-- eachother if hoisted upward to a common scope.
--
----------------------------------------------------------------
module Language.Hakaru.Syntax.Hoist where

import           Control.Monad.RWS
import           Data.Foldable                   (foldrM)
import           Data.List                       (groupBy, nub)
import qualified Data.Maybe                      as M
import           Data.Number.Nat
import           Data.Proxy                      (KProxy (..))
import           Prelude                         hiding (product, (+))

import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.AST.Eq
import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Syntax.Prelude  hiding (fst, maybe, not, (<$>),
                                                  (==))
import qualified Language.Hakaru.Syntax.Prelude  as P
import           Language.Hakaru.Syntax.TypeOf   (typeOf)
import           Language.Hakaru.Syntax.Variable (varSubSet)
import           Language.Hakaru.Types.DataKind
import           Language.Hakaru.Types.Sing      (Sing)

data Entry (abt :: Hakaru -> *)
  = forall (a :: Hakaru) . Entry
  { varDependencies :: !(VarSet (KindOf a))
  , expression      :: !(abt a)
  , binding         :: ![Variable a]
  }

instance Show (Entry a) where
  show (Entry deps _ bindings) = "Entry (" ++ show deps ++ ") (" ++ show bindings ++ ")"

type VarState    = Assocs Entry
type HakaruProxy = ('KProxy :: KProxy Hakaru)
type LiveSet     = VarSet HakaruProxy
type HakaruVar   = SomeVariable HakaruProxy

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
  = HoistM { runHoistM :: RWS LiveSet (EntrySet abt) Nat a }

deriving instance (ABT Term abt) => Functor (HoistM abt)
deriving instance (ABT Term abt) => Applicative (HoistM abt)
deriving instance (ABT Term abt) => Monad (HoistM abt)
deriving instance (ABT Term abt) => MonadState Nat (HoistM abt)
deriving instance (ABT Term abt) => MonadWriter (EntrySet abt) (HoistM abt)
deriving instance (ABT Term abt) => MonadReader LiveSet (HoistM abt)

newtype EntrySet (abt :: [Hakaru] -> Hakaru -> *)
  = EntrySet { entryList :: [Entry (abt '[])] }

-- This instance should behave more like a set, but the rest of the algorith
-- currently does not support that.
instance (ABT Term abt) => Monoid (EntrySet abt) where
  mempty = EntrySet []
  mappend (EntrySet xs) (EntrySet ys) =
     EntrySet $ concat $ map uniquify $ groupBy equal (xs ++ ys)
    where
      uniquify :: [Entry (abt '[])] -> [Entry (abt '[])]
      uniquify []  = []
      uniquify [x] = [x]
      uniquify xs  = [foldl1 join xs]

      join :: Entry (abt '[]) -> Entry (abt '[]) -> Entry (abt '[])
      join (Entry d e b1) (Entry _ e' b2) =
        case jmEq1 (typeOf e) (typeOf e') of
          Just Refl -> Entry d e $ nub (b1 ++ b2)
          Nothing   -> error "cannot mappend mismatched entries"

      equal :: Entry (abt '[]) -> Entry (abt '[]) -> Bool
      equal Entry{expression=e1} Entry{expression=e2} =
        case jmEq1 (typeOf e1) (typeOf e2) of
          Nothing   -> False
          Just Refl -> alphaEq e1 e2

singleEntry
  :: (ABT Term abt)
  => Variable a
  -> abt '[] a
  -> EntrySet abt
singleEntry v abt = EntrySet [Entry (freeVars abt) abt [v]]

freeEntry
  :: (ABT Term abt)
  => abt '[] a
  -> EntrySet abt
freeEntry abt = EntrySet [Entry (freeVars abt) abt []]

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

toplevelEntry
  :: Entry abt
  -> Bool
toplevelEntry Entry{varDependencies=d} = sizeVarSet d == 0

hoist
  :: (ABT Term abt)
  => abt '[] a
  -> abt '[] a
hoist abt = execHoistM (nextFreeOrBind abt) $ do
  (abt', entries) <- listen $ hoist' abt
  let toplevel = filter toplevelEntry $ entryList entries
      intro    = concatMap (\ Entry{binding=b} -> fmap SomeVariable b) toplevel
  wrapped <- introduceBindings emptyVarSet intro abt' entries
  wrapExpr wrapped toplevel

zapDependencies
  :: forall (a :: Hakaru) b abt
  .  (ABT Term abt)
  => Variable a
  -> HoistM abt b
  -> HoistM abt b
zapDependencies v = censor zap
  where
    zap :: EntrySet abt -> EntrySet abt
    zap = EntrySet
        . filter (\ Entry{varDependencies=d} -> not $ memberVarSet v d)
        . entryList

isolateBinder
  :: (ABT Term abt)
  => Variable (a :: Hakaru)
  -> HoistM abt b
  -> HoistM abt (b, EntrySet abt)
isolateBinder v m = zapDependencies v . local (insertVarSet v) $ listen m

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
    loop _  (Var v)    = return (var v)

    -- This case is not needed, but we can avoid performing the expensive work
    -- of calling introduceBindings in the case were we won't be performing any
    -- work.
    loop [] (Syn s)    = hoistTerm s
    loop xs (Syn s)    = do
      (term, entries) <- listen $ hoistTerm s
      available       <- ask
      introduceBindings available xs term entries

    loop xs (Bind v b) = do
      let xs' = SomeVariable v : xs
      b' <- zapDependencies v (loop xs' b)
      return (bind v b')

getBoundVar :: Entry x -> [HakaruVar]
getBoundVar Entry{binding=b} = fmap SomeVariable b

wrapExpr
  :: forall abt b . (ABT Term abt)
  => abt '[] b
  -> [Entry (abt '[])]
  -> HoistM abt (abt '[] b)
wrapExpr = foldrM wrap
  where
    mklet e b v = syn (Let_ :$ e :* bind v b :* End)

    wrap :: Entry (abt '[]) -> abt '[] b ->  HoistM abt (abt '[] b)
    wrap Entry{expression=e,binding=b} acc =
      case b of
        [] -> mklet e acc <$> newVar (typeOf e)
        _  -> return $ foldr (\v acc' -> mklet e acc' v) acc b

introduceBindings
  :: forall (a :: Hakaru) abt
  .  (ABT Term abt)
  => VarSet HakaruProxy
  -> [SomeVariable HakaruProxy]
  -> abt '[] a
  -> EntrySet abt
  -> HoistM abt (abt '[] a)
introduceBindings liveVars newVars body (EntrySet entries) =
  wrapExpr body resultEntries
  where
    resultEntries :: [Entry (abt '[])]
    resultEntries = loop liveVars newVars

    loop :: LiveSet -> [HakaruVar] -> [Entry (abt '[])]
    loop _    [] = []
    loop live (SomeVariable v : xs) = introduced ++ loop live' (xs ++ vars)
      where
        live'      = insertVarSet v live
        vars       = concatMap getBoundVar introduced
        introduced = [e | e@Entry{varDependencies=deps} <- entries
                        , memberVarSet v deps
                        , varSubSet deps live' ]

-- Contrary to the other binding forms, let expressions are killed by the
-- hoisting pass. Their RHSs are floated upward in the AST and re-introduced
-- where their data dependencies are fulfilled. Thus, the result of hoisting
-- a let expression is just the hoisted body.
hoistTerm
  :: forall (a :: Hakaru) (abt :: [Hakaru] -> Hakaru -> *) . (ABT Term abt)
  => Term abt a
  -> HoistM abt (abt '[] a)
hoistTerm (Let_ :$ rhs :* body :* End) =
  caseBind body $ \ v body' -> do
    rhs' <- hoist' rhs
    tell $ singleEntry v rhs'
    local (insertVarSet v) (hoist' body')

hoistTerm term = do
  result <- syn <$> traverse21 hoist' term
  tell $ freeEntry result
  return result

