{-# LANGUAGE MultiParamTypeClasses, TypeFamilies,
             FlexibleInstances, FlexibleContexts,
             ConstraintKinds, DataKinds, Rank2Types, ScopedTypeVariables #-}

module Language.Hakaru.Vector (Nat(..), Repeat, Vector(..),
        sequenceA, mapM, sequence, mapAccum, iota, mapC) where

import Prelude hiding (Real, mapM, sequence)
import qualified Control.Applicative as A
import Language.Hakaru.Syntax
import Language.Hakaru.Sample (Sample(unSample))
import Control.Applicative (WrappedMonad(..))
import Control.Monad.State (runState, state)
import Control.Monad.Cont (runCont, cont)

infixl 4 <*>, <$>

data Nat = I | S Nat deriving (Eq, Ord, Show, Read)

type TenPlus n = S (S (S (S (S (S (S (S (S (S n)))))))))
type HundredPlus n = TenPlus (TenPlus (TenPlus (TenPlus (TenPlus
                    (TenPlus (TenPlus (TenPlus (TenPlus (TenPlus n)))))))))

type Length a as = Length' as
type family   Length' as :: Nat
type instance Length' ()      = I
type instance Length' (a, as) = S (Length' as)

type Repeat n a = (a, Repeat' n a)
type family   Repeat' (n :: Nat) a
type instance Repeat' I     a = ()
type instance Repeat' (S n) a = (a, Repeat' n a)

type SameLength as b = Length' as ~ Length' (Repeat' (Length' as) b)

class (as ~ Repeat' (Length' as) a) => Vector a as where
  pure            :: a -> (a, as)
  (<*>)           :: (SameLength as (a -> b), SameLength as b) =>
                     Repeat (Length a as) (a -> b) ->
                     (a, as) ->
                     Repeat (Length a as) b
  (<$>)           :: (SameLength as b) =>
                     (a -> b) ->
                     (a, as) ->
                     Repeat (Length a as) b
  traverse        :: (A.Applicative f, SameLength as b) =>
                     (a -> f b) -> (a, as) -> f (Repeat (Length a as) b)
  toNestedPair    :: (SameLength as (repr a), Base repr) =>
                     Repeat (Length a as) (repr a) -> repr (a, as)
  fromNestedPair  :: (SameLength as (repr a), Base repr) => repr (a, as) ->
                     (Repeat (Length a as) (repr a) -> repr w) -> repr w
  toList          :: (a, as) -> [a]
  fromList        :: [a] -> (a, as)

instance Vector a () where
  pure a                        = (a, ())
  (ab, ()) <*> (a, ())          = (ab a, ())
  ab <$> (a, ())                = (ab a, ())
  traverse f (a, ())            = (\b -> (b,())) A.<$> f a
  toNestedPair (a, ())          = pair a unit
  fromNestedPair repr_a_unit k  = unpair repr_a_unit (\a _ -> k (a,()))
  toList (a, ())                = [a]
  fromList (a : _)              = (a, ())

instance (Vector a as) => Vector a (a, as) where
  pure a                        = (a, pure a)
  (ab, abs) <*> (a, as)         = (ab a, abs <*> as)
  ab <$> (a, as)                = (ab a, ab <$> as)
  traverse f (a, as)            = (,) A.<$> f a A.<*> traverse f as
  toNestedPair (a, as)          = pair a (toNestedPair as)
  fromNestedPair repr_a_as k    = unpair repr_a_as (\a repr_as ->
                                  fromNestedPair repr_as (\as -> k (a,as)))
  toList (a, as)                = a : toList as
  fromList (a : as)             = (a, fromList as)

sequenceA :: (A.Applicative f, Vector (f a) fas, SameLength fas a) =>
             (f a, fas) -> f (Repeat (Length (f a) fas) a)
sequenceA = traverse id

mapM :: (Vector a as, Monad m, SameLength as b) =>
        (a -> m b) -> (a, as) -> m (Repeat (Length a as) b)
mapM f = unwrapMonad . traverse (WrapMonad . f)

sequence :: (Monad m, Vector (m a) mas, SameLength mas a) =>
            (m a, mas) -> m (Repeat (Length (m a) mas) a)
sequence = mapM id

mapAccum :: (Vector x xs, SameLength xs y) =>
            (acc -> x -> (acc, y)) -> acc -> (x, xs) ->
            (acc, Repeat (Length x xs) y)
mapAccum f acc xs = exch (runState (mapM f' xs) acc)
  where exch (a,b) = (b,a)
        f' = state . curry (exch . uncurry f . exch)

iota :: (Enum y, Vector () xs, SameLength xs y) =>
        y -> (y, Repeat (Length () xs) y)
iota start = snd (mapAccum (\x () -> (succ x, x)) start (pure ()))

mapC :: (Vector a as, SameLength as b) =>
        (a -> (b -> w) -> w) -> (a, as) -> (Repeat (Length a as) b -> w) -> w
mapC f = runCont . mapM (cont . f)

main :: IO ()
main = do
  print (unSample (toNestedPair ((+) <$>
                                 fromList [1,2,3] <*>
                                 fromList [100,200,300])
                   :: Sample IO (Repeat (S (S I)) Real)))
       -- (101.0,(202.0,(303.0,())))
  print (unSample (fromNestedPair (pair 3 (pair 5 (pair 7 unit)))
                                  (\(a,(b,(c,()))) -> a + b + c)
                   :: Sample IO Real))
       -- 15.0
  print (iota 10 :: Repeat (HundredPlus I) Int)
