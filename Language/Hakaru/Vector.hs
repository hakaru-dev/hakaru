{-# LANGUAGE MultiParamTypeClasses, TypeFamilies, FlexibleInstances,
             ConstraintKinds, DataKinds, Rank2Types, ScopedTypeVariables #-}

module Language.Hakaru.Vector (Nat(..), Repeat, Vector(..)) where

import Prelude hiding (Real)
import qualified Control.Applicative as A
import Language.Hakaru.Syntax
import Language.Hakaru.Sample (Sample(unSample))

infixl 4 <*>, <$>

data Nat = I | S Nat deriving (Eq, Ord, Show, Read)

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
  toNestedPair    :: Base repr => Repeat (Length a as) (repr a) -> repr (a, as)
  fromNestedPair  :: Base repr => repr (a, as) ->
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
