-- TODO: move this somewhere else, like "Language.Hakaru.IClasses"
{-# LANGUAGE Rank2Types, PolyKinds #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.06.26
-- |
-- Module      :  Language.Hakaru.Syntax.IClasses
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  Rank2Types + PolyKinds
--
-- A collection of classes generalizing standard classes in order
-- to support indexed types.
--
-- TODO: DeriveDataTypeable for all our newtypes?
----------------------------------------------------------------
module Language.Hakaru.Syntax.IClasses
    ( Lift1(..)
    , Show1(..), shows1, showList1, Showable1(..)
    {- TODO: as necessary
    , Show2(..), Showable2(..)
    , Eq1(..)
    , Eq2(..)
    -}
    , Functor1(..)
    , Foldable1(..)
    ) where


----------------------------------------------------------------
-- | Any unindexed type can be lifted to be (trivially) @k@-indexed.
newtype Lift1 (a :: *) (i :: k) =
    Lift1 { unLift1 :: a }

----------------------------------------------------------------
-- TODO: cf., <http://hackage.haskell.org/package/abt-0.1.1.0>
-- | Uniform variant of Show for @k@-indexed types. This differs
-- from @transformers:@'Data.Functor.Classes.Show1' in being
-- polykinded, like it ought to be.
--
-- Alas, I don't think there's any way to derive instances the way
-- we can derive for 'Show'.
class Show1 (a :: k -> *) where
    {-# MINIMAL showsPrec1 | show1 #-}

    showsPrec1 :: Int -> a i -> ShowS
    showsPrec1 _ x s = show1 x ++ s

    show1 :: a i -> String
    show1 x = shows1 x ""

shows1 :: (Show1 a) => a i -> ShowS
shows1 =  showsPrec1 0

showList1 :: Show1 a => [a i] -> ShowS
showList1 []     s = "[]" ++ s
showList1 (x:xs) s = '[' : shows1 x (showl xs)
    where
    showl []     = ']' : s
    showl (y:ys) = ',' : shows1 y (showl ys)

{-
-- BUG: these require (Show (i::k)) in the class definition of Show1
instance Show1 Maybe where
    showsPrec1 = showsPrec
    show1      = show

instance Show1 [] where
    showsPrec1 = showsPrec
    show1      = show

instance Show1 ((,) a) where
    showsPrec1 = showsPrec
    show1      = show

instance Show1 (Either a) where
    showsPrec1 = showsPrec
    show1      = show
-}

instance Show a => Show1 (Lift1 a) where
    showsPrec1 p (Lift1 x) = showsPrec p x
    show1        (Lift1 x) = show x


-- | Every 'Show1' instance gives rise to the 'Show' instance we
-- wanted all along.
newtype Showable1 (a :: k -> *) (i :: k) =
    Showable1 { unShowable1 :: a i }

instance Show1 a => Show (Showable1 a i) where
    showsPrec p (Showable1 x) = showsPrec1 p x
    show        (Showable1 x) = show1 x

----------------------------------------------------------------
----------------------------------------------------------------
-- | A functor on the category of @k@-indexed types.
--
-- Alas, I don't think there's any way to derive instances the way
-- we can derive for 'Functor'.
class Functor1 (f :: (k -> *) -> k -> *) where
    fmap1 :: (forall i. a i -> b i) -> f a j -> f b j
    -- (<$1) :: (forall i. a i) -> f b j -> f a j


----------------------------------------------------------------
-- TODO: in theory we could define some Monoid1 class to avoid the
-- explicit dependency on Lift1 in fold1's type. But we'd need that
-- Monoid1 class to have some sort of notion of combining things
-- at different indices...

-- | A foldable functor on the category of @k@-indexed types.
--
-- Alas, I don't think there's any way to derive instances the way
-- we can derive for 'Foldable'.
class Functor1 f => Foldable1 (f :: (k -> *) -> k -> *) where
    {-# MINIMAL fold1 | foldMap1 #-}

    fold1 :: (Monoid m) => f (Lift1 m) i -> m
    fold1 = foldMap1 unLift1

    foldMap1 :: (Monoid m) => (forall i. a i -> m) -> f a j -> m
    foldMap1 f = fold1 . fmap1 (Lift1 . f)

----------------------------------------------------------------
----------------------------------------------------------- fin.
