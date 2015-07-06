-- TODO: move this somewhere else, like "Language.Hakaru.IClasses"
{-# LANGUAGE CPP, Rank2Types, PolyKinds, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.07.01
-- |
-- Module      :  Language.Hakaru.Syntax.IClasses
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  CPP + Rank2Types + PolyKinds + ScopedTypeVariables
--
-- A collection of classes generalizing standard classes in order
-- to support indexed types.
--
-- TODO: DeriveDataTypeable for all our newtypes?
----------------------------------------------------------------
module Language.Hakaru.Syntax.IClasses
    ( Lift1(..)
    -- * Showing indexed types
    , Show1(..), shows1, showList1
    -- ** some helpers for implementing the instances
    , showParen_0
    , showParen_1
    , showParen_01
    , showParen_11
    , showParen_111
    -- * Equality
    , Eq1(..)
    -- * Generalized abstract nonsense
    , Functor1(..)
    , Fix1(..), cata1, ana1, hylo1
    , Foldable1(..)
    ) where

#if __GLASGOW_HASKELL__ < 710
import Data.Monoid
#endif

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

----------------------------------------------------------------
showParen_0 :: Show a => Int -> String -> a -> ShowS
showParen_0 p s e =
    showParen (p > 9)
        ( showString s
        . showString " "
        . showsPrec 11 e
        )

showParen_1 :: Show1 a => Int -> String -> a i -> ShowS
showParen_1 p s e =
    showParen (p > 9)
        ( showString s
        . showString " "
        . showsPrec1 11 e
        )

showParen_01 :: (Show b, Show1 a) => Int -> String -> b -> a i -> ShowS
showParen_01 p s e1 e2 =
    showParen (p > 9)
        ( showString s
        . showString " "
        . showsPrec  11 e1
        . showString " "
        . showsPrec1 11 e2
        )

showParen_11 :: (Show1 a, Show1 b) => Int -> String -> a i -> b j -> ShowS
showParen_11 p s e1 e2 =
    showParen (p > 9)
        ( showString s
        . showString " "
        . showsPrec1 11 e1
        . showString " "
        . showsPrec1 11 e2
        )

showParen_111
    :: (Show1 a, Show1 b, Show1 c)
    => Int -> String -> a i -> b j -> c k -> ShowS
showParen_111 p s e1 e2 e3 =
    showParen (p > 9)
        ( showString s
        . showString " "
        . showsPrec1 11 e1
        . showString " "
        . showsPrec1 11 e2
        . showString " "
        . showsPrec1 11 e3
        )

----------------------------------------------------------------
----------------------------------------------------------------
-- | Uniform variant of 'Eq' for @k@-indexed types. N.B., this
-- function returns term equality. We assume the indices match up.
--
-- Alas, I don't think there's any way to derive instances the way
-- we can derive for 'Eq'.
class Eq1 (a :: k -> *) where
    eq1 :: a i -> a i -> Bool

instance Eq a => Eq1 (Lift1 a) where
    eq1 (Lift1 a) (Lift1 b) = a == b


----------------------------------------------------------------
----------------------------------------------------------------
-- | A functor on the category of @k@-indexed types.
--
-- Alas, I don't think there's any way to derive instances the way
-- we can derive for 'Functor'.
class Functor1 (f :: (k -> *) -> k -> *) where
    fmap1 :: (forall i. a i -> b i) -> f a j -> f b j


newtype Fix1 (f :: (k -> *) -> k -> *) (i :: k) =
    Fix1 { unFix1 :: f (Fix1 f) i }

cata1
    :: forall f a j
    .  (Functor1 f)
    => (forall i. f a i -> a i)
    -> Fix1 f j -> a j
cata1 alg = go
    where
    go :: forall j'. Fix1 f j' -> a j'
    go = alg . fmap1 go . unFix1

ana1
    :: forall f a j
    .  (Functor1 f)
    => (forall i. a i -> f a i)
    -> a j -> Fix1 f j
ana1 coalg = go
    where
    go :: forall j'. a j' -> Fix1 f j'
    go = Fix1 . fmap1 go . coalg

hylo1
    :: forall f a b j
    .  (Functor1 f)
    => (forall i. a i -> f a i)
    -> (forall i. f b i -> b i)
    -> a j
    -> b j
hylo1 coalg alg = go
    where
    go :: forall j'. a j' -> b j'
    go = alg . fmap1 go . coalg

-- TODO: a tracing evaluator: <http://www.timphilipwilliams.com/posts/2013-01-16-fixing-gadts.html>


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

-- TODO: standard Foldable wrappers 'and1', 'or1', 'all1', 'any1',...

----------------------------------------------------------------
----------------------------------------------------------- fin.
