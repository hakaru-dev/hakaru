-- TODO: move this somewhere else, like "Language.Hakaru.Types"
-- TODO: merge with the Posta version. Release them as a standalone package?
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.06.26
-- |
-- Module      :  Language.Hakaru.Syntax.Nat
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  Haskell98
--
-- A data type for natural numbers (aka non-negative integers).
----------------------------------------------------------------
module Language.Hakaru.Syntax.Nat
    ( Nat()
    , fromNat
    , toNat
    , unsafeNat
    ) where

----------------------------------------------------------------
-- | Natural numbers, with fixed-width à la 'Int'. N.B., the 'Num'
-- instance will throw errors on subtraction, negation, and
-- 'fromInteger' when the result is not a natural number.
newtype Nat = Nat Int
    deriving (Eq, Ord, Show)

-- N.B., we cannot derive Read, since that would inject invalid numbers!
instance Read Nat where
    readsPrec d =
        readParen (d > 10) $ \s0 -> do
            ("Nat", s1) <- lex s0
            (i,     s2) <- readsPrec 11 s1
            maybe [] (\n -> [(n,s2)]) (toNat i)


-- | Safely convert a natural number to an integer.
fromNat :: Nat -> Int
fromNat (Nat i) = i
{-# INLINE fromNat #-}


-- | Safely convert an integer to a natural number. Returns @Nothing@
-- if the integer is negative.
toNat :: Int -> Maybe Nat
toNat x
    | x < 0     = Nothing
    | otherwise = Just (Nat x)
{-# INLINE toNat #-}


-- | Unsafely convert an integer to a natural number. Throws an
-- error if the integer is negative.
unsafeNat :: Int -> Nat
unsafeNat x
    | x < 0     = error _errmsg_unsafeNat
    | otherwise = Nat x
{-# INLINE unsafeNat #-}


instance Num Nat where
    Nat i + Nat j   = Nat (i + j)
    Nat i * Nat j   = Nat (i * j)
    Nat i - Nat j
        | i >= j    = Nat (i - j)
        | otherwise = error _errmsg_subtraction
    negate _        = error _errmsg_negate
    abs n           = n
    signum _        = Nat 1
    fromInteger i
        | i >= 0 && n >= 0 = Nat n
        | otherwise = error _errmsg_fromInteger
        where
        n :: Int
        n = fromInteger i
    {-# INLINE (+) #-}
    {-# INLINE (*) #-}
    {-# INLINE (-) #-}
    {-# INLINE negate #-}
    {-# INLINE abs #-}
    {-# INLINE signum #-}
    {-# INLINE fromInteger #-}

_errmsg_unsafeNat, _errmsg_subtraction, _errmsg_negate, _errmsg_fromInteger
    :: String
_errmsg_unsafeNat   = "unsafeNat: negative input"
_errmsg_subtraction = "(-)@Nat: Num is a bad abstraction"
_errmsg_negate      = "negate@Nat: Num is a bad abstraction"
_errmsg_fromInteger = "fromInteger@Nat: Num is a bad abstraction"
{-# NOINLINE _errmsg_unsafeNat #-}
{-# NOINLINE _errmsg_subtraction #-}
{-# NOINLINE _errmsg_negate #-}
{-# NOINLINE _errmsg_fromInteger #-}

----------------------------------------------------------------
----------------------------------------------------------- fin.
