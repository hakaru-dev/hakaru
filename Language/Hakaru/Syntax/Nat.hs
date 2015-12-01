-- TODO: move this somewhere else, like "Language.Hakaru.Types"
-- TODO: merge with the Posta version. Release them as a standalone package?
{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.27
-- |
-- Module      :  Language.Hakaru.Syntax.Nat
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  Haskell98 + CPP
--
-- A data type for natural numbers (aka non-negative integers).
----------------------------------------------------------------
module Language.Hakaru.Syntax.Nat
    ( Nat()
    , fromNat
    , toNat
    , unsafeNat
    , MaxNat(..)
    ) where

#if __GLASGOW_HASKELL__ < 710
import Data.Monoid (Monoid(..))
#endif

----------------------------------------------------------------
----------------------------------------------------------------
-- | Natural numbers, with fixed-width à la 'Int'. N.B., the 'Num'
-- instance will throw errors on subtraction, negation, and
-- 'fromInteger' when the result is not a natural number.
newtype Nat = Nat Int
    deriving (Eq, Ord, Show)

-- TODO: should we define our own Show instance, in order to just
-- show the Int itself, relying on our 'fromInteger' definition to
-- preserve cut&paste-ability? If so, then we should ensure that
-- the Read instance is optional in whether the \"Nat\" is there
-- or not.

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

instance Enum Nat where
    succ (Nat i) = if i /= maxBound then Nat (i+1) else error _errmsg_succ
    pred (Nat i) = if i /= 0        then Nat (i-1) else error _errmsg_pred
    toEnum n     = if n >= 0        then Nat n     else error _errmsg_toEnum
    fromEnum (Nat i) = i

    enumFrom       (Nat i)                 = map Nat (enumFrom       i)
    enumFromThen   (Nat i) (Nat j)         = map Nat (enumFromThen   i j)
    enumFromTo     (Nat i)         (Nat k) = map Nat (enumFromTo     i   k)
    enumFromThenTo (Nat i) (Nat j) (Nat k) = map Nat (enumFromThenTo i j k)
    {-# INLINE succ #-}
    {-# INLINE pred #-}
    {-# INLINE toEnum #-}
    {-# INLINE fromEnum #-}
    {-# INLINE enumFrom #-}
    {-# INLINE enumFromThen #-}
    {-# INLINE enumFromTo #-}
    {-# INLINE enumFromThenTo #-}

instance Real Nat where
    toRational (Nat i) = toRational i
    {-# INLINE toRational #-}

instance Integral Nat where
    quot    (Nat i) (Nat j) = Nat (quot i j)
    rem     (Nat i) (Nat j) = Nat (rem  i j)
    quotRem (Nat i) (Nat j) = case quotRem i j of (q,r) -> (Nat q, Nat r)
    div    = quot
    mod    = rem
    divMod = quotRem
    toInteger (Nat i) = toInteger i
    {-# INLINE quot #-}
    {-# INLINE rem #-}
    {-# INLINE div #-}
    {-# INLINE mod #-}
    {-# INLINE quotRem #-}
    {-# INLINE divMod #-}
    {-# INLINE toInteger #-}


----------------------------------------------------------------
newtype MaxNat = MaxNat { unMaxNat :: Nat }

instance Monoid MaxNat where
    mempty                        = MaxNat 0
    mappend (MaxNat m) (MaxNat n) = MaxNat (max m n)


----------------------------------------------------------------
_errmsg_unsafeNat, _errmsg_subtraction, _errmsg_negate, _errmsg_fromInteger, _errmsg_succ, _errmsg_pred, _errmsg_toEnum
    :: String
_errmsg_unsafeNat   = "unsafeNat: negative input"
_errmsg_subtraction = "(-)@Nat: Num is a bad abstraction"
_errmsg_negate      = "negate@Nat: Num is a bad abstraction"
_errmsg_fromInteger = "fromInteger@Nat: Num is a bad abstraction"
_errmsg_succ        = "succ@Nat: No successor of the maxBound"
_errmsg_pred        = "pred@Nat: No predecessor of zero"
_errmsg_toEnum      = "toEnum@Nat: negative input"
{-# NOINLINE _errmsg_unsafeNat #-}
{-# NOINLINE _errmsg_subtraction #-}
{-# NOINLINE _errmsg_negate #-}
{-# NOINLINE _errmsg_fromInteger #-}
{-# NOINLINE _errmsg_succ #-}
{-# NOINLINE _errmsg_pred #-}
{-# NOINLINE _errmsg_toEnum #-}

----------------------------------------------------------------
----------------------------------------------------------- fin.
