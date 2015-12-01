-- TODO: move this somewhere else, like "Language.Hakaru.Types"
-- TODO: merge with the Posta version. Release them as a standalone package?
{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.12.01
-- |
-- Module      :  Language.Hakaru.Syntax.Natural
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  Haskell98 + CPP
--
-- A data type for natural numbers (aka non-negative integers).
----------------------------------------------------------------
module Language.Hakaru.Syntax.Natural
    ( Natural()
    , fromNatural
    , toNatural
    , unsafeNatural
    , MaxNatural(..)
    , NonNegativeRational
    , fromNonNegativeRational
    , toNonNegativeRational
    , unsafeNonNegativeRational
    ) where

#if __GLASGOW_HASKELL__ < 710
import Data.Monoid (Monoid(..))
#endif
import Data.Ratio

----------------------------------------------------------------
----------------------------------------------------------------
-- | Natural numbers, with unbounded-width à la 'Integer'. N.B.,
-- the 'Num' instance will throw errors on subtraction, negation,
-- and 'fromInteger' when the result is not a natural number.
newtype Natural = Natural Integer
    deriving (Eq, Ord, Show)

-- TODO: should we define our own Show instance, in order to just
-- show the Integer itself, relying on our 'fromInteger' definition
-- to preserve cut&paste-ability? If so, then we should ensure that
-- the Read instance is optional in whether the \"Natural\" is there
-- or not.

-- N.B., we cannot derive Read, since that would inject invalid numbers!
instance Read Natural where
    readsPrec d =
        readParen (d > 10) $ \s0 -> do
            ("Natural", s1) <- lex s0
            (i,         s2) <- readsPrec 11 s1
            maybe [] (\n -> [(n,s2)]) (toNatural i)


-- | Safely convert a natural number to an integer.
fromNatural :: Natural -> Integer
fromNatural (Natural i) = i
{-# INLINE fromNatural #-}


-- | Safely convert an integer to a natural number. Returns @Nothing@
-- if the integer is negative.
toNatural :: Integer -> Maybe Natural
toNatural x
    | x < 0     = Nothing
    | otherwise = Just (Natural x)
{-# INLINE toNatural #-}


-- | Unsafely convert an integer to a natural number. Throws an
-- error if the integer is negative.
unsafeNatural :: Integer -> Natural
unsafeNatural x
    | x < 0     = error _errmsg_unsafeNatural
    | otherwise = Natural x
{-# INLINE unsafeNatural #-}


instance Num Natural where
    Natural i + Natural j   = Natural (i + j)
    Natural i * Natural j   = Natural (i * j)
    Natural i - Natural j
        | i >= j    = Natural (i - j)
        | otherwise = error _errmsg_subtraction
    negate _        = error _errmsg_negate
    abs n           = n
    signum _        = Natural 1
    fromInteger i
        | i >= 0 && i >= 0 = Natural i
        | otherwise = error _errmsg_fromInteger
    {-# INLINE (+) #-}
    {-# INLINE (*) #-}
    {-# INLINE (-) #-}
    {-# INLINE negate #-}
    {-# INLINE abs #-}
    {-# INLINE signum #-}
    {-# INLINE fromInteger #-}

instance Enum Natural where
    succ (Natural i) = Natural (i+1)
    pred (Natural i)
        | i /= 0     = Natural (i-1)
        | otherwise  = error _errmsg_pred
    toEnum n
        | n >= 0     = Natural (toInteger n)
        | otherwise  = error _errmsg_toEnum
    fromEnum (Natural i) = fromEnum i

    enumFrom       (Natural i)             = map Natural (enumFrom i)
    enumFromThen   (Natural i) (Natural j) = map Natural (enumFromThen i j)
    enumFromTo     (Natural i) (Natural k) = map Natural (enumFromTo i k)
    enumFromThenTo (Natural i) (Natural j) (Natural k) =
        map Natural (enumFromThenTo i j k)
    {-# INLINE succ #-}
    {-# INLINE pred #-}
    {-# INLINE toEnum #-}
    {-# INLINE fromEnum #-}
    {-# INLINE enumFrom #-}
    {-# INLINE enumFromThen #-}
    {-# INLINE enumFromTo #-}
    {-# INLINE enumFromThenTo #-}

instance Real Natural where
    toRational (Natural i) = toRational i
    {-# INLINE toRational #-}

instance Integral Natural where
    quot    (Natural i) (Natural j) = Natural (quot i j)
    rem     (Natural i) (Natural j) = Natural (rem  i j)
    quotRem (Natural i) (Natural j) =
        case quotRem i j of
        (q,r) -> (Natural q, Natural r)
    div    = quot
    mod    = rem
    divMod = quotRem
    toInteger (Natural i) = i
    {-# INLINE quot #-}
    {-# INLINE rem #-}
    {-# INLINE div #-}
    {-# INLINE mod #-}
    {-# INLINE quotRem #-}
    {-# INLINE divMod #-}
    {-# INLINE toInteger #-}


----------------------------------------------------------------
newtype MaxNatural = MaxNatural { unMaxNatural :: Natural }

instance Monoid MaxNatural where
    mempty                                = MaxNatural 0
    mappend (MaxNatural m) (MaxNatural n) = MaxNatural (max m n)


----------------------------------------------------------------
-- TODO: come up with a more succinct name...
type NonNegativeRational = Ratio Natural

-- | Safely convert a non-negative rational to a rational.
fromNonNegativeRational :: NonNegativeRational -> Rational
fromNonNegativeRational x =
    fromNatural (numerator x) % fromNatural (denominator x)
    -- TODO: can we use @(:%)@ directly?
{-# INLINE fromNonNegativeRational #-}


-- | Safely convert a rational to a non-negative rational. Returns
-- @Nothing@ if the argument is negative.
toNonNegativeRational :: Rational -> Maybe NonNegativeRational
toNonNegativeRational x = do
    n <- toNatural (numerator x)
    d <- toNatural (denominator x)
    return (n % d)
    -- TODO: can we use @(:%)@ directly?
{-# INLINE toNonNegativeRational #-}


-- | Unsafely convert a rational to a non-negative rational. Throws
-- an error if the argument is negative.
unsafeNonNegativeRational :: Rational -> NonNegativeRational
unsafeNonNegativeRational x =
    case toNonNegativeRational x of
    Just y  -> y
    Nothing -> error _errmsg_unsafeNonNegativeRational
{-# INLINE unsafeNonNegativeRational #-}


----------------------------------------------------------------
_errmsg_unsafeNatural, _errmsg_subtraction, _errmsg_negate, _errmsg_fromInteger, _errmsg_pred, _errmsg_toEnum, _errmsg_unsafeNonNegativeRational
    :: String
_errmsg_unsafeNatural = "unsafeNatural: negative input"
_errmsg_subtraction   = "(-)@Natural: Num is a bad abstraction"
_errmsg_negate        = "negate@Natural: Num is a bad abstraction"
_errmsg_fromInteger   = "fromInteger@Natural: Num is a bad abstraction"
_errmsg_pred          = "pred@Natural: No predecessor of zero"
_errmsg_toEnum        = "toEnum@Natural: negative input"
_errmsg_unsafeNonNegativeRational = "unsafeNonNegativeRational: negative input"
{-# NOINLINE _errmsg_unsafeNatural #-}
{-# NOINLINE _errmsg_subtraction #-}
{-# NOINLINE _errmsg_negate #-}
{-# NOINLINE _errmsg_fromInteger #-}
{-# NOINLINE _errmsg_pred #-}
{-# NOINLINE _errmsg_toEnum #-}
{-# NOINLINE _errmsg_unsafeNonNegativeRational #-}

----------------------------------------------------------------
----------------------------------------------------------- fin.
