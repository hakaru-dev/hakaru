-- TODO: move this somewhere else, like "Language.Hakaru.Types"
module Language.Hakaru.Syntax.Nat
    ( Nat()
    , fromNat
    , toNat
    , unsafeNat
    ) where

----------------------------------------------------------------
-- | A type for natural numbers (aka non-negative integers).
newtype Nat = Nat Int
    deriving (Eq, Ord, Read, Show)

fromNat :: Nat -> Int
fromNat (Nat i) = i
{-# INLINE fromNat #-}

toNat :: Int -> Maybe Nat
toNat x
    | x < 0     = Nothing
    | otherwise = Just (Nat x)
{-# INLINE toNat #-}

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
        n = fromInteger i
    {-# INLINE (+) #-}
    {-# INLINE (*) #-}
    {-# INLINE (-) #-}
    {-# INLINE negate #-}
    {-# INLINE abs #-}
    {-# INLINE signum #-}
    {-# INLINE fromInteger #-}


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