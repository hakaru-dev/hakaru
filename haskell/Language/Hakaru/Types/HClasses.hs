{-# LANGUAGE CPP
           , GADTs
           , KindSignatures
           , DataKinds
           , PolyKinds
           , TypeFamilies
           , FlexibleContexts
           , FlexibleInstances
           , TypeSynonymInstances
           , StandaloneDeriving
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.12.15
-- |
-- Module      :  Language.Hakaru.Types.HClasses
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- A collection of type classes for encoding Hakaru's numeric hierarchy.
----------------------------------------------------------------
module Language.Hakaru.Types.HClasses
    (
    -- * Equality
      HEq(..)
    , HEq_(..)
    , sing_HEq
    , hEq_Sing

    -- * Ordering
    , HOrd(..)
    , hEq_HOrd
    , HOrd_(..)
    , sing_HOrd
    , hOrd_Sing

    -- * Semirings
    , HSemiring(..)
    , HSemiring_(..)
    , sing_HSemiring
    , hSemiring_Sing

    -- * Rings
    , HRing(..)
    , hSemiring_HRing
    , hSemiring_NonNegativeHRing
    , HRing_(..)
    , sing_HRing
    , hRing_Sing
    , sing_NonNegative

    -- * Fractional types
    , HFractional(..)
    , hSemiring_HFractional
    , HFractional_(..)
    , sing_HFractional
    , hFractional_Sing

    -- * Radical types
    , HRadical(..)
    , hSemiring_HRadical
    , HRadical_(..)
    , sing_HRadical
    , hRadical_Sing

   -- * Discrete types
    , HDiscrete(..)
    , HDiscrete_(..)
    , sing_HDiscrete
    , hDiscrete_Sing

    -- * Continuous types
    , HContinuous(..)
    , hFractional_HContinuous
    , hSemiring_HIntegralContinuous
    , HContinuous_(..)
    , sing_HContinuous
    , hContinuous_Sing
    , sing_HIntegral
    ) where

#if __GLASGOW_HASKELL__ < 710
import Data.Functor ((<$>))
#endif
import Control.Applicative ((<|>))
import Language.Hakaru.Syntax.IClasses (TypeEq(..), Eq1(..), JmEq1(..))
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing

----------------------------------------------------------------
-- | Concrete dictionaries for Hakaru types with decidable equality.
data HEq :: Hakaru -> * where
    HEq_Nat    :: HEq 'HNat
    HEq_Int    :: HEq 'HInt
    HEq_Prob   :: HEq 'HProb
    HEq_Real   :: HEq 'HReal
    HEq_Array  :: !(HEq a) -> HEq ('HArray a)
    HEq_Bool   :: HEq HBool
    HEq_Unit   :: HEq HUnit
    HEq_Pair   :: !(HEq a) -> !(HEq b) -> HEq (HPair   a b)
    HEq_Either :: !(HEq a) -> !(HEq b) -> HEq (HEither a b)

deriving instance Eq   (HEq a)
-- TODO: instance JmEq1 HEq
-- BUG: deriving instance Read (HEq a)
deriving instance Show (HEq a)

-- N.B., we do case analysis so that we don't need the class constraint!
sing_HEq :: HEq a -> Sing a
sing_HEq HEq_Nat          = SNat
sing_HEq HEq_Int          = SInt
sing_HEq HEq_Prob         = SProb
sing_HEq HEq_Real         = SReal
sing_HEq (HEq_Array  a)   = SArray  (sing_HEq a)
sing_HEq HEq_Bool         = sBool
sing_HEq HEq_Unit         = sUnit
sing_HEq (HEq_Pair   a b) = sPair   (sing_HEq a) (sing_HEq b)
sing_HEq (HEq_Either a b) = sEither (sing_HEq a) (sing_HEq b)

hEq_Sing :: Sing a -> Maybe (HEq a)
hEq_Sing SNat        = Just HEq_Nat
hEq_Sing SInt        = Just HEq_Int
hEq_Sing SProb       = Just HEq_Prob
hEq_Sing SReal       = Just HEq_Real
hEq_Sing (SArray a)  = HEq_Array <$> hEq_Sing a
hEq_Sing s           = (jmEq1 s sUnit  >>= \Refl -> Just HEq_Unit) <|>
                       (jmEq1 s sBool  >>= \Refl -> Just HEq_Bool)
{-
hEq_Sing (sPair   a b) = HEq_Pair <$> hEq_Sing a <*> hEq_Sing b
hEq_Sing (sEither a b) = HEq_Either <$> hEq_Sing a <*> hEq_Sing b
-}

-- | Haskell type class for automatic 'HEq' inference.
class    HEq_ (a :: Hakaru) where hEq :: HEq a
instance HEq_ 'HNat         where hEq = HEq_Nat 
instance HEq_ 'HInt         where hEq = HEq_Int 
instance HEq_ 'HProb        where hEq = HEq_Prob 
instance HEq_ 'HReal        where hEq = HEq_Real 
instance HEq_ HBool         where hEq = HEq_Bool 
instance HEq_ HUnit         where hEq = HEq_Unit 
instance (HEq_ a) => HEq_ ('HArray a) where
    hEq = HEq_Array hEq
instance (HEq_ a, HEq_ b) => HEq_ (HPair a b) where
    hEq = HEq_Pair hEq hEq
instance (HEq_ a, HEq_ b) => HEq_ (HEither a b) where
    hEq = HEq_Either hEq hEq


----------------------------------------------------------------
-- | Concrete dictionaries for Hakaru types with decidable total ordering.
data HOrd :: Hakaru -> * where
    HOrd_Nat    :: HOrd 'HNat
    HOrd_Int    :: HOrd 'HInt
    HOrd_Prob   :: HOrd 'HProb
    HOrd_Real   :: HOrd 'HReal
    HOrd_Array  :: !(HOrd a) -> HOrd ('HArray a)
    HOrd_Bool   :: HOrd HBool
    HOrd_Unit   :: HOrd HUnit
    HOrd_Pair   :: !(HOrd a) -> !(HOrd b) -> HOrd (HPair   a b)
    HOrd_Either :: !(HOrd a) -> !(HOrd b) -> HOrd (HEither a b)

deriving instance Eq   (HOrd a)
-- TODO: instance JmEq1 HOrd
-- BUG: deriving instance Read (HOrd a)
deriving instance Show (HOrd a)

sing_HOrd :: HOrd a -> Sing a
sing_HOrd HOrd_Nat          = SNat
sing_HOrd HOrd_Int          = SInt
sing_HOrd HOrd_Prob         = SProb
sing_HOrd HOrd_Real         = SReal
sing_HOrd (HOrd_Array  a)   = SArray  (sing_HOrd a)
sing_HOrd HOrd_Bool         = sBool
sing_HOrd HOrd_Unit         = sUnit
sing_HOrd (HOrd_Pair   a b) = sPair   (sing_HOrd a) (sing_HOrd b)
sing_HOrd (HOrd_Either a b) = sEither (sing_HOrd a) (sing_HOrd b)

hOrd_Sing :: Sing a -> Maybe (HOrd a)
hOrd_Sing SNat              = Just HOrd_Nat
hOrd_Sing SInt              = Just HOrd_Int
hOrd_Sing SProb             = Just HOrd_Prob
hOrd_Sing SReal             = Just HOrd_Real
hOrd_Sing (SArray a)        = HOrd_Array <$> hOrd_Sing a
hOrd_Sing _                 = Nothing

-- | Every 'HOrd' type is 'HEq'.
hEq_HOrd :: HOrd a -> HEq a
hEq_HOrd HOrd_Nat          = HEq_Nat
hEq_HOrd HOrd_Int          = HEq_Int
hEq_HOrd HOrd_Prob         = HEq_Prob
hEq_HOrd HOrd_Real         = HEq_Real
hEq_HOrd (HOrd_Array  a)   = HEq_Array  (hEq_HOrd a)
hEq_HOrd HOrd_Bool         = HEq_Bool
hEq_HOrd HOrd_Unit         = HEq_Unit
hEq_HOrd (HOrd_Pair   a b) = HEq_Pair   (hEq_HOrd a) (hEq_HOrd b)
hEq_HOrd (HOrd_Either a b) = HEq_Either (hEq_HOrd a) (hEq_HOrd b)

-- | Haskell type class for automatic 'HOrd' inference.
class    HEq_ a => HOrd_ (a :: Hakaru) where hOrd :: HOrd a
instance HOrd_ 'HNat                   where hOrd = HOrd_Nat 
instance HOrd_ 'HInt                   where hOrd = HOrd_Int 
instance HOrd_ 'HProb                  where hOrd = HOrd_Prob 
instance HOrd_ 'HReal                  where hOrd = HOrd_Real 
instance HOrd_ HBool                   where hOrd = HOrd_Bool 
instance HOrd_ HUnit                   where hOrd = HOrd_Unit 
instance (HOrd_ a) => HOrd_ ('HArray a) where
    hOrd = HOrd_Array hOrd
instance (HOrd_ a, HOrd_ b) => HOrd_ (HPair a b) where
    hOrd = HOrd_Pair hOrd hOrd
instance (HOrd_ a, HOrd_ b) => HOrd_ (HEither a b) where
    hOrd = HOrd_Either hOrd hOrd


-- TODO: class HPER (a :: Hakaru)
-- TODO: class HPartialOrder (a :: Hakaru)

----------------------------------------------------------------
-- | Concrete dictionaries for Hakaru types which are semirings.
-- N.B., even though these particular semirings are commutative,
-- we don't necessarily assume that.
data HSemiring :: Hakaru -> * where
    HSemiring_Nat  :: HSemiring 'HNat
    HSemiring_Int  :: HSemiring 'HInt
    HSemiring_Prob :: HSemiring 'HProb
    HSemiring_Real :: HSemiring 'HReal


instance Eq (HSemiring a) where -- This one could be derived...
    (==) = eq1
instance Eq1 HSemiring where
    eq1 x y = maybe False (const True) (jmEq1 x y)
instance JmEq1 HSemiring where
    jmEq1 HSemiring_Nat  HSemiring_Nat  = Just Refl
    jmEq1 HSemiring_Int  HSemiring_Int  = Just Refl
    jmEq1 HSemiring_Prob HSemiring_Prob = Just Refl
    jmEq1 HSemiring_Real HSemiring_Real = Just Refl
    jmEq1 _              _              = Nothing

-- BUG: deriving instance Read (HSemiring a)
deriving instance Show (HSemiring a)

sing_HSemiring :: HSemiring a -> Sing a
sing_HSemiring HSemiring_Nat  = SNat
sing_HSemiring HSemiring_Int  = SInt
sing_HSemiring HSemiring_Prob = SProb
sing_HSemiring HSemiring_Real = SReal

hSemiring_Sing :: Sing a -> Maybe (HSemiring a)
hSemiring_Sing SNat  = Just HSemiring_Nat 
hSemiring_Sing SInt  = Just HSemiring_Int 
hSemiring_Sing SProb = Just HSemiring_Prob
hSemiring_Sing SReal = Just HSemiring_Real
hSemiring_Sing _     = Nothing

-- | Haskell type class for automatic 'HSemiring' inference.
class    HSemiring_ (a :: Hakaru) where hSemiring :: HSemiring a
instance HSemiring_ 'HNat  where hSemiring = HSemiring_Nat 
instance HSemiring_ 'HInt  where hSemiring = HSemiring_Int 
instance HSemiring_ 'HProb where hSemiring = HSemiring_Prob 
instance HSemiring_ 'HReal where hSemiring = HSemiring_Real 


----------------------------------------------------------------
-- | Concrete dictionaries for Hakaru types which are rings. N.B.,
-- even though these particular rings are commutative, we don't
-- necessarily assume that.
data HRing :: Hakaru -> * where
    HRing_Int  :: HRing 'HInt
    HRing_Real :: HRing 'HReal


instance Eq (HRing a) where -- This one could be derived...
    (==) = eq1
instance Eq1 HRing where
    eq1 x y = maybe False (const True) (jmEq1 x y)
instance JmEq1 HRing where
    jmEq1 HRing_Int  HRing_Int  = Just Refl
    jmEq1 HRing_Real HRing_Real = Just Refl
    jmEq1 _          _          = Nothing

    
-- BUG: deriving instance Read (HRing a)

deriving instance Show (HRing a)

sing_HRing :: HRing a -> Sing a
sing_HRing HRing_Int  = SInt
sing_HRing HRing_Real = SReal

hRing_Sing :: Sing a -> Maybe (HRing a)
hRing_Sing SInt  = Just HRing_Int
hRing_Sing SReal = Just HRing_Real
hRing_Sing _     = Nothing

sing_NonNegative :: HRing a -> Sing (NonNegative a)
sing_NonNegative = sing_HSemiring . hSemiring_NonNegativeHRing

-- hNonNegative_Sing :: Sing (NonNegative a) -> Maybe (HRing a)

-- | Every 'HRing' is a 'HSemiring'.
hSemiring_HRing :: HRing a -> HSemiring a
hSemiring_HRing HRing_Int  = HSemiring_Int
hSemiring_HRing HRing_Real = HSemiring_Real

-- | The non-negative type of every 'HRing' is a 'HSemiring'.
hSemiring_NonNegativeHRing :: HRing a -> HSemiring (NonNegative a)
hSemiring_NonNegativeHRing HRing_Int  = HSemiring_Nat
hSemiring_NonNegativeHRing HRing_Real = HSemiring_Prob

-- | Haskell type class for automatic 'HRing' inference.
--
-- Every 'HRing' has an associated type for the semiring of its
-- non-negative elements. This type family captures two notions.
-- First, if we take the semiring and close it under negation\/subtraction
-- then we will generate this ring. Second, when we take the absolute
-- value of something in the ring we will get back something in the
-- non-negative semiring. For 'HInt' and 'HReal' these two notions
-- coincide; however for Complex and Vector types, the notions
-- diverge.
--
-- TODO: Can we somehow specify that the @HSemiring (NonNegative
-- a)@ semantics coincides with the @HSemiring a@ semantics? Or
-- should we just assume that?
class (HSemiring_ (NonNegative a), HSemiring_ a) => HRing_ (a :: Hakaru)
    where
    type NonNegative (a :: Hakaru) :: Hakaru
    hRing :: HRing a

instance HRing_ 'HInt where
    type NonNegative 'HInt = 'HNat
    hRing = HRing_Int

instance HRing_ 'HReal where
    type NonNegative 'HReal = 'HProb
    hRing = HRing_Real



----------------------------------------------------------------
-- N.B., We're assuming two-sided inverses here. That doesn't entail
-- commutativity, though it does strongly suggest it... (cf.,
-- Wedderburn's little theorem)
--
-- N.B., the (Nat,"+"=lcm,"*"=gcd) semiring is sometimes called
-- "the division semiring"
--
-- HACK: tracking the generating carriers here wouldn't be quite
-- right b/c we get more than just the (non-negative)rationals
-- generated from HNat/HInt! However, we should have some sort of
-- associated type so we can add rationals and non-negative
-- rationals...
--
-- TODO: associated type for non-zero elements. To guarantee the
-- safety of division\/recip? For now, we have Infinity, so it's
-- actually safe for these two types. But if we want to add the
-- rationals...
--
-- | Concrete dictionaries for Hakaru types which are division-semirings;
-- i.e., division-rings without negation. This is called a \"semifield\"
-- in ring theory, but should not be confused with the \"semifields\"
-- of geometry.
data HFractional :: Hakaru -> * where
    HFractional_Prob :: HFractional 'HProb
    HFractional_Real :: HFractional 'HReal


instance Eq (HFractional a) where -- This one could be derived...
    (==) = eq1
instance Eq1 HFractional where
    eq1 x y = maybe False (const True) (jmEq1 x y)
instance JmEq1 HFractional where
    jmEq1 HFractional_Prob HFractional_Prob = Just Refl
    jmEq1 HFractional_Real HFractional_Real = Just Refl
    jmEq1 _                _                = Nothing

-- BUG: deriving instance Read (HFractional a)
deriving instance Show (HFractional a)

sing_HFractional :: HFractional a -> Sing a
sing_HFractional HFractional_Prob = SProb
sing_HFractional HFractional_Real = SReal

hFractional_Sing :: Sing a -> Maybe (HFractional a)
hFractional_Sing SProb = Just HFractional_Prob
hFractional_Sing SReal = Just HFractional_Real
hFractional_Sing _     = Nothing

-- | Every 'HFractional' is a 'HSemiring'.
hSemiring_HFractional :: HFractional a -> HSemiring a
hSemiring_HFractional HFractional_Prob = HSemiring_Prob
hSemiring_HFractional HFractional_Real = HSemiring_Real

-- | Haskell type class for automatic 'HFractional' inference.
class (HSemiring_ a) => HFractional_ (a :: Hakaru) where
    hFractional :: HFractional a
instance HFractional_ 'HProb where hFractional = HFractional_Prob 
instance HFractional_ 'HReal where hFractional = HFractional_Real 


-- type HDivisionRing a = (HFractional a, HRing a)
-- type HField a = (HDivisionRing a, HCommutativeSemiring a)


----------------------------------------------------------------
-- Numbers formed by finitely many uses of integer addition,
-- subtraction, multiplication, division, and nat-roots are all
-- algebraic; however, N.B., not all algebraic numbers can be formed
-- this way (cf., Abel–Ruffini theorem)
-- TODO: ought we require HFractional rather than HSemiring?
-- TODO: any special associated type?
--
-- | Concrete dictionaries for semirings which are closed under all
-- 'HNat'-roots. This means it's closed under all positive rational
-- powers as well. (If the type happens to be 'HFractional', then
-- it's closed under /all/ rational powers.)
--
-- N.B., 'HReal' is not 'HRadical' because we do not have real-valued
-- roots for negative reals.
--
-- N.B., we assume not only that the type is surd-complete, but
-- also that it's still complete under the semiring operations.
-- Thus we have values like @sqrt 2 + sqrt 3@ which cannot be
-- expressed as a single root. Thus, in order to solve for zeros\/roots,
-- we'll need solutions to more general polynomials than just the
-- @x^n - a@ polynomials. However, the Galois groups of these are
-- all solvable, so this shouldn't be too bad.
data HRadical :: Hakaru -> * where
    HRadical_Prob :: HRadical 'HProb


instance Eq (HRadical a) where -- This one could be derived...
    (==) = eq1
instance Eq1 HRadical where
    eq1 x y = maybe False (const True) (jmEq1 x y)
instance JmEq1 HRadical where
    jmEq1 HRadical_Prob HRadical_Prob = Just Refl

-- BUG: deriving instance Read (HRadical a)
deriving instance Show (HRadical a)

sing_HRadical :: HRadical a -> Sing a
sing_HRadical HRadical_Prob = SProb

hRadical_Sing :: Sing a -> Maybe (HRadical a)
hRadical_Sing SProb = Just HRadical_Prob
hRadical_Sing _     = Nothing

-- | Every 'HRadical' is a 'HSemiring'.
hSemiring_HRadical :: HRadical a -> HSemiring a
hSemiring_HRadical HRadical_Prob = HSemiring_Prob

-- | Haskell type class for automatic 'HRadical' inference.
class (HSemiring_ a) => HRadical_ (a :: Hakaru) where
    hRadical :: HRadical a
instance HRadical_ 'HProb where hRadical = HRadical_Prob 


-- TODO: class (HDivisionRing a, HRadical a) => HAlgebraic a where...


-- | Concrete dictionaries for Hakaru types which are \"discrete\".
data HDiscrete :: Hakaru -> * where
    HDiscrete_Nat :: HDiscrete 'HNat
    HDiscrete_Int :: HDiscrete 'HInt

instance Eq (HDiscrete a) where -- This one could be derived...
    (==) = eq1
instance Eq1 HDiscrete where
    eq1 x y = maybe False (const True) (jmEq1 x y)
instance JmEq1 HDiscrete where
    jmEq1 HDiscrete_Nat HDiscrete_Nat = Just Refl
    jmEq1 HDiscrete_Int HDiscrete_Int = Just Refl
    jmEq1 _             _             = Nothing

-- BUG: deriving instance Read (HDiscrete a)
deriving instance Show (HDiscrete a)

sing_HDiscrete :: HDiscrete a -> Sing a
sing_HDiscrete HDiscrete_Nat = SNat
sing_HDiscrete HDiscrete_Int = SInt

hDiscrete_Sing :: Sing a -> Maybe (HDiscrete a)
hDiscrete_Sing SNat = Just HDiscrete_Nat
hDiscrete_Sing SInt = Just HDiscrete_Int
hDiscrete_Sing _    = Nothing

-- | Haskell type class for automatic 'HFractional' inference.
class (HSemiring_ a) => HDiscrete_ (a :: Hakaru) where
    hDiscrete :: HDiscrete a
instance HDiscrete_ 'HNat where hDiscrete = HDiscrete_Nat 
instance HDiscrete_ 'HInt where hDiscrete = HDiscrete_Int 

----------------------------------------------------------------
-- TODO: find better names than HContinuous and HIntegral
-- TODO: how to require that "if HRing a, then HRing b too"?
-- TODO: should we call this something like Dedekind-complete?
-- That's what distinguishes the reals from the rationals. Of course,
-- calling it that suggests (but does not require) that we should
-- have some supremum operator; but supremum only differs from
-- maximum if we have some way of talking about infinite sets of
-- values (which is surely too much to bother with).
--
-- | Concrete dictionaries for Hakaru types which are \"continuous\".
-- This is an ad-hoc class for (a) lifting 'HNat'\/'HInt' into
-- 'HProb'\/'HReal', and (b) handling the polymorphism of monotonic
-- functions like @etf@.
data HContinuous :: Hakaru -> * where
    HContinuous_Prob :: HContinuous 'HProb
    HContinuous_Real :: HContinuous 'HReal


instance Eq (HContinuous a) where -- This one could be derived...
    (==) = eq1
instance Eq1 HContinuous where
    eq1 x y = maybe False (const True) (jmEq1 x y)
instance JmEq1 HContinuous where
    jmEq1 HContinuous_Prob HContinuous_Prob = Just Refl
    jmEq1 HContinuous_Real HContinuous_Real = Just Refl
    jmEq1 _                _                = Nothing

-- BUG: deriving instance Read (HContinuous a)
deriving instance Show (HContinuous a)

sing_HContinuous :: HContinuous a -> Sing a
sing_HContinuous HContinuous_Prob = SProb
sing_HContinuous HContinuous_Real = SReal

hContinuous_Sing :: Sing a -> Maybe (HContinuous a)
hContinuous_Sing SProb = Just HContinuous_Prob
hContinuous_Sing SReal = Just HContinuous_Real
hContinuous_Sing _     = Nothing

sing_HIntegral :: HContinuous a -> Sing (HIntegral a)
sing_HIntegral = sing_HSemiring . hSemiring_HIntegralContinuous

-- hIntegral_Sing :: Sing (HIntegral a) -> Maybe (HContinuous a)

-- | Every 'HContinuous' is a 'HFractional'.
hFractional_HContinuous :: HContinuous a -> HFractional a
hFractional_HContinuous HContinuous_Prob = HFractional_Prob
hFractional_HContinuous HContinuous_Real = HFractional_Real

-- | The integral type of every 'HContinuous' is a 'HSemiring'.
hSemiring_HIntegralContinuous :: HContinuous a -> HSemiring (HIntegral a)
hSemiring_HIntegralContinuous HContinuous_Prob = HSemiring_Nat
hSemiring_HIntegralContinuous HContinuous_Real = HSemiring_Int

-- | Haskell type class for automatic 'HContinuous' inference.
--
-- Every 'HContinuous' has an associated type for the semiring of
-- its integral elements.
--
-- TODO: Can we somehow specify that the @HSemiring (HIntegral a)@
-- semantics coincides with the @HSemiring a@ semantics? Or should
-- we just assume that?
class (HSemiring_ (HIntegral a), HFractional_ a)
    => HContinuous_ (a :: Hakaru)
    where
    type HIntegral (a :: Hakaru) :: Hakaru
    hContinuous :: HContinuous a

instance HContinuous_ 'HProb where
    type HIntegral 'HProb = 'HNat
    hContinuous = HContinuous_Prob

instance HContinuous_ 'HReal where
    type HIntegral 'HReal = 'HInt
    hContinuous = HContinuous_Real


----------------------------------------------------------------
----------------------------------------------------------- fin.
