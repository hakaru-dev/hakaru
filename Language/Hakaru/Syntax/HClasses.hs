{-# LANGUAGE KindSignatures
           , DataKinds
           , PolyKinds
           , TypeFamilies
           , FlexibleContexts
           , FlexibleInstances
           , TypeSynonymInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.06.28
-- |
-- Module      :  Language.Hakaru.Syntax.HClasses
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- A collection of type classes for encoding Hakaru's numeric hierarchy.
----------------------------------------------------------------
module Language.Hakaru.Syntax.HClasses where

import Language.Hakaru.Syntax.DataKind

----------------------------------------------------------------
{- TODO: break the HEq class out from HOrder
-- TODO: allow lifting of equality to work on HPair, HEither,...?
class HEq (a :: Hakaru *)
instance HEq HBool
instance HEq 'HNat
instance HEq 'HInt
instance HEq 'HProb
instance HEq 'HReal
-}

-- TODO: class HPER (a :: Hakaru *) -- ?
-- TODO: class HPartialOrder (a :: Hakaru *)

{-
-- TODO: replace the open type class with a closed equivalent, e.g.:
data HOrder :: Hakaru * -> * where
    HOrder_HNat  :: HOrder 'HNat
    HOrder_HInt  :: HOrder 'HInt
    HOrder_HProb :: HOrder 'HProb
    HOrder_HReal :: HOrder 'HReal
    ...
-- The problem is, how to we handle things like the HRing type class?
-}
class    HOrder (a :: Hakaru)
instance HOrder HBool
instance HOrder 'HNat
instance HOrder 'HInt
instance HOrder 'HProb
instance HOrder 'HReal
instance HOrder HUnit
instance (HOrder a, HOrder b) => HOrder (HPair   a b)
instance (HOrder a, HOrder b) => HOrder (HEither a b)
instance (HOrder a) => HOrder ('HArray a)


-- N.B., even though these ones are commutative, we don't assume that!
class    HSemiring (a :: Hakaru)
instance HSemiring 'HNat
instance HSemiring 'HInt
instance HSemiring 'HProb
instance HSemiring 'HReal


-- N.B., even though these ones are commutative, we don't assume that!
-- N.B., the NonNegative associated type is (a) actually the semiring
-- that generates this ring, but (b) is also used for the result
-- of calling the absolute value. For Int and Real that's fine; but
-- for Complex and Vector these two notions diverge
-- TODO: Can we specify that the @HSemiring (NonNegative a)@
-- constraint coincides with the @HSemiring a@ constraint on the
-- appropriate subset of @a@? Or should that just be assumed...?
class (HSemiring (NonNegative a), HSemiring a)
    => HRing (a :: Hakaru) where type NonNegative a :: Hakaru
instance HRing 'HInt  where type NonNegative 'HInt  = 'HNat 
instance HRing 'HReal where type NonNegative 'HReal = 'HProb 

{-
data HRing_ :: Hakaru -> * where
    HRing_Int  :: HRing_ 'HInt
    HRing_Real :: HRing_ 'HReal

type family   NonNegative (a :: Hakaru) :: Hakaru
type instance NonNegative 'HInt  = 'HNat 
type instance NonNegative 'HReal = 'HProb 

data HRing :: Hakaru -> * where
    HRing
        :: !(HRing_ a)
        -> !(HSemiring a)
        -> !(HSemiring (NonNegative a))
        -> HRing a
-}


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
-- | A division-semiring; i.e., a division-ring without negation.
-- This is called a \"semifield\" in ring theory, but should not
-- be confused with the \"semifields\" of geometry.
class (HSemiring a) => HFractional (a :: Hakaru)
instance HFractional 'HProb
instance HFractional 'HReal

-- type HDivisionRing a = (HFractional a, HRing a)
-- type HField a = (HDivisionRing a, HCommutativeSemiring a)


-- Numbers formed by finitely many uses of integer addition,
-- subtraction, multiplication, division, and nat-roots are all
-- algebraic; however, N.B., not all algebraic numbers can be formed
-- this way (cf., Abel–Ruffini theorem)
-- TODO: ought we require HRing or HFractional rather than HSemiring?
-- TODO: any special associated type?
-- N.B., we /assume/ closure under the semiring operations, thus
-- we get things like @sqrt 2 + sqrt 3@ which cannot be expressed
-- as a single root. Thus, solving the HRadical class means we need
-- solutions to more general polynomials (than just @x^n - a@) in
-- order to express the results as roots. However, the Galois groups
-- of these are all solvable, so this shouldn't be too bad.
class (HSemiring a) => HRadical (a :: Hakaru)
instance HRadical 'HProb

-- TODO: class (HDivisionRing a, HRadical a) => HAlgebraic a where...


-- TODO: find a better name than HIntegral
-- TODO: how to require that "if HRing a, then HRing b too"?
class (HSemiring (HIntegral a), HFractional a)
    => HContinuous (a :: Hakaru) where type HIntegral a :: Hakaru
instance HContinuous 'HProb where type HIntegral 'HProb = 'HNat 
instance HContinuous 'HReal where type HIntegral 'HReal = 'HInt 

----------------------------------------------------------------
----------------------------------------------------------- fin.
