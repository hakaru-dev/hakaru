{-# LANGUAGE KindSignatures
           , DataKinds
           , GADTs
           , StandaloneDeriving
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.07.04
-- |
-- Module      :  Language.Hakaru.Syntax.Coercion
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Our theory of coercions for Hakaru's numeric hierarchy.
----------------------------------------------------------------
module Language.Hakaru.Syntax.Coercion
    ( PrimCoercion(..)
    , signed
    , continuous
    , Coercion(..)
    , singCoerceTo
    , singCoerceFrom
    ) where

import Prelude          hiding (id, (.))
import Control.Category (Category(..))
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.TypeEq
import Language.Hakaru.Syntax.HClasses

----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: (?) coercing HMeasure by coercing the underlying measure space.
-- TODO: lifting coercion over (:->), to avoid the need for eta-expansion
-- TODO: lifting coersion over datatypes, to avoid traversing them at runtime
-- TODO: see how GHC handles lifting coersions these days...

-- N.B., we don't need to store the dictionary values here, we can recover them by typeclass (using -XScopedTypeVariables).
--
-- | Primitive proofs of the inclusions in our numeric hierarchy.
data PrimCoercion :: Hakaru -> Hakaru -> * where
    Signed     :: !(HRing a)       -> PrimCoercion (NonNegative a) a
    Continuous :: !(HContinuous a) -> PrimCoercion (HIntegral   a) a

deriving instance Eq   (PrimCoercion a b)
-- BUG: deriving instance Read (PrimCoercion a b)
deriving instance Show (PrimCoercion a b)


-- BUG: GHC 7.8 does not allow making these into pattern synonyms:
-- (1) it disallows standalone type signatures for pattern synonyms,
-- so we'd need to give it as an annotation, which isn't too terrible;
-- but, (2) it does not allow polymorphic pattern synonyms :(

-- | A smart constructor for 'Signed'.
signed :: (HRing_ a) => Coercion (NonNegative a) a
signed = ConsCoercion (Signed hRing) IdCoercion

-- | A smart constructor for 'Continuous'.
continuous :: (HContinuous_ a) => Coercion (HIntegral a) a
continuous = ConsCoercion (Continuous hContinuous) IdCoercion


-- | General proofs of the inclusions in our numeric hierarchy.
data Coercion :: Hakaru -> Hakaru -> * where
    -- | Added the trivial coercion so we get the Category instance.
    -- This may/should make program transformations easier to write
    -- by allowing more intermediate ASTs, but will require a cleanup
    -- pass afterwards to remove the trivial coercions.
    IdCoercion :: Coercion a a

    -- TODO: but sometimes we need the snoc-based inductive hypothesis...
    -- | We use a cons-based approach rather than append-based in
    -- order to get a better inductive hypothesis.
    ConsCoercion :: !(PrimCoercion a b) -> !(Coercion b c) -> Coercion a c

-- BUG: deriving instance Eq   (Coercion a b)
-- BUG: deriving instance Read (Coercion a b)
deriving instance Show (Coercion a b)


instance Category Coercion where
    id = IdCoercion
    xs . IdCoercion        = xs
    xs . ConsCoercion y ys = ConsCoercion y (xs . ys)

----------------------------------------------------------------
singPrimCoerceTo :: PrimCoercion a b -> Sing a -> Sing b
singPrimCoerceTo (Signed theRing) s =
    case jmEq s (sing_NonNegative theRing) of
    Just Refl -> sing_HRing theRing
    Nothing   -> error "singPrimCoerceTo: the impossible happened"
singPrimCoerceTo (Continuous theCont) s =
    case jmEq s (sing_HIntegral theCont) of
    Just Refl -> sing_HContinuous theCont
    Nothing   -> error "singPrimCoerceTo: the impossible happened"


singPrimCoerceFrom :: PrimCoercion a b -> Sing b -> Sing a
singPrimCoerceFrom (Signed theRing) s =
    case jmEq s (sing_HRing theRing) of
    Just Refl -> sing_NonNegative theRing
    Nothing   -> error "singPrimCoerceFrom: the impossible happened"
singPrimCoerceFrom (Continuous theCont) s =
    case jmEq s (sing_HContinuous theCont) of
    Just Refl -> sing_HIntegral theCont
    Nothing   -> error "singPrimCoerceFrom: the impossible happened"


singCoerceTo :: Coercion a b -> Sing a -> Sing b
singCoerceTo IdCoercion          s = s
singCoerceTo (ConsCoercion c cs) s =
    singCoerceTo cs (singPrimCoerceTo c s)

singCoerceFrom :: Coercion a b -> Sing b -> Sing a
singCoerceFrom IdCoercion          s = s
singCoerceFrom (ConsCoercion c cs) s =
    singPrimCoerceFrom c (singCoerceFrom cs s)

----------------------------------------------------------------
{-
-- TODO: make these rules for coalescing things work
data UnsafeFrom_CoerceTo :: Hakaru -> Hakaru -> * where
    UnsafeFrom_CoerceTo
        :: !(Coercion c b)
        -> !(Coercion a b)
        -> UnsafeFrom_CoerceTo a c

unsafeFrom_coerceTo
    :: Coercion c b
    -> Coercion a b
    -> UnsafeFrom_CoerceTo a c
unsafeFrom_coerceTo xs ys =
    case xs of
    IdCoercion          -> UnsafeFrom_CoerceTo IdCoercion ys
    ConsCoercion x xs'  ->
        case ys of
        IdCoercion      -> UnsafeFrom_CoerceTo xs IdCoercion
        ConsCoercion y ys'
            -- TODO: use a variant of jmEq instead, so it typechecks
            | x == y    -> unsafeFrom_coerceTo xs' ys'
            | otherwise -> UnsafeFrom_CoerceTo xs  ys

data CoerceTo_UnsafeFrom :: Hakaru -> Hakaru -> * where
    CoerceTo_UnsafeFrom
        :: !(Coercion c b)
        -> !(Coercion a b)
        -> CoerceTo_UnsafeFrom a c

coerceTo_unsafeFrom
    :: Coercion a b
    -> Coercion c b
    -> CoerceTo_UnsafeFrom a c
coerceTo_unsafeFrom xs ys = ...
-}

-- TODO: implement a simplifying pass for pushing/gathering coersions over other things (e.g., Less/Equal)

----------------------------------------------------------------
----------------------------------------------------------- fin.
