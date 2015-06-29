{-# LANGUAGE KindSignatures
           , DataKinds
           , GADTs
           , StandaloneDeriving
           , PatternSynonyms
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.06.28
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
    , pattern Signed
    , pattern Continuous
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
-- TODO: lifting coercion over HFun, to avoid the need for eta-expansion
-- TODO: lifting coersion over datatypes, to avoid traversing them at runtime
-- TODO: see how GHC handles lifting coersions these days...

-- | Primitive proofs of the inclusions in our numeric hierarchy.
data PrimCoercion :: Hakaru -> Hakaru -> * where
    PrimSigned     :: HRing a       => PrimCoercion (NonNegative a) a
    PrimContinuous :: HContinuous a => PrimCoercion (HIntegral   a) a

deriving instance Eq   (PrimCoercion a b)
-- BUG: deriving instance Read (PrimCoercion a b)
deriving instance Show (PrimCoercion a b)


-- | A smart constructor and pattern synonym for 'PrimSigned'.
pattern Signed :: HRing a => Coercion (NonNegative a) a
pattern Signed = ConsCoercion PrimSigned IdCoercion


-- | A smart constructor and pattern synonym for 'PrimContinuous'.
pattern Continuous :: HContinuous a => Coercion (HIntegral a) a
pattern Continuous = ConsCoercion PrimContinuous IdCoercion


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
-- BUG: we must use explicit singleton dictionaries for HRing and HContinuous, so we can pattern match on them in order to produce the resulting singleton.
singPrimCoerceTo :: PrimCoercion a b -> Sing a -> Sing b
singPrimCoerceTo PrimSigned     s = error "TODO: singPrimCoerceTo"
singPrimCoerceTo PrimContinuous s = error "TODO: singPrimCoerceTo"

singCoerceTo :: Coercion a b -> Sing a -> Sing b
singCoerceTo IdCoercion          s = s
singCoerceTo (ConsCoercion c cs) s = singCoerceTo cs (singPrimCoerceTo c s)

singPrimCoerceFrom :: PrimCoercion a b -> Sing b -> Sing a
singPrimCoerceFrom PrimSigned     s = error "TODO: singPrimCoerceFrom"
singPrimCoerceFrom PrimContinuous s = error "TODO: singPrimCoerceFrom"

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
