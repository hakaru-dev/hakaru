{-# LANGUAGE KindSignatures
           , DataKinds
           , GADTs
           , StandaloneDeriving
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.07.15
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
    , singletonCoercion
    , singCoerceTo
    , singCoerceFrom
    , singCoerceDom
    , singCoerceCod
    , singCoerceDomCod
    -- * Experimental optimization functions
    {-
    , CoerceTo_UnsafeFrom(..)
    , simplifyCTUF
    , UnsafeFrom_CoerceTo(..)
    , simplifyUFCT
    -}
    , ZigZag(..)
    , simplifyZZ
    ) where

import Prelude          hiding (id, (.))
import Control.Category (Category(..))
import Data.Functor     ((<$>))
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


-- | A smart constructor for lifting 'PrimCoercion' into 'Coercion'
singletonCoercion :: PrimCoercion a b -> Coercion a b
singletonCoercion c = CCons c CNil

-- | A smart constructor for 'Signed'.
signed :: (HRing_ a) => Coercion (NonNegative a) a
signed = singletonCoercion $ Signed hRing

-- | A smart constructor for 'Continuous'.
continuous :: (HContinuous_ a) => Coercion (HIntegral a) a
continuous = singletonCoercion $ Continuous hContinuous


-- | General proofs of the inclusions in our numeric hierarchy.
data Coercion :: Hakaru -> Hakaru -> * where
    -- | Added the trivial coercion so we get the Category instance.
    -- This may/should make program transformations easier to write
    -- by allowing more intermediate ASTs, but will require a cleanup
    -- pass afterwards to remove the trivial coercions.
    CNil :: Coercion a a

    -- TODO: but sometimes we need the snoc-based inductive hypothesis...
    -- | We use a cons-based approach rather than append-based in
    -- order to get a better inductive hypothesis.
    CCons :: !(PrimCoercion a b) -> !(Coercion b c) -> Coercion a c

-- BUG: deriving instance Eq   (Coercion a b)
-- BUG: deriving instance Read (Coercion a b)
deriving instance Show (Coercion a b)


instance Category Coercion where
    id = CNil
    xs . CNil       = xs
    xs . CCons y ys = CCons y (xs . ys)

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
singCoerceTo CNil         s = s
singCoerceTo (CCons c cs) s =
    singCoerceTo cs (singPrimCoerceTo c s)

singCoerceFrom :: Coercion a b -> Sing b -> Sing a
singCoerceFrom CNil         s = s
singCoerceFrom (CCons c cs) s =
    singPrimCoerceFrom c (singCoerceFrom cs s)

----------------------------------------------------------------
singPrimCoerceDom :: PrimCoercion a b -> Sing a
singPrimCoerceDom (Signed     theRing) = sing_NonNegative theRing
singPrimCoerceDom (Continuous theCont) = sing_HIntegral   theCont

singPrimCoerceCod :: PrimCoercion a b -> Sing b
singPrimCoerceCod (Signed     theRing) = sing_HRing       theRing
singPrimCoerceCod (Continuous theCont) = sing_HContinuous theCont


singCoerceDom :: Coercion a b -> Maybe (Sing a)
singCoerceDom CNil           = Nothing
singCoerceDom (CCons c CNil) = Just $ singPrimCoerceDom c
singCoerceDom (CCons c cs)   = singPrimCoerceFrom c <$> singCoerceDom cs

singCoerceCod :: Coercion a b -> Maybe (Sing b)
singCoerceCod CNil           = Nothing
singCoerceCod (CCons c CNil) = Just $ singPrimCoerceCod c
singCoerceCod (CCons c cs)   = Just . singCoerceTo cs $ singPrimCoerceCod c


singCoerceDomCod :: Coercion a b -> Maybe (Sing a, Sing b)
singCoerceDomCod CNil           = Nothing
singCoerceDomCod (CCons c CNil) =
    Just (singPrimCoerceDom c, singPrimCoerceCod c)
singCoerceDomCod (CCons c cs)   = do
    dom <- singCoerceDom cs
    Just (singPrimCoerceFrom c dom
        , singCoerceTo cs $ singPrimCoerceCod c
        )

----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: move this to HClasses.hs
jmEq_Ring :: HRing a -> HRing b -> Maybe (TypeEq a b)
jmEq_Ring HRing_Int  HRing_Int  = Just Refl
jmEq_Ring HRing_Real HRing_Real = Just Refl
jmEq_Ring _ _ = Nothing

-- TODO: move this to HClasses.hs
jmEq_Cont :: HContinuous a -> HContinuous b -> Maybe (TypeEq a b)
jmEq_Cont HContinuous_Prob HContinuous_Prob = Just Refl
jmEq_Cont HContinuous_Real HContinuous_Real = Just Refl
jmEq_Cont _ _ = Nothing

jmEq_Coe
    :: PrimCoercion a1 a2
    -> PrimCoercion b1 b2
    -> Maybe (TypeEq a1 b1, TypeEq a2 b2)
jmEq_Coe (Signed r1) (Signed r2) =
    jmEq_Ring r1 r2 >>= \Refl -> Just (Refl, Refl)
jmEq_Coe (Continuous c1) (Continuous c2) =
    jmEq_Cont c1 c2 >>= \Refl -> Just (Refl, Refl)
jmEq_Coe _ _ = Nothing


data CoerceTo_UnsafeFrom :: Hakaru -> Hakaru -> * where
    CTUF :: !(Coercion b c) -> !(Coercion b a) -> CoerceTo_UnsafeFrom a c

-- BUG: deriving instance Eq   (CoerceTo_UnsafeFrom a b)
-- BUG: deriving instance Read (CoerceTo_UnsafeFrom a b)
deriving instance Show (CoerceTo_UnsafeFrom a b)

-- TODO: handle the fact that certain coercions commute over one another!
simplifyCTUF :: CoerceTo_UnsafeFrom a c -> CoerceTo_UnsafeFrom a c
simplifyCTUF (CTUF xs ys) =
    case xs of
    CNil        -> CTUF CNil ys
    CCons x xs' ->
        case ys of
        CNil        -> CTUF xs CNil
        CCons y ys' ->
            case jmEq_Coe x y of
            Just (Refl, Refl) -> simplifyCTUF (CTUF xs' ys')
            Nothing           -> CTUF xs ys

----------------------------------------------------------------
-- | Choose the other inductive hypothesis.
data RevCoercion :: Hakaru -> Hakaru -> * where
    CLin  :: RevCoercion a a
    CSnoc :: !(RevCoercion a b) -> !(PrimCoercion b c) -> RevCoercion a c

-- BUG: deriving instance Eq   (RevCoercion a b)
-- BUG: deriving instance Read (RevCoercion a b)
deriving instance Show (RevCoercion a b)

instance Category RevCoercion where
    id = CLin
    CLin . xs       = xs
    CSnoc ys y . xs = CSnoc (ys . xs) y

revCons :: PrimCoercion a b -> RevCoercion b c -> RevCoercion a c
revCons x CLin         = CSnoc CLin x
revCons x (CSnoc ys y) = CSnoc (revCons x ys) y

toRev :: Coercion a b -> RevCoercion a b
toRev CNil         = CLin
toRev (CCons x xs) = revCons x (toRev xs)

obvSnoc :: Coercion a b -> PrimCoercion b c -> Coercion a c
obvSnoc CNil         y = CCons y CNil
obvSnoc (CCons x xs) y = CCons x (obvSnoc xs y)

fromRev :: RevCoercion a b -> Coercion a b
fromRev CLin         = CNil
fromRev (CSnoc xs x) = obvSnoc (fromRev xs) x

data UnsafeFrom_CoerceTo :: Hakaru -> Hakaru -> * where
    UFCT
        :: !(Coercion c b)
        -> !(Coercion a b)
        -> UnsafeFrom_CoerceTo a c

-- BUG: deriving instance Eq   (UnsafeFrom_CoerceTo a b)
-- BUG: deriving instance Read (UnsafeFrom_CoerceTo a b)
deriving instance Show (UnsafeFrom_CoerceTo a b)

data RevUFCT :: Hakaru -> Hakaru -> * where
    RevUFCT :: !(RevCoercion c b) -> !(RevCoercion a b) -> RevUFCT a c
        
-- TODO: handle the fact that certain coercions commute over one another!
-- N.B., This version can be tricky to get to type check because our associated type families aren't guaranteed injective.
simplifyUFCT :: UnsafeFrom_CoerceTo a c -> UnsafeFrom_CoerceTo a c
simplifyUFCT (UFCT xs ys) =
    case simplifyRevUFCT $ RevUFCT (toRev xs) (toRev ys) of
    RevUFCT xs' ys' -> UFCT (fromRev xs') (fromRev ys')

simplifyRevUFCT :: RevUFCT a c -> RevUFCT a c
simplifyRevUFCT (RevUFCT xs ys) =
    case xs of
    CLin        -> RevUFCT CLin ys
    CSnoc xs' x ->
        case ys of
        CLin        -> RevUFCT xs CLin
        CSnoc ys' y ->
            case jmEq_Coe x y of
            Just (Refl, Refl) -> simplifyRevUFCT (RevUFCT xs' ys')
            Nothing           -> RevUFCT xs ys


-- TODO: implement a simplifying pass for pushing/gathering coersions over other things (e.g., Less/Equal)

----------------------------------------------------------------
----------------------------------------------------------------

-- | An arbitrary composition of safe and unsafe coercions.
data ZigZag :: Hakaru -> Hakaru -> * where
    ZRefl :: ZigZag a a
    Zig   :: !(Coercion a b) -> !(ZigZag b c) -> ZigZag a c
    Zag   :: !(Coercion b a) -> !(ZigZag b c) -> ZigZag a c

-- BUG: deriving instance Eq   (ZigZag a b)
-- BUG: deriving instance Read (ZigZag a b)
deriving instance Show (ZigZag a b)

-- TODO: whenever we build up a new ZigZag from the remains of a simplification step, do we need to resimplify? If so, how can we avoid quadratic behavior? cf., <http://research.microsoft.com/en-us/um/people/simonpj/papers/ext-f/fc-normalization-rta.pdf> Also, try just doing a shortest-path problem on the graph of coercions (since we can get all the singletons along the way)
-- TODO: handle the fact that certain coercions commute over one another!
simplifyZZ :: ZigZag a b -> ZigZag a b
simplifyZZ ZRefl      = ZRefl
simplifyZZ (Zig x xs) =
    case simplifyZZ xs of
    ZRefl   -> Zig x ZRefl
    Zig y z -> Zig (y . x) z
    Zag y z ->
        -- TODO: can we optimize this to avoid reversing things?
        case simplifyUFCT (UFCT x y) of
        UFCT CNil CNil -> z
        UFCT CNil y'   -> Zag y' z
        UFCT x'   CNil -> Zig x' z
        UFCT x'   y'   -> Zig x' (Zag y' z)
simplifyZZ (Zag x xs) =
    case simplifyZZ xs of
    ZRefl   -> Zag x ZRefl
    Zag y z -> Zag (x . y) z
    Zig y z ->
        case simplifyCTUF (CTUF x y) of
        CTUF CNil CNil -> z
        CTUF CNil y'   -> Zig y' z
        CTUF x'   CNil -> Zag x' z
        CTUF x'   y'   -> Zag x' (Zig y' z)

----------------------------------------------------------------
----------------------------------------------------------- fin.
