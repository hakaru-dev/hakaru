{-# LANGUAGE DataKinds
           , PolyKinds
           , TypeOperators
           , GADTs
           , TypeFamilies
           , PatternSynonyms
           
           -- TODO: how much of this is needed for splices?
           , QuasiQuotes
           , TemplateHaskell
           , UndecidableInstances
           , TypeSynonymInstances
           , FlexibleInstances
           , ScopedTypeVariables
           , StandaloneDeriving
           #-}

-- Singletons generates orphan instances warnings 
{-# OPTIONS_GHC -Wall -fwarn-tabs -fno-warn-orphans #-}

-- DEBUG
-- {-# OPTIONS_GHC -ddump-splices #-} 

----------------------------------------------------------------
--                                                    2015.06.30
-- |
-- Module      :  Language.Hakaru.Syntax.TypeEq
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Singleton types for the @Hakaru@ kind, and a decision procedure
-- for @Hakaru@ type-equality.
----------------------------------------------------------------
module Language.Hakaru.Syntax.TypeEq 
    ( module Language.Hakaru.Syntax.TypeEq
    , Sing(..)
    , SingI(..)
    , jmEq
    {-
    , pattern SBool
    , pattern SUnit
    , pattern SPair
    , pattern SEither
    , pattern SList
    , pattern SMaybe
    -}
    {-
    , SingKind(..), SDecide(..), (:~:)(..)
    -}
    ) where

import Language.Hakaru.Syntax.DataKind
{- -- BUG: this code does not work on my system(s). It generates some strange CPP errors.

import Data.Singletons
import Data.Singletons.TH 
import Data.Singletons.Prelude (Sing(..))

import Unsafe.Coerce

genSingletons [ ''Hakaru, ''HakaruFun  ] 

-- BUG: The generated code doesn't typecheck because it contains a Symbol, so it has to be written manually. I imagine singletons should have a way to handle Symbol but I haven't found.
-- genSingletons [ ''HakaruCon ]

-- Singleton datatype
infixl 0 :%@
data instance Sing (x :: HakaruCon k) where 
    SHCon :: Sing s -> Sing (HCon s) 
    (:%@) :: Sing a -> Sing b -> Sing (a :@ b) 

-- Show instances for each singleton
instance Show (SHakaru x) where
    show = show . fromSing 
instance Show (SHakaruCon (x :: HakaruCon Hakaru)) where
    show = show . fromSing 
instance Show (SHakaruFun x) where
    show = show . fromSing 

-- Type synonym for HakaruCon
type SHakaruCon (x :: HakaruCon k) = Sing x

-- Demoting/promoting. Used for showing singletons. 
instance SingKind ('KProxy :: KProxy k)
    => SingKind ('KProxy :: KProxy (HakaruCon k))
    where
    type DemoteRep ('KProxy :: KProxy (HakaruCon k)) =
        HakaruCon (DemoteRep ('KProxy :: KProxy k))

    fromSing (SHCon b_a1d9D) =
        HCon ((unsafeCoerce :: String -> Symbol) (fromSing b_a1d9D))
    fromSing ((:%@) b_a1d9E b_a1d9F) =
        (:@) (fromSing b_a1d9E) (fromSing b_a1d9F)

    toSing (HCon b_a1d9G) =
        case toSing ((unsafeCoerce :: Symbol -> String) b_a1d9G)
            :: SomeSing ('KProxy :: KProxy Symbol)
        of { SomeSing c_a1d9H -> SomeSing (SHCon c_a1d9H) }

    toSing (a :@ b) = 
        case (toSing a :: SomeSing ('KProxy :: KProxy (HakaruCon k))
            , toSing b :: SomeSing ('KProxy :: KProxy k)
            )
        of (SomeSing a', SomeSing b') -> SomeSing (a' :%@ b')

-- Implicit singleton 
instance SingI a            => SingI (HCon a) where sing = SHCon sing 
instance (SingI a, SingI b) => SingI (a :@ b) where sing = (:%@) sing sing

-- This generates jmEq (or rather a strong version)
singDecideInstances [ ''Hakaru, ''HakaruCon, ''HakaruFun ] 

type TypeEq = (:~:)

jmEq :: SHakaru a -> SHakaru b -> Maybe (a :~: b)
jmEq a b =
    case a %~ b of 
    Proved p -> Just p 
    _        -> Nothing


-- TODO: Smart constructors for built-in types like Pair, Either, etc.
sPair :: Sing a -> Sing b -> Sing (HPair a b) 
sPair a b =
    SHTag (SHCon (singByProxy (Proxy :: Proxy "Pair")) :%@ a :%@ b) 
        (SCons (SCons (SK a) $ SCons (SK b) SNil) SNil)
-}


----------------------------------------------------------------
data family Sing (a :: k) :: *

-- BUG: data family instances must be fully saturated, but since these are GADTs, the name of the parameter is irrelevant. However, using a wildcard causes GHC to panic. cf., <https://ghc.haskell.org/trac/ghc/ticket/10586>

-- | Singleton types for the kind of Hakaru types. We need to use
-- this instead of 'Proxy' in order to implement 'jmEq'.
data instance Sing (unused :: Hakaru) where
    SNat     :: Sing 'HNat
    SInt     :: Sing 'HInt
    SProb    :: Sing 'HProb
    SReal    :: Sing 'HReal
    SMeasure :: !(Sing a) -> Sing ('HMeasure a)
    SArray   :: !(Sing a) -> Sing ('HArray a)
    SFun     :: !(Sing a) -> !(Sing b) -> Sing ('HFun a b)

    STag :: !(Sing con) -> !(Sing (Code con)) -> Sing ('HTag con (Code con))
    -- TODO: @a@ should always be @'HTag con sop@, and @sop@ should always be @Code con@
    SUnrolled :: !(Sing sop) -> !(Sing a) -> Sing (sop ':$ a)

-- BUG: deriving instance Eq   (Sing a)
-- BUG: deriving instance Read (Sing a)
-- BUG: deriving instance Show (Sing a)

{-
-- TODO:
pattern SUnit :: Sing HUnit
pattern SUnit =
    STag (SCon SSymbol_Unit)
        (SNil `SPlus` SVoid)
        
pattern SBool :: Sing HBool
pattern SBool =
    STag (SCon SSymbol_Bool)
        (SNil `SPlus` SNil `SPlus` SVoid)

-- BUG: what does this "Conflicting definitions for ‘a’" message mean?
pattern SPair :: Sing a -> Sing b -> Sing (HPair a b)
pattern SPair a b =
    STag (SCon SSymbol_Pair `SApp` a `SApp` b)
        ((SKonst a `SCons` SKonst b `SCons` SNil) `SPlus` SVoid)

pattern SEither :: Sing a -> Sing b -> Sing (HEither a b)
pattern SEither a b =
    STag (SCon SSymbol_Either `SApp` a `SApp` b)
        ((SKonst a `SCons` SNil) `SPlus` (SKonst b `SCons` SNil)
            `SPlus` SVoid)

pattern SList :: Sing a -> Sing (HList a)
pattern SList a =
    STag (SCon SSymbol_List `SApp` a)
        (SNil `SPlus` (SKonst a `SCons` SIdent `SCons` SNil) `SPlus` SVoid)

pattern SMaybe :: Sing a -> Sing (HMaybe a)
pattern SMaybe a =
    STag (SCon SSymbol_Maybe `SApp` a)
        (SNil `SPlus` (SKonst a `SCons` SNil) `SPlus` SVoid)
-}


-- HACK: because of polykindedness, we have to give explicit type signatures for the index in the result of these data constructors.

data instance Sing (unused :: HakaruCon Hakaru) where
    SCon :: !(Sing s)              -> Sing ('HCon s :: HakaruCon Hakaru)
    SApp :: !(Sing a) -> !(Sing b) -> Sing (a ':@ b :: HakaruCon Hakaru) 

data instance Sing (s :: Symbol) where -- TODO: fixme
    SSymbol_Bool   :: Sing "Bool"
    SSymbol_Unit   :: Sing "Unit"
    SSymbol_Pair   :: Sing "Pair"
    SSymbol_Either :: Sing "Either"
    SSymbol_List   :: Sing "List"
    SSymbol_Maybe  :: Sing "Maybe"

data instance Sing (unused :: [[HakaruFun]]) where
    SVoid :: Sing ('[] :: [[HakaruFun]])
    SPlus
        :: !(Sing xs)
        -> !(Sing xss)
        -> Sing ((xs ': xss) :: [[HakaruFun]])

data instance Sing (unused :: [HakaruFun]) where
    SNil  :: Sing ('[] :: [HakaruFun])
    SCons :: !(Sing x) -> !(Sing xs) -> Sing ((x ': xs) :: [HakaruFun])

data instance Sing (unused :: HakaruFun) where
    SIdent :: Sing 'I
    SKonst :: !(Sing a) -> Sing ('K a)

----------------------------------------------------------------
-- | A class for automatically generating the singleton for a given
-- Hakaru type.
class SingI (a :: k) where sing :: Sing a

instance SingI 'HNat                             where sing = SNat 
instance SingI 'HInt                             where sing = SInt 
instance SingI 'HProb                            where sing = SProb 
instance SingI 'HReal                            where sing = SReal 
instance (SingI a) => SingI ('HMeasure a)        where sing = SMeasure sing
instance (SingI a) => SingI ('HArray a)          where sing = SArray sing
instance (SingI a, SingI b) => SingI ('HFun a b) where sing = SFun sing sing

-- N.B., must use @(~)@ to delay the use of the type family (it's illegal to put it inline in the instance head).
instance (sop ~ Code con, SingI con, SingI sop)
    => SingI ('HTag con sop)
    where
    sing = STag sing sing
instance (SingI sop, SingI a) => SingI (sop ':$ a) where
    sing = SUnrolled sing sing

instance SingI ('HCon s :: HakaruCon Hakaru) where
    sing = SCon sing
instance (SingI a, SingI b) => SingI ((a ':@ b) :: HakaruCon Hakaru) where
    sing = SApp sing sing

instance SingI (s :: Symbol) where
    sing = error "sing{Symbol} unimplemented"
    
instance SingI ('[] :: [[HakaruFun]]) where
    sing = SVoid 
instance (SingI xs, SingI xss) => SingI ((xs ': xss) :: [[HakaruFun]]) where
    sing = SPlus sing sing
    
instance SingI ('[] :: [HakaruFun]) where
    sing = SNil 
instance (SingI x, SingI xs) => SingI ((x ': xs) :: [HakaruFun]) where
    sing = SCons sing sing

instance SingI 'I where
    sing = SIdent 
instance (SingI a) => SingI ('K a) where
    sing = SKonst sing

----------------------------------------------------------------
{-
-- I think it's impossible to actually implement a function of this
-- type (i.e., without any type constraints on @a@). That is, even
-- though for every @a :: Hakaru@ there is some value of type @Sing
-- a@, and even though that value is unique for each @a@, nevertheless
-- I'm pretty sure @forall a. Sing a@ must be empty, by parametricity.
-- We'd need to inspect the @a@ in order to construct the appropriate
-- @Sing a@, but \"forall\" doesn't allow that.
--
-- BUG: this implementation just gives us a <<loop>>
toSing :: proxy a -> Sing a
toSing _ = everySing es
    where
    es = EverySing (everySing es)

everySing :: EverySing -> Sing a
everySing (EverySing s) = s

data EverySing where
    EverySing :: (forall a. Sing a) -> EverySing
-}

-- TODO: what is the actual runtype cost of using 'toSing'...?
-- | Convert any given proxy into a singleton. This is a convenience
-- function for type checking; it ignores its argument.
toSing :: (SingI a) => proxy a -> Sing a
toSing _ = sing
{-# INLINE toSing #-}

-- | Concrete proofs of type equality. In order to make use of a
-- proof @p :: TypeEq a b@, you must pattern-match on the 'Refl'
-- constructor in order to show GHC that the types @a@ and @b@ are
-- equal.
data TypeEq :: k -> k -> * where
    Refl :: TypeEq a a

-- | Type constructors are extensional.
cong :: TypeEq a b -> TypeEq (f a) (f b)
cong Refl = Refl


-- BUG: how can we implement this when Sing isn't a closed type?
-- | Decide whether the types @a@ and @b@ are equal. If you don't
-- have the singleton laying around, you can use 'toSing' to convert
-- whatever type-indexed value into one.
jmEq :: Sing (a :: Hakaru) -> Sing (b :: Hakaru) -> Maybe (TypeEq a b)
jmEq SNat             SNat             = Just Refl
jmEq SInt             SInt             = Just Refl
jmEq SProb            SProb            = Just Refl
jmEq SReal            SReal            = Just Refl
jmEq (SMeasure a)     (SMeasure b)     = jmEq a  b  >>= \Refl -> Just Refl
jmEq (SArray   a)     (SArray   b)     = jmEq a  b  >>= \Refl -> Just Refl
jmEq (SFun     a1 a2) (SFun     b1 b2) = jmEq a1 b1 >>= \Refl -> 
                                         jmEq a2 b2 >>= \Refl -> Just Refl
jmEq (STag con1 code1) (STag con2 code2) =
    jmEq_Con  con1  con2  >>= \Refl ->
    jmEq_Code code1 code2 >>= \Refl -> Just Refl
jmEq (SUnrolled code1 a) (SUnrolled code2 b) =
    jmEq_Code code1 code2 >>= \Refl -> 
    jmEq a b >>= \Refl -> Just Refl
jmEq _ _ = Nothing

jmEq_Con
    :: Sing (a :: HakaruCon Hakaru)
    -> Sing (b :: HakaruCon Hakaru)
    -> Maybe (TypeEq a b)
jmEq_Con (SCon s)   (SCon z)   = jmEq_Symb s z >>= \Refl -> Just Refl
jmEq_Con (SApp f a) (SApp g b) = jmEq_Con  f g >>= \Refl ->
                                 jmEq a b      >>= \Refl -> Just Refl
jmEq_Con _ _ = Nothing

jmEq_Symb :: Sing (a :: Symbol) -> Sing (b :: Symbol) -> Maybe (TypeEq a b)
jmEq_Symb SSymbol_Bool   SSymbol_Bool   = Just Refl
jmEq_Symb SSymbol_Unit   SSymbol_Unit   = Just Refl
jmEq_Symb SSymbol_Pair   SSymbol_Pair   = Just Refl
jmEq_Symb SSymbol_Either SSymbol_Either = Just Refl
jmEq_Symb SSymbol_List   SSymbol_List   = Just Refl
jmEq_Symb SSymbol_Maybe  SSymbol_Maybe  = Just Refl
jmEq_Symb _ _ = Nothing

jmEq_Code
    :: Sing (a :: [[HakaruFun]])
    -> Sing (b :: [[HakaruFun]])
    -> Maybe (TypeEq a b)
jmEq_Code SVoid        SVoid        = Just Refl
jmEq_Code (SPlus x xs) (SPlus y ys) =
    jmEq_Prod x  y  >>= \Refl ->
    jmEq_Code xs ys >>= \Refl -> Just Refl
jmEq_Code _ _ = Nothing

jmEq_Prod
    :: Sing (a :: [HakaruFun])
    -> Sing (b :: [HakaruFun])
    -> Maybe (TypeEq a b)
jmEq_Prod SNil         SNil         = Just Refl
jmEq_Prod (SCons x xs) (SCons y ys) =
    jmEq_Fun  x  y  >>= \Refl ->
    jmEq_Prod xs ys >>= \Refl -> Just Refl
jmEq_Prod _ _ = Nothing

jmEq_Fun
    :: Sing (a :: HakaruFun)
    -> Sing (b :: HakaruFun)
    -> Maybe (TypeEq a b)
jmEq_Fun SIdent     SIdent     = Just Refl
jmEq_Fun (SKonst a) (SKonst b) = jmEq a b >>= \Refl -> Just Refl
jmEq_Fun _ _ = Nothing

----------------------------------------------------------------
----------------------------------------------------------- fin.