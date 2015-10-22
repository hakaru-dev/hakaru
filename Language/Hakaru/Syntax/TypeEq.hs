{-# LANGUAGE DataKinds
           , PolyKinds
           , TypeOperators
           , GADTs
           , TypeFamilies
           , FlexibleInstances
           , RankNTypes
           #-}
{-
           -- TODO: how much of this is needed for splices?
           , QuasiQuotes
           , TemplateHaskell
           , UndecidableInstances
           , TypeSynonymInstances
           , ScopedTypeVariables
           , StandaloneDeriving
-- Singletons generates orphan instances warnings
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- DEBUG
-- {-# OPTIONS_GHC -ddump-splices #-}
-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.21
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
    ( Sing(..)
    , SingI(..)
    , toSing
    -- * Some helpful shorthands for \"built-in\" datatypes
    , sBool
    , sUnit
    , sPair
    , sEither
    , sList
    , sMaybe
    {-
    , module Language.Hakaru.Syntax.TypeEq
    , SingKind(..), SDecide(..), (:~:)(..)
    -}
    ) where

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.DataKind
----------------------------------------------------------------
----------------------------------------------------------------
infixr 0 `SFun`
infixr 6 `SPlus`
infixr 7 `SEt`


-- | The data families of singletons for each kind.
data family Sing (a :: k) :: *


-- | A class for automatically generating the singleton for a given
-- Hakaru type.
class SingI (a :: k) where sing :: Sing a


----------------------------------------------------------------
-- BUG: data family instances must be fully saturated, but since
-- these are GADTs, the name of the parameter is irrelevant. However,
-- using a wildcard causes GHC to panic. cf.,
-- <https://ghc.haskell.org/trac/ghc/ticket/10586>

-- | Singleton types for the kind of Hakaru types. We need to use
-- this instead of 'Proxy' in order to implement 'jmEq1'.
data instance Sing (a :: Hakaru) where
    SNat     :: Sing 'HNat
    SInt     :: Sing 'HInt
    SProb    :: Sing 'HProb
    SReal    :: Sing 'HReal
    SMeasure :: !(Sing a) -> Sing ('HMeasure a)
    SArray   :: !(Sing a) -> Sing ('HArray a)
    -- TODO: would it be clearer to use (:$->) in order to better mirror the type-level (:->)
    SFun     :: !(Sing a) -> !(Sing b) -> Sing (a ':-> b)
    SData    :: !(Sing t) -> !(Sing (Code t)) -> Sing (HData' t)


instance Eq (Sing (a :: Hakaru)) where
    (==) = eq1
instance Eq1 (Sing :: Hakaru -> *) where
    eq1 x y = maybe False (const True) (jmEq1 x y)
instance JmEq1 (Sing :: Hakaru -> *) where
    jmEq1 SNat             SNat             = Just Refl
    jmEq1 SInt             SInt             = Just Refl
    jmEq1 SProb            SProb            = Just Refl
    jmEq1 SReal            SReal            = Just Refl
    jmEq1 (SMeasure a)     (SMeasure b)     =
        jmEq1 a  b  >>= \Refl ->
        Just Refl
    jmEq1 (SArray   a)     (SArray   b)     =
        jmEq1 a  b  >>= \Refl ->
        Just Refl
    jmEq1 (SFun     a1 a2) (SFun     b1 b2) =
        jmEq1 a1 b1 >>= \Refl ->
        jmEq1 a2 b2 >>= \Refl ->
        Just Refl
    jmEq1 (SData con1 code1) (SData con2 code2) =
        jmEq1 con1  con2  >>= \Refl ->
        jmEq1 code1 code2 >>= \Refl ->
        Just Refl
    jmEq1 _ _ = Nothing


-- TODO: instance Read (Sing (a :: Hakaru))


instance Show (Sing (a :: Hakaru)) where
    showsPrec = showsPrec1
    show      = show1
instance Show1 (Sing :: Hakaru -> *) where
    showsPrec1 p s =
        case s of
        SNat            -> showString     "SNat"
        SInt            -> showString     "SInt"
        SProb           -> showString     "SProb"
        SReal           -> showString     "SReal"
        SMeasure  s1    -> showParen_1  p "SMeasure"  s1
        SArray    s1    -> showParen_1  p "SArray"    s1
        SFun      s1 s2 -> showParen_11 p "SFun"      s1 s2
        SData     s1 s2 -> showParen_11 p "SData"     s1 s2


instance SingI 'HNat                            where sing = SNat 
instance SingI 'HInt                            where sing = SInt 
instance SingI 'HProb                           where sing = SProb 
instance SingI 'HReal                           where sing = SReal 
instance (SingI a) => SingI ('HMeasure a)       where sing = SMeasure sing
instance (SingI a) => SingI ('HArray a)         where sing = SArray sing
instance (SingI a, SingI b) => SingI (a ':-> b) where sing = SFun sing sing
-- N.B., must use @(~)@ to delay the use of the type family (it's illegal to put it inline in the instance head).
instance (sop ~ Code t, SingI t, SingI sop) => SingI ('HData t sop) where
    sing = SData sing sing


----------------------------------------------------------------
-- These aren't pattern synonyms (cf., the problems mentioned
-- elsewhere about those), but they're helpful for generating
-- singletons at least.
-- TODO: we might be able to use 'singByProxy' to generate singletons
-- for Symbols? Doesn't work in pattern synonyms, of course.
sUnit :: Sing HUnit
sUnit =
    SData (STyCon sSymbol_Unit)
        (SDone `SPlus` SVoid)

sBool :: Sing HBool
sBool =
    SData (STyCon sSymbol_Bool)
        (SDone `SPlus` SDone `SPlus` SVoid)

-- BUG: what does this "Conflicting definitions for ‘a’" message mean when we try to make this a pattern synonym?
sPair :: Sing a -> Sing b -> Sing (HPair a b)
sPair a b =
    SData (STyCon sSymbol_Pair `STyApp` a `STyApp` b)
        ((SKonst a `SEt` SKonst b `SEt` SDone) `SPlus` SVoid)

sEither :: Sing a -> Sing b -> Sing (HEither a b)
sEither a b =
    SData (STyCon sSymbol_Either `STyApp` a `STyApp` b)
        ((SKonst a `SEt` SDone) `SPlus` (SKonst b `SEt` SDone)
            `SPlus` SVoid)

sList :: Sing a -> Sing (HList a)
sList a =
    SData (STyCon sSymbol_List `STyApp` a)
        (SDone `SPlus` (SKonst a `SEt` SIdent `SEt` SDone) `SPlus` SVoid)

sMaybe :: Sing a -> Sing (HMaybe a)
sMaybe a =
    SData (STyCon sSymbol_Maybe `STyApp` a)
        (SDone `SPlus` (SKonst a `SEt` SDone) `SPlus` SVoid)


----------------------------------------------------------------
data instance Sing (a :: HakaruCon Hakaru) where
    STyCon :: !(Sing s)              -> Sing ('TyCon s :: HakaruCon Hakaru)
    STyApp :: !(Sing a) -> !(Sing b) -> Sing (a ':@ b  :: HakaruCon Hakaru)


instance Eq (Sing (a :: HakaruCon Hakaru)) where
    (==) = eq1
instance Eq1 (Sing :: HakaruCon Hakaru -> *) where
    eq1 x y = maybe False (const True) (jmEq1 x y)
instance JmEq1 (Sing :: HakaruCon Hakaru -> *) where
    jmEq1 (STyCon s)   (STyCon z)   = jmEq1 s z >>= \Refl -> Just Refl
    jmEq1 (STyApp f a) (STyApp g b) =
        jmEq1 f g >>= \Refl ->
        jmEq1 a b >>= \Refl ->
        Just Refl
    jmEq1 _ _ = Nothing


-- TODO: instance Read (Sing (a :: HakaruCon Hakaru))


instance Show (Sing (a :: HakaruCon Hakaru)) where
    showsPrec = showsPrec1
    show      = show1
instance Show1 (Sing :: HakaruCon Hakaru -> *) where
    showsPrec1 p s =
        case s of
        STyCon s1    -> showParen_1  p "STyCon" s1
        STyApp s1 s2 -> showParen_11 p "STyApp" s1 s2


instance SingI ('TyCon s :: HakaruCon Hakaru) where
    sing = STyCon sing
instance (SingI a, SingI b) => SingI ((a ':@ b) :: HakaruCon Hakaru) where
    sing = STyApp sing sing


----------------------------------------------------------------
-- BUG: this whole section is a gross hack! the singletons for
-- symbols conveys no information, and thus is useless as a singleton.
-- 'jmEq_Symb' will always return false; but that should be easier
-- to work around than 'sing' always throwing an undefined-ness
-- exception.

data instance Sing (s :: Symbol) where
    SomeSymbol :: Sing (s :: Symbol)


sSymbol_Bool   :: Sing "Bool"
sSymbol_Bool = SomeSymbol
sSymbol_Unit   :: Sing "Unit"
sSymbol_Unit = SomeSymbol
sSymbol_Pair   :: Sing "Pair"
sSymbol_Pair = SomeSymbol
sSymbol_Either :: Sing "Either"
sSymbol_Either = SomeSymbol
sSymbol_List   :: Sing "List"
sSymbol_List = SomeSymbol
sSymbol_Maybe  :: Sing "Maybe"
sSymbol_Maybe = SomeSymbol


instance Eq (Sing (a :: Symbol)) where
    (==) = eq1
instance Eq1 (Sing :: Symbol -> *) where
    eq1 x y = maybe False (const True) (jmEq1 x y)
instance JmEq1 (Sing :: Symbol -> *) where
    {-
    jmEq1 SSymbol_Bool   SSymbol_Bool   = Just Refl
    jmEq1 SSymbol_Unit   SSymbol_Unit   = Just Refl
    jmEq1 SSymbol_Pair   SSymbol_Pair   = Just Refl
    jmEq1 SSymbol_Either SSymbol_Either = Just Refl
    jmEq1 SSymbol_List   SSymbol_List   = Just Refl
    jmEq1 SSymbol_Maybe  SSymbol_Maybe  = Just Refl
    -}
    jmEq1 _ _ = Nothing


-- TODO: instance Read (Sing (a :: Symbol))


instance Show (Sing (a :: Symbol)) where
    showsPrec = showsPrec1
    show      = show1
instance Show1 (Sing :: Symbol -> *) where
    showsPrec1 _ s = showString "SomeSymbol"
    {-
        case s of
        SSymbol_Bool   -> showString "SSymbol_Bool"
        SSymbol_Unit   -> showString "SSymbol_Unit"
        SSymbol_Pair   -> showString "SSymbol_Pair"
        SSymbol_Either -> showString "SSymbol_Either"
        SSymbol_List   -> showString "SSymbol_List"
        SSymbol_Maybe  -> showString "SSymbol_Maybe"
    -}


instance SingI (s :: Symbol) where
    sing = SomeSymbol


----------------------------------------------------------------
data instance Sing (a :: [[HakaruFun]]) where
    SVoid :: Sing ('[] :: [[HakaruFun]])
    SPlus
        :: !(Sing xs)
        -> !(Sing xss)
        -> Sing ((xs ': xss) :: [[HakaruFun]])


instance Eq (Sing (a :: [[HakaruFun]])) where
    (==) = eq1
instance Eq1 (Sing :: [[HakaruFun]] -> *) where
    eq1 x y = maybe False (const True) (jmEq1 x y)
instance JmEq1 (Sing :: [[HakaruFun]] -> *) where
    jmEq1 SVoid        SVoid        = Just Refl
    jmEq1 (SPlus x xs) (SPlus y ys) =
        jmEq1 x  y  >>= \Refl ->
        jmEq1 xs ys >>= \Refl ->
        Just Refl
    jmEq1 _ _ = Nothing


-- TODO: instance Read (Sing (a :: [[HakaruFun]]))


instance Show (Sing (a :: [[HakaruFun]])) where
    showsPrec = showsPrec1
    show      = show1
instance Show1 (Sing :: [[HakaruFun]] -> *) where
    showsPrec1 p s =
        case s of
        SVoid       -> showString     "SVoid"
        SPlus s1 s2 -> showParen_11 p "SPlus" s1 s2


instance SingI ('[] :: [[HakaruFun]]) where
    sing = SVoid
instance (SingI xs, SingI xss) => SingI ((xs ': xss) :: [[HakaruFun]]) where
    sing = SPlus sing sing


----------------------------------------------------------------
data instance Sing (a :: [HakaruFun]) where
    SDone :: Sing ('[] :: [HakaruFun])
    SEt   :: !(Sing x) -> !(Sing xs) -> Sing ((x ': xs) :: [HakaruFun])


instance Eq (Sing (a :: [HakaruFun])) where
    (==) = eq1
instance Eq1 (Sing :: [HakaruFun] -> *) where
    eq1 x y = maybe False (const True) (jmEq1 x y)
instance JmEq1 (Sing :: [HakaruFun] -> *) where
    jmEq1 SDone      SDone      = Just Refl
    jmEq1 (SEt x xs) (SEt y ys) =
        jmEq1 x  y  >>= \Refl ->
        jmEq1 xs ys >>= \Refl ->
        Just Refl
    jmEq1 _ _ = Nothing


-- TODO: instance Read (Sing (a :: [HakaruFun]))


instance Show (Sing (a :: [HakaruFun])) where
    showsPrec = showsPrec1
    show      = show1
instance Show1 (Sing :: [HakaruFun] -> *) where
    showsPrec1 p s =
        case s of
        SDone     -> showString     "SDone"
        SEt s1 s2 -> showParen_11 p "SEt" s1 s2


instance SingI ('[] :: [HakaruFun]) where
    sing = SDone
instance (SingI x, SingI xs) => SingI ((x ': xs) :: [HakaruFun]) where
    sing = SEt sing sing


----------------------------------------------------------------
data instance Sing (a :: HakaruFun) where
    SIdent :: Sing 'I
    SKonst :: !(Sing a) -> Sing ('K a)


instance Eq (Sing (a :: HakaruFun)) where
    (==) = eq1
instance Eq1 (Sing :: HakaruFun -> *) where
    eq1 x y = maybe False (const True) (jmEq1 x y)
instance JmEq1 (Sing :: HakaruFun -> *) where
    jmEq1 SIdent     SIdent     = Just Refl
    jmEq1 (SKonst a) (SKonst b) = jmEq1 a b >>= \Refl -> Just Refl
    jmEq1 _          _          = Nothing


-- TODO: instance Read (Sing (a :: HakaruFun))


instance Show (Sing (a :: HakaruFun)) where
    showsPrec = showsPrec1
    show      = show1
instance Show1 (Sing :: HakaruFun -> *) where
    showsPrec1 p s =
        case s of
        SIdent    -> showString    "SIdent"
        SKonst s1 -> showParen_1 p "SKonst" s1

instance SingI 'I where
    sing = SIdent
instance (SingI a) => SingI ('K a) where
    sing = SKonst sing

----------------------------------------------------------------
----------------------------------------------------------------
toSing :: Hakaru -> (forall a. Sing (a :: Hakaru) -> r) -> r
toSing HNat         k = k SNat
toSing HInt         k = k SInt
toSing HProb        k = k SProb
toSing HReal        k = k SReal
toSing (HMeasure a) k = toSing a $ \a' -> k (SMeasure a')
toSing (HArray   a) k = toSing a $ \a' -> k (SArray   a')
toSing (a :-> b)    k =
    toSing a $ \a' ->
    toSing b $ \b' ->
    k (SFun a' b')
toSing (HData t xss) k =
    error "TODO: toSing{HData}"
    {-
    -- BUG: the type index for @t' :: Sing t@ must match the one for @xss' :: Sing (Code t)@
    toSing_Con  t  $ \t' ->
    toSing_Code xss $ \xss' ->
    k (SData t' xss')
    -}

toSing_Con
    :: HakaruCon Hakaru
    -> (forall t. Sing (t :: HakaruCon Hakaru) -> r) -> r
toSing_Con (TyCon s)  k = toSing_Symbol s $ \s' -> k (STyCon s')
toSing_Con (t :@ a) k =
    toSing_Con t $ \t' ->
    toSing     a $ \a' ->
    k (STyApp t' a')

toSing_Symbol
    :: Symbol
    -> (forall s. Sing (s :: Symbol) -> r) -> r
toSing_Symbol s k = k SomeSymbol

toSing_Code
    :: [[HakaruFun]]
    -> (forall xss. Sing (xss :: [[HakaruFun]]) -> r) -> r
toSing_Code []       k = k SVoid
toSing_Code (xs:xss) k =
    toSing_Struct xs  $ \xs'  ->
    toSing_Code   xss $ \xss' ->
    k (SPlus xs' xss')

toSing_Struct
    :: [HakaruFun]
    -> (forall xs. Sing (xs :: [HakaruFun]) -> r) -> r
toSing_Struct []     k = k SDone
toSing_Struct (x:xs) k =
    toSing_Fun    x  $ \x'  ->
    toSing_Struct xs $ \xs' ->
    k (SEt x' xs')

toSing_Fun
    :: HakaruFun
    -> (forall x. Sing (x :: HakaruFun) -> r) -> r
toSing_Fun I     k = k SIdent
toSing_Fun (K a) k = toSing a $ \a' -> k (SKonst a')

----------------------------------------------------------------
----------------------------------------------------------- fin.
