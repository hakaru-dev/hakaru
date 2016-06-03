{-# LANGUAGE DataKinds
           , PolyKinds
           , TypeOperators
           , GADTs
           , TypeFamilies
           , FlexibleInstances
           , Rank2Types
           , UndecidableInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.05.28
-- |
-- Module      :  Language.Hakaru.Types.Sing
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Singleton types for the @Hakaru@ kind, and a decision procedure
-- for @Hakaru@ type-equality.
----------------------------------------------------------------
module Language.Hakaru.Types.Sing
    ( Sing(..)
    , SingI(..)
    -- * Some helpful shorthands for \"built-in\" datatypes
    -- ** Constructing singletons
    , sBool
    , sUnit
    , sPair
    , sEither
    , sList
    , sMaybe
    -- ** Destructing singletons
    , sUnMeasure
    , sUnArray
    , sUnPair
    , sUnEither
    , sUnList
    , sUnMaybe
    -- ** Singletons for `Symbol`
    , sSymbol_Bool
    , sSymbol_Unit
    , sSymbol_Pair
    , sSymbol_Either
    , sSymbol_List
    , sSymbol_Maybe
    ) where

import qualified GHC.TypeLits as TL
-- TODO: should we use @(Data.Type.Equality.:~:)@ everywhere instead of our own 'TypeEq'?
import Unsafe.Coerce

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Types.DataKind
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

{-
-- TODO: we'd much rather have something like this, to prove that
-- we have a SingI instance for /every/ @a :: Hakaru@. Is there any
-- possible way of actually doing this?

class SingI1 (kproxy :: KProxy k) where
    sing1 :: Sing (a :: k)
    -- or, if it helps at all:
    -- > sing1 :: forall (a :: k). proxy a -> Sing a

instance SingI1 ('KProxy :: KProxy Hakaru) where
    sing1 = undefined
-}

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

sUnMeasure :: Sing ('HMeasure a) -> Sing a
sUnMeasure (SMeasure a) = a

sUnArray :: Sing ('HArray a) -> Sing a
sUnArray (SArray a) = a

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

sUnPair :: Sing (HPair a b) -> (Sing a, Sing b)
sUnPair (SData (STyApp (STyApp (STyCon _) a) b) _) = (a,b)
sUnPair _ = error "sUnPair: the impossible happened"

sEither :: Sing a -> Sing b -> Sing (HEither a b)
sEither a b =
    SData (STyCon sSymbol_Either `STyApp` a `STyApp` b)
        ((SKonst a `SEt` SDone) `SPlus` (SKonst b `SEt` SDone)
            `SPlus` SVoid)

sUnEither :: Sing (HEither a b) -> (Sing a, Sing b)
sUnEither (SData (STyApp (STyApp (STyCon _) a) b) _) = (a,b)
sUnEither _ = error "sUnEither: the impossible happened"

sList :: Sing a -> Sing (HList a)
sList a =
    SData (STyCon sSymbol_List `STyApp` a)
        (SDone `SPlus` (SKonst a `SEt` SIdent `SEt` SDone) `SPlus` SVoid)

sUnList :: Sing (HList a) -> Sing a
sUnList (SData (STyApp (STyCon _) a) _) = a
sUnList _ = error "sUnList: the impossible happened"

sMaybe :: Sing a -> Sing (HMaybe a)
sMaybe a =
    SData (STyCon sSymbol_Maybe `STyApp` a)
        (SDone `SPlus` (SKonst a `SEt` SDone) `SPlus` SVoid)

sUnMaybe :: Sing (HMaybe a) -> Sing a
sUnMaybe (SData (STyApp (STyCon _) a) _) = a
sUnMaybe _ = error "sUnMaybe: the impossible happened"

----------------------------------------------------------------
data instance Sing (a :: HakaruCon) where
    STyCon :: !(Sing s)              -> Sing ('TyCon s :: HakaruCon)
    STyApp :: !(Sing a) -> !(Sing b) -> Sing (a ':@ b  :: HakaruCon)


instance Eq (Sing (a :: HakaruCon)) where
    (==) = eq1
instance Eq1 (Sing :: HakaruCon -> *) where
    eq1 x y = maybe False (const True) (jmEq1 x y)
instance JmEq1 (Sing :: HakaruCon -> *) where
    jmEq1 (STyCon s)   (STyCon z)   = jmEq1 s z >>= \Refl -> Just Refl
    jmEq1 (STyApp f a) (STyApp g b) =
        jmEq1 f g >>= \Refl ->
        jmEq1 a b >>= \Refl ->
        Just Refl
    jmEq1 _ _ = Nothing


-- TODO: instance Read (Sing (a :: HakaruCon))


instance Show (Sing (a :: HakaruCon)) where
    showsPrec = showsPrec1
    show      = show1
instance Show1 (Sing :: HakaruCon -> *) where
    showsPrec1 p (STyCon s1)    = showParen_1  p "STyCon" s1
    showsPrec1 p (STyApp s1 s2) = showParen_11 p "STyApp" s1 s2


instance TL.KnownSymbol s => SingI ('TyCon s :: HakaruCon) where
    sing = STyCon sing
instance (SingI a, SingI b) => SingI ((a ':@ b) :: HakaruCon) where
    sing = STyApp sing sing


----------------------------------------------------------------
-- | N.B., in order to bring the 'TL.KnownSymbol' dictionary into
-- scope, you need to pattern match on the 'SingSymbol' constructor
-- (similar to when we need to match on 'Refl' explicitly). In
-- general you'll want to do this with an at-pattern so that you
-- can also have a variable name for passing the value around (e.g.
-- to be used as an argument to 'TL.symbolVal').
data instance Sing (s :: Symbol) where
    SingSymbol :: TL.KnownSymbol s => Sing (s :: Symbol)

sSymbol_Bool   :: Sing "Bool"
sSymbol_Bool   = SingSymbol
sSymbol_Unit   :: Sing "Unit"
sSymbol_Unit   = SingSymbol
sSymbol_Pair   :: Sing "Pair"
sSymbol_Pair   = SingSymbol
sSymbol_Either :: Sing "Either"
sSymbol_Either = SingSymbol
sSymbol_List   :: Sing "List"
sSymbol_List   = SingSymbol
sSymbol_Maybe  :: Sing "Maybe"
sSymbol_Maybe  = SingSymbol


instance Eq (Sing (s :: Symbol)) where
    (==) = eq1
instance Eq1 (Sing :: Symbol -> *) where
    eq1 x y = maybe False (const True) (jmEq1 x y)
instance JmEq1 (Sing :: Symbol -> *) where
     jmEq1 x@SingSymbol y@SingSymbol
        | TL.symbolVal x == TL.symbolVal y = Just (unsafeCoerce Refl)
        | otherwise                        = Nothing

-- TODO: is any meaningful Read (Sing (a :: Symbol)) instance possible?

instance Show (Sing (s :: Symbol)) where
    showsPrec = showsPrec1
    show      = show1
instance Show1 (Sing :: Symbol -> *) where
    showsPrec1 _ s@SingSymbol =
        showParen True
            ( showString "SingSymbol :: Sing "
            . showString (show $ TL.symbolVal s)
            )

-- Alas, this requires UndecidableInstances
instance TL.KnownSymbol s => SingI (s :: Symbol) where
    sing = SingSymbol


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
    showsPrec1 _ SVoid         = showString     "SVoid"
    showsPrec1 p (SPlus s1 s2) = showParen_11 p "SPlus" s1 s2


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
    showsPrec1 _ SDone       = showString     "SDone"
    showsPrec1 p (SEt s1 s2) = showParen_11 p "SEt" s1 s2


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
    showsPrec1 _ SIdent      = showString    "SIdent"
    showsPrec1 p (SKonst s1) = showParen_1 p "SKonst" s1

instance SingI 'I where
    sing = SIdent
instance (SingI a) => SingI ('K a) where
    sing = SKonst sing

----------------------------------------------------------------
----------------------------------------------------------- fin.
