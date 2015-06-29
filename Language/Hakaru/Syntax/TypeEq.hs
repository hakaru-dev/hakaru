{-# LANGUAGE 
    QuasiQuotes
  , TemplateHaskell

  -- Needed by spliced code 
  , PolyKinds
  , UndecidableInstances
  , DataKinds
  , GADTs
  , ScopedTypeVariables
  , StandaloneDeriving
  #-}

-- Singletons generates orphan instances warnings 
{-# OPTIONS_GHC -Wall -fwarn-tabs -fno-warn-orphans #-}

-- DEBUG
-- {-# OPTIONS_GHC -ddump-splices #-} 

----------------------------------------------------------------
--                                                    2015.06.28
-- |
-- Module      :  Language.Hakaru.Syntax.TypeEq
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Singleton types for the @Hakaru*@ kind, and a decision procedure
-- for @Hakaru*@ type-equality. 
----------------------------------------------------------------
module Language.Hakaru.Syntax.TypeEq 
    ( module Language.Hakaru.Syntax.TypeEq
    , Sing(..), SingI(..), SingKind(..), SDecide(..), (:~:)(..)
    ) where

-- import Data.Proxy
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
-- | Singleton types for the kind of Hakaru types. We need to use
-- this instead of 'Proxy' in order to implement 'jmEq'.
data Sing :: Hakaru * -> * where
    SNat     :: Sing 'HNat
    SInt     :: Sing 'HInt
    SProb    :: Sing 'HProb
    SReal    :: Sing 'HReal
    SMeasure :: Sing a -> Sing ('HMeasure a)
    SArray   :: Sing a -> Sing ('HArray a)
    SFun     :: Sing a -> Sing b -> Sing ('HFun a b)
    SBool    :: Sing 'HBool
    SUnit    :: Sing 'HUnit
    SPair    :: Sing a -> Sing b -> Sing ('HPair a b)
    SEither  :: Sing a -> Sing b -> Sing ('HEither a b)
    SList    :: Sing a -> Sing ('HList a)
    SMaybe   :: Sing a -> Sing ('HMaybe a)
    {-
    -- TODO
    SMu  :: SingSOPHakaruFun sop -> Sing ('HMu sop)
    SApp :: SingSOPHakaruFun sop -> Sing a -> Sing (sop ':$ a)
    STag :: Proxy a -> SingSOPHakaruFun sop -> Sing ('HTag a sop)
    -}

deriving instance Eq   (Sing a)
-- BUG: deriving instance Read (Sing a)
deriving instance Show (Sing a)

{-
data SingHakaruFun :: Hakaru * -> * where
    SId :: SingHakaruFun 'Id
    SK  :: SingHakaru a -> SingHakaruFun ('K a)

deriving instance Eq   (SingHakaruFun a)
deriving instance Read (SingHakaruFun a)
deriving instance Show (SingHakaruFun a)
-}


----------------------------------------------------------------
-- | A class for automatically generating the singleton for a given
-- Hakaru type.
class    SingI (a :: Hakaru *)            where sing :: Sing a
instance SingI 'HNat                      where sing = SNat 
instance SingI 'HInt                      where sing = SInt 
instance SingI 'HProb                     where sing = SProb 
instance SingI 'HReal                     where sing = SReal 
instance SingI 'HBool                     where sing = SBool 
instance SingI 'HUnit                     where sing = SUnit 
instance (SingI a) => SingI ('HMeasure a) where sing = SMeasure sing
instance (SingI a) => SingI ('HArray a)   where sing = SArray sing
instance (SingI a) => SingI ('HList a)    where sing = SList sing
instance (SingI a) => SingI ('HMaybe a)   where sing = SMaybe sing
instance (SingI a, SingI b) => SingI ('HFun a b)    where sing = SFun sing sing
instance (SingI a, SingI b) => SingI ('HPair a b)   where sing = SPair sing sing
instance (SingI a, SingI b) => SingI ('HEither a b) where sing = SEither sing sing
{-
-- TODO
instance SingI ('HMu sop)    where sing = SMu singSOPHakaruFun
instance SingI (sop ':$ a)   where sing = SApp singSOPHakaruFun sing
instance SingI ('HTag a sop) where sing = STag Proxy singSOPHakaruFun
-}


{-
-- I think it's impossible to actually implement a function of this
-- type (i.e., without any type constraints on @a@). That is, even
-- though for every @a :: Hakaru*@ there is some value of type @Sing
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
jmEq :: Sing a -> Sing b -> Maybe (TypeEq a b)
jmEq SNat             SNat             = Just Refl
jmEq SInt             SInt             = Just Refl
jmEq SProb            SProb            = Just Refl
jmEq SReal            SReal            = Just Refl
jmEq SBool            SBool            = Just Refl
jmEq SUnit            SUnit            = Just Refl
jmEq (SMeasure a)     (SMeasure b)     = jmEq a  b  >>= \Refl -> Just Refl
jmEq (SArray   a)     (SArray   b)     = jmEq a  b  >>= \Refl -> Just Refl
jmEq (SList    a)     (SList    b)     = jmEq a  b  >>= \Refl -> Just Refl
jmEq (SMaybe   a)     (SMaybe   b)     = jmEq a  b  >>= \Refl -> Just Refl
jmEq (SFun     a1 a2) (SFun     b1 b2) = jmEq a1 b1 >>= \Refl -> 
                                         jmEq a2 b2 >>= \Refl -> Just Refl
jmEq (SPair    a1 a2) (SPair    b1 b2) = jmEq a1 b1 >>= \Refl -> 
                                         jmEq a2 b2 >>= \Refl -> Just Refl
jmEq (SEither  a1 a2) (SEither  b1 b2) = jmEq a1 b1 >>= \Refl -> 
                                         jmEq a2 b2 >>= \Refl -> Just Refl
{-
-- TODO
jmEq (SMu  a)   (SMu  a)
jmEq (SApp a b) (SApp a b)
jmEq (STag a b) (STag a b)
-}
jmEq _ _ = Nothing

----------------------------------------------------------------
----------------------------------------------------------- fin.