{-# LANGUAGE DataKinds
           , PolyKinds
           , StandaloneDeriving
           , DeriveDataTypeable
           , ScopedTypeVariables
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.06.24
-- |
-- Module      :  Language.Hakaru.Syntax.DataKind
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- A data-kind for the universe of Hakaru types.
----------------------------------------------------------------
module Language.Hakaru.Syntax.DataKind
    ( Hakaru(..)
    , HakaruFun(..)
    , HakaruCon(..) 
    , Symbol
    , Code 
    , HakaruType, HBool, HUnit, HPair, HEither, HList, HMaybe

    ) where

import Data.Typeable (Typeable)
import GHC.TypeLits (Symbol) 
import Unsafe.Coerce

----------------------------------------------------------------
-- | The universe/kind of Hakaru types. N.B., the @star@ parameter
-- will always be @*@ when used as a data-kind.
data Hakaru 
    = HNat
    | HInt
    | HProb -- ^ Non-negative real numbers (not the [0,1] interval!)
    | HReal -- ^ The real projective line (includes +/- infinity)
    | HMeasure Hakaru
    | HArray Hakaru
    | HFun Hakaru Hakaru

    -- TODO: replace HUnit, HPair, HEither with the Embed stuff
    {-
    | HBool
    | HUnit
    | HPair Hakaru Hakaru
    | HEither Hakaru Hakaru
    -}

    -- The lists-of-lists are sum-of-products functors. The application
    -- form allows us to unroll fixpoints: @HMu sop ~= sop :$ HMu sop@.
    | [[HakaruFun]] :$ Hakaru
    | HTag (HakaruCon Hakaru) [[HakaruFun]]

    -- Used in "Language.Hakaru.Expect"
    -- TODO: replace HList with the Embed stuff
    -- | HList Hakaru

    -- Used in "Language.Hakaru.Sample"
    -- TODO: replace HMaybe with the Embed stuff
    -- | HMaybe Hakaru
   deriving (Show)

-- Huge hack - but there is no way to produce a value level term of type Symbol
-- other than through the fromSing function in TypeEq, so this should be safe.
instance Show Symbol where show x = show (unsafeCoerce x :: String)

-- | The identity and constant functors on @Hakaru*@. This gives
-- us limited access to type-variables in @Hakaru*@, for use in
-- recursive sums-of-products. Notably, however, it only allows a
-- single variable (namely the one bound by the closest binder) so
-- it can't encode mutual recursion or other non-local uses of
-- multiple binders.
--
-- Products and sums are represented as lists, so they aren't
-- in this datatype.
data HakaruFun = Id | K Hakaru
   deriving (Show)

-- | The kind of hakaru constructors - simply a name, with 0 or more
-- arguements. It parametric in arguement - this is especially useful when you
-- need a singleton of the constructor, but not the types in the arguements. The
-- arguement positions are necessary to do variable binding in Code. Symbol is
-- the kind of "type level strings".
data HakaruCon a = HCon Symbol | HakaruCon a :@ a 
   deriving (Show)

-- | The Code type family allows users to extend the Hakaru language by adding
-- new types. The right hand side is the sum-of-products representation of that
-- type. See the built-in types for examples. 
type family Code (a :: HakaruCon Hakaru) :: [[HakaruFun]]

-- Built-in types 
type instance Code (HCon "Unit") = '[ '[] ]
type instance Code (HCon "Maybe" :@ a) = '[ '[] , '[ K a ] ]
type instance Code (HCon "List" :@ a) = '[ '[] , '[ K a, Id ]]
type instance Code (HCon "Pair" :@ a :@ b) = '[ '[ K a, K b ]]
type instance Code (HCon "Either" :@ a :@ b) = '[ '[K a], '[K b]]
type instance Code (HCon "Bool") = '[ '[], '[] ]



{-
BUG: Fully expand these types because the type checker for some reason
doesn't reduce the type family applications which prevents the use of these
type synonyms in class instance heads.  Any type synonym created with
`HakaruType' will suffer the same issue, so type synonyms must be written out
by hand - or copied from the GHC pretty printer, which will happily reduce
things in the repl, even in the presence of quantified type variables. 
   >:kind! forall a b . HakaruType (HCon "Pair" :@ a :@ b)
   forall a b . HakaruType (HCon "Pair" :@ a :@ b) :: Hakaru
   = forall (a :: Hakaru) (b :: Hakaru).
     'HTag (('HCon "Pair" ':@ a) ':@ b) '['['K a, 'K b]]
-}

type HakaruType t = HTag t (Code t)

{-
type HBool = HakaruType (HCon "Bool")
type HUnit = HTag (HCon "Unit") '[ '[] ]
type HPair a b = HakaruType (HCon "Pair" :@ a :@ b)
type HEither a b = HakaruType (HCon "Either" :@ a :@ b)
type HList a = HakaruType (HCon "List" :@ a)
type HMaybe a = HakaruType (HCon "Maybe" :@ a)
-}
type HBool = 'HTag ('HCon "Bool") '[ '[], '[]]
type HUnit = 'HTag ('HCon "Unit") '[ '[]]
type HPair a b = 'HTag (('HCon "Pair" ':@ a) ':@ b) '[ '[ 'K a, 'K b]]
type HEither a b = 'HTag (('HCon "Either" ':@ a) ':@ b) '[ '[ 'K a], '[ 'K b]]
type HList a = 'HTag ('HCon "List" ':@ a) '[ '[], '[ 'K a, 'Id]]
type HMaybe a = 'HTag ('HCon "Maybe" ':@ a) '[ '[], '[ 'K a]]




-- N.B., The @Proxy@ type from "Data.Proxy" is polykinded, so it
-- works for @Hakaru*@ too. However, it is _not_ Typeable!

-- TODO: these instances are only used in
-- 'Language.Hakaru.Simplify.closeLoop'; it would be cleaner to
-- remove these instances and reimplement that function to work
-- without them.
deriving instance Typeable 'HNat
deriving instance Typeable 'HInt
deriving instance Typeable 'HReal
deriving instance Typeable 'HProb
deriving instance Typeable 'HMeasure
deriving instance Typeable 'HArray
deriving instance Typeable 'HFun
deriving instance Typeable 'HTag
deriving instance Typeable '(:$) 
deriving instance Typeable 'Id
deriving instance Typeable 'K
deriving instance Typeable 'HCon 
deriving instance Typeable '(:@)

----------------------------------------------------------------
----------------------------------------------------------- fin.
