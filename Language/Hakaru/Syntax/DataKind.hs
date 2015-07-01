{-# LANGUAGE DataKinds
           , PolyKinds
           , TypeOperators
           , TypeFamilies
           , StandaloneDeriving
           , DeriveDataTypeable
           , ScopedTypeVariables
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.06.30
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
    (
    -- * The core definition of Hakaru types
      Hakaru(..)
    , HakaruFun(..)
    , HakaruCon(..) 
    -- *
    , Symbol
    , Code
    , HData'
    -- * Some \"built-in\" types
    -- Naturally, these aren't actually built-in, otherwise they'd
    -- be part of the 'Hakaru' data-kind.
    , HBool, HUnit, HPair, HEither, HList, HMaybe
    ) where

import Data.Typeable (Typeable)
import GHC.TypeLits (Symbol)
import Unsafe.Coerce

----------------------------------------------------------------
-- HACK: there is no way to produce a value level term of type
-- Symbol other than through the fromSing function in TypeEq, so
-- this should be safe.
instance Show Symbol where
    show x = show (unsafeCoerce x :: String)

instance Read Symbol where
    readsPrec = unsafeCoerce (readsPrec :: Int -> ReadS String)


----------------------------------------------------------------
infixr 0 :->

-- | The universe\/kind of Hakaru types.
data Hakaru
    = HNat -- ^ The natural numbers; aka, the non-negative integers.

    -- TODO: in terms of Summate (etc), do we consider this to include omega?
    -- | The integers.
    | HInt

    -- | Non-negative real numbers. Unlike what you might expect,
    -- this is /not/ restructed to the @[0,1]@ interval!
    | HProb

    -- | The affinely extended real number line. That is, the real
    -- numbers extended with positive and negative infinities.
    | HReal

    -- TODO: so much of our code has to distinguish between monadic and pure stuff. Maybe we should just break this out into a separate larger universe?
    -- | The measure monad
    | HMeasure !Hakaru

    -- | The built-in type for uniform arrays.
    | HArray !Hakaru

    -- | The type of Hakaru functions.
    | !Hakaru :-> !Hakaru

    -- | A user-defined polynomial datatype. Each such type is
    -- specified by a \"tag\" (the @HakaruCon Hakaru@) which names
    -- the type, and a sum-of-product representation of the type
    -- itself.
    | HData !(HakaruCon Hakaru) [[HakaruFun]]

    deriving (Read, Show)


-- N.B., The @Proxy@ type from "Data.Proxy" is polykinded, so it
-- works for @Hakaru@ too. However, it is _not_ Typeable!
--
-- TODO: all the Typeable instances in this file are only used in
-- 'Language.Hakaru.Simplify.closeLoop'; it would be cleaner to
-- remove these instances and reimplement that function to work
-- without them.

deriving instance Typeable 'HNat
deriving instance Typeable 'HInt
deriving instance Typeable 'HProb
deriving instance Typeable 'HReal
deriving instance Typeable 'HMeasure
deriving instance Typeable 'HArray
deriving instance Typeable '(:->)
deriving instance Typeable 'HData


----------------------------------------------------------------
-- | The identity and constant functors on 'Hakaru'. This gives
-- us limited access to type-variables in @Hakaru@, for use in
-- recursive sums-of-products. Notably, however, it only allows a
-- single variable (namely the one bound by the closest binder) so
-- it can't encode mutual recursion or other non-local uses of
-- multiple binders. We also cannot encode non-regular recursive
-- types (aka nested datatypes), like rose trees. To do that, we'd
-- need to allow any old functor here.
--
-- Products and sums are represented as lists in the 'Hakaru'
-- data-kind itself, so they aren't in this datatype.
data HakaruFun = I | K !Hakaru
    deriving (Read, Show)

deriving instance Typeable 'I
deriving instance Typeable 'K


----------------------------------------------------------------
-- | The kind of user-defined Hakaru type constructors, which serves
-- as a tag for the sum-of-products representation of the user-defined
-- Hakaru type. The head of the 'HakaruCon' is a symbolic name, and
-- the rest are arguments to that type constructor. The @a@ parameter
-- is parametric, which is especially useful when you need a singleton
-- of the constructor. The argument positions are necessary to do
-- variable binding in Code. 'Symbol' is the kind of \"type level
-- strings\".
data HakaruCon a = HCon !Symbol | HakaruCon a :@ a
    deriving (Read, Show)
infixl 0 :@

deriving instance Typeable 'HCon
deriving instance Typeable '(:@)


-- | The Code type family allows users to extend the Hakaru language
-- by adding new types. The right hand side is the sum-of-products
-- representation of that type. See the \"built-in\" types for examples.
type family   Code (a :: HakaruCon Hakaru) :: [[HakaruFun]]
type instance Code ('HCon "Bool")               = '[ '[], '[] ]
type instance Code ('HCon "Unit")               = '[ '[] ]
type instance Code ('HCon "Maybe"  ':@ a)       = '[ '[] , '[ 'K a ] ]
type instance Code ('HCon "List"   ':@ a)       = '[ '[] , '[ 'K a, 'I ] ]
type instance Code ('HCon "Pair"   ':@ a ':@ b) = '[ '[ 'K a, 'K b ] ]
type instance Code ('HCon "Either" ':@ a ':@ b) = '[ '[ 'K a ], '[ 'K b ] ]


-- | A helper type alias for simplifying type signatures for
-- user-provided Hakaru types.
--
-- BUG: you cannot use this alias when defining other type aliases!
-- For some reason the type checker doesn't reduce the type family
-- applications, which prevents the use of these type synonyms in
-- class instance heads. Any type synonym created with 'HData''
-- will suffer the same issue, so type synonyms must be written out
-- by hand— or copied from the GHC pretty printer, which will happily
-- reduce things in the repl, even in the presence of quantified
-- type variables.
type HData' t = 'HData t (Code t)
{-
   >:kind! forall a b . HData' (HCon "Pair" :@ a :@ b)
   forall a b . HData' (HCon "Pair" :@ a :@ b) :: Hakaru
   = forall (a :: Hakaru) (b :: Hakaru).
     'HData (('HCon "Pair" ':@ a) ':@ b) '['['K a, 'K b]]

type HBool       = HData' (HCon "Bool")
type HUnit       = HData' (HCon "Unit")
type HPair   a b = HData' (HCon "Pair"   :@ a :@ b)
type HEither a b = HData' (HCon "Either" :@ a :@ b)
type HList   a   = HData' (HCon "List"   :@ a)
type HMaybe  a   = HData' (HCon "Maybe"  :@ a)
-}

type HBool       = 'HData ('HCon "Bool") '[ '[], '[] ]
type HUnit       = 'HData ('HCon "Unit") '[ '[] ]
type HPair   a b = 'HData (('HCon "Pair"   ':@ a) ':@ b) '[ '[ 'K a, 'K b] ]
type HEither a b = 'HData (('HCon "Either" ':@ a) ':@ b) '[ '[ 'K a], '[ 'K b] ]
type HList   a   = 'HData ('HCon "List"    ':@ a) '[ '[], '[ 'K a, 'I] ]
type HMaybe  a   = 'HData ('HCon "Maybe"   ':@ a) '[ '[], '[ 'K a] ]

----------------------------------------------------------------
----------------------------------------------------------- fin.
