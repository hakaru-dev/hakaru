{-# LANGUAGE KindSignatures
           , DataKinds
           , DeriveDataTypeable
           , Rank2Types
           , ExistentialQuantification
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}

module Language.Hakaru.Any
    ( Any(Any, unAny)
    , Any'
    , AnySimplifiable(AnySimplifiable, unAnySimplifiable)
    ) where

import Data.Typeable (Typeable)

import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.PrettyPrint
import Language.Hakaru.Simplifiable (Simplifiable)


newtype Any (a :: Hakaru) = Any { unAny :: Any' a }
  deriving Typeable
  -- beware GHC 7.8 https://ghc.haskell.org/trac/ghc/wiki/GhcKinds/PolyTypeable

{-
-- TODO: fix this up again. There's some strange existential-type issues about just using 'pretty'/'prettyPrec'...
asPrettyPrint :: PrettyPrint a -> PrettyPrint a
asPrettyPrint = id

instance Show (Any a) where
  show        (Any a) = show        (asPrettyPrint a)
  showsPrec p (Any a) = showsPrec p (asPrettyPrint a)
  showList    as      = showList    [asPrettyPrint a | Any a <- as]
-}


type Any' (a :: Hakaru) = forall abt. (ABT abt) => abt '[] a

data AnySimplifiable =
    forall (a :: Hakaru) . (Simplifiable a) =>
    AnySimplifiable { unAnySimplifiable :: Any' a }
    deriving Typeable
