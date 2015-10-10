{-# LANGUAGE DeriveDataTypeable, Rank2Types, ExistentialQuantification #-}
{-# OPTIONS -Wall -Werror #-}

module Language.Hakaru.Any (Any(Any, unAny), Any',
  AnySimplifiable(AnySimplifiable, unAnySimplifiable)) where

import Language.Hakaru.Syntax (Lambda, Mochastic, Integrate)
-- import Language.Hakaru.Embed (Embed) 
import Language.Hakaru.PrettyPrint (PrettyPrint)
import Language.Hakaru.Util.Pretty (Pretty(pretty))
import Language.Hakaru.Simplifiable (Simplifiable)
import Data.Typeable (Typeable)

newtype Any a = Any { unAny :: Any' a }
  deriving Typeable
  -- beware GHC 7.8 https://ghc.haskell.org/trac/ghc/wiki/GhcKinds/PolyTypeable

asPrettyPrint :: PrettyPrint a -> PrettyPrint a
asPrettyPrint = id

instance Show (Any a) where
  show        (Any a) = show        (asPrettyPrint a)
  showsPrec p (Any a) = showsPrec p (asPrettyPrint a)
  showList    as      = showList    [asPrettyPrint a | Any a <- as]

instance Pretty (Any a) where
  pretty      (Any a) = pretty      (asPrettyPrint a)


type Any' a =
  forall repr. (Mochastic repr, Integrate repr, Lambda repr
  {-
  , Embed repr
  -}
  ) => repr a

data AnySimplifiable = forall a. (Simplifiable a) =>
                       AnySimplifiable { unAnySimplifiable :: Any' a }
  deriving Typeable
