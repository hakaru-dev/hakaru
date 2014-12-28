{-# LANGUAGE DeriveDataTypeable, Rank2Types #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Any (Any(Any, unAny)) where

import Language.Hakaru.Syntax (Lambda, Mochastic)
import Data.Typeable (Typeable)

newtype Any a = Any
  { unAny :: forall repr. (Lambda repr, Mochastic repr) => repr a }
  deriving Typeable
  -- beware GHC 7.8 https://ghc.haskell.org/trac/ghc/wiki/GhcKinds/PolyTypeable
