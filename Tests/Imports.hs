-- This internal module is used by Language.Hakaru.Simplify to parse strings
-- as Hakaru code.  It exports just the names that those strings may use.

module Tests.Imports
  ( ()(..), (,)(..), Either(..), Bool(..), Int, Num(..)
  , Fractional(..), Floating(..), ($), (^^)
  , Any(Any), AnySimplifiable(AnySimplifiable)
  , module Language.Hakaru.Syntax
  , module Language.Hakaru.Embed 
  ) where

import GHC.Tuple (()(..), (,)(..))
import Language.Hakaru.Syntax
import Language.Hakaru.Any (Any(Any), AnySimplifiable(AnySimplifiable))
import Language.Hakaru.Embed 
