{-# LANGUAGE RankNTypes, DeriveDataTypeable, StandaloneDeriving #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.18
-- |
-- Module      :  Language.Hakaru.Sampling.Types
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- Basic types for conditioning and conditioned sampler
----------------------------------------------------------------
module Language.Hakaru.Sampling.Types where

import Data.Dynamic
import Control.Monad.Primitive
import qualified System.Random.MWC as MWC
----------------------------------------------------------------

type PRNG m = MWC.Gen (PrimState m)

data Density a = Lebesgue !a | Discrete !a
    deriving Typeable

type Cond = Maybe Dynamic

fromDiscrete :: Density t -> t
fromDiscrete (Discrete a) = a
fromDiscrete _            = error "fromDiscrete: got a non-discrete sampler"

fromLebesgue :: Density t -> t
fromLebesgue (Lebesgue a) = a
fromLebesgue  _           = error "fromLebesgue: got a discrete sampler"

fromDensity :: Density t -> t
fromDensity (Discrete a) = a
fromDensity (Lebesgue a) = a

type LogLikelihood = Double
data Dist a = Dist
    { logDensity :: Density a -> LogLikelihood
    , distSample :: (Functor m, PrimMonad m) => PRNG m -> m (Density a)
    }
deriving instance Typeable Dist

----------------------------------------------------------------
----------------------------------------------------------- fin.