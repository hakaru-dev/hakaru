{-# LANGUAGE RankNTypes, DeriveDataTypeable, StandaloneDeriving #-}
{-# OPTIONS -W #-}

module Language.Hakaru.Types where

import Data.Dynamic
import Control.Monad.Primitive
import qualified System.Random.MWC as MWC

type PRNG m = MWC.Gen (PrimState m)

-- Basic types for conditioning and conditioned sampler
data Density a = Lebesgue !a | Discrete !a deriving Typeable
type Cond = Maybe Dynamic

fromDiscrete :: Density t -> t
fromDiscrete (Discrete a) = a
fromDiscrete _            = error "got a non-discrete sampler"

fromLebesgue :: Density t -> t
fromLebesgue (Lebesgue a) = a
fromLebesgue  _           = error "got a discrete sampler"

fromDensity :: Density t -> t
fromDensity (Discrete a) = a
fromDensity (Lebesgue a) = a

type LogLikelihood = Double
data Dist a = Dist {logDensity :: Density a -> LogLikelihood,
                    distSample :: (PrimMonad m) => PRNG m -> m (Density a)}
deriving instance Typeable1 Dist
