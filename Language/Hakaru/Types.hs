{-# LANGUAGE RankNTypes, BangPatterns, DeriveDataTypeable, StandaloneDeriving #-}
{-# OPTIONS -W #-}

module Language.Hakaru.Types where

import Data.Dynamic
import System.Random

-- Basic types for conditioning and conditioned sampler
data Density a = Lebesgue !a | Discrete !a deriving Typeable
type Cond = Maybe Dynamic

fromDiscrete (Discrete a) = a
fromDiscrete _            = error "got a non-discrete sampler"

fromLebesgue (Lebesgue a) = a
fromLebesgue  _           = error "got a discrete sampler"

fromDensity (Discrete a) = a
fromDensity (Lebesgue a) = a

type LogLikelihood = Double
data Dist a = Dist {logDensity :: Density a -> LogLikelihood,
                    distSample :: forall g.
                                  RandomGen g => g -> (Density a, g)}
deriving instance Typeable1 Dist