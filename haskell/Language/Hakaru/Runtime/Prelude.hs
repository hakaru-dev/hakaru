{-# LANGUAGE GADTs
           , DataKinds
           , OverloadedStrings
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs -fsimpl-tick-factor=1000 #-}
module Language.Hakaru.Runtime.Prelude where

import qualified System.Random.MWC               as MWC
import qualified System.Random.MWC.Distributions as MWCD
import           Data.Number.Natural
import qualified Control.Monad                   as M
import           Prelude hiding ((>>=))



normal :: Double -> Double -> MWC.GenIO -> IO Double
normal mu sd g = MWCD.normal mu sd g

(>>=) :: (MWC.GenIO -> IO a)
      -> (a -> MWC.GenIO -> IO b)
      -> MWC.GenIO
      -> IO b
m >>= f = \g -> m g M.>>= flip f g

real_ :: Rational -> Double
real_ = fromRational

prob_ :: NonNegativeRational -> Double
prob_ = fromRational . fromNonNegativeRational

run :: Show a => MWC.GenIO -> (MWC.GenIO -> IO a) -> IO ()
run g k = k g M.>>= print
