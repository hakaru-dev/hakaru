module Language.Hakaru.Runtime.Prelude where

import qualified System.Random.MWC               as MWC
import qualified System.Random.MWC.Distributions as MWCD
import           Data.Number.Natural


normal :: Double -> Double -> MWC.GenIO -> IO Double
normal mu sd g = MWCD.normal mu sd g

real_ :: Rational -> Double
real_ = fromRational

prob_ :: NonNegativeRational -> Double
prob_ = fromRational . fromNonNegativeRational

run :: MWC.GenIO -> (MWC.GenIO -> IO a) -> IO a
run g k = k g

test1 :: MWC.GenIO -> IO Double
test1 = normal (real_ 0) (prob_ 3)

runTest1 :: IO Double
runTest1 = do
   g <- MWC.create
   run g test1
