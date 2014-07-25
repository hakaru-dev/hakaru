{-# LANGUAGE NoMonomorphismRestriction #-}
module Tests ( tests ) where

--import qualified Language.Hakaru.Tests.ImportanceSampler as IS
--import qualified Language.Hakaru.Tests.Metropolis as MH

import Distribution.TestSuite
import Distribution.TestSuite.QuickCheck

eq :: Double -> Bool
eq x = x == x

qtest = testProperty "STUB test" eq

tests :: IO [Test]
tests = return [ qtest ]
