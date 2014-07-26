{-# LANGUAGE NoMonomorphismRestriction #-}
module Tests.Tests ( tests ) where

import qualified Tests.ImportanceSampler as IS
import qualified Tests.Metropolis as MH

import Distribution.TestSuite
import Distribution.TestSuite.QuickCheck

eq :: Double -> Bool
eq x = x == x

qtest = testProperty "STUB test" eq

tests :: IO [Test]
tests = return [ qtest ]
