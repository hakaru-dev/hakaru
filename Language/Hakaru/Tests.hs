{-# LANGUAGE NoMonomorphismRestriction #-}
module Language.Hakaru.Tests ( tests ) where

import qualified Language.Hakaru.Tests.ImportanceSampler as IS
import qualified Language.Hakaru.Tests.Metropolis as MH

import Distribution.TestSuite
import Distribution.TestSuite.QuickCheck

qtest = testProperty "STUB test" True

tests :: IO [Test]
tests = return [ qtest ]
