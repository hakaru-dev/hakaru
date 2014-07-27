{-# LANGUAGE NoMonomorphismRestriction, ConstraintKinds #-}
module Tests.Tests ( tests ) where

import Prelude hiding (Real)

import qualified Tests.ImportanceSampler as IS
import qualified Tests.Metropolis as MH

import Data.Ratio
import Language.Hakaru.Syntax
-- import Language.Hakaru.Lambda

import Distribution.TestSuite
import Distribution.TestSuite.QuickCheck

-- While this might be "right", this sure isn't a nice way to write
-- programs!  Looks like our embedding is sub-optimal.
prog_mixture :: (Mochastic m, Type m Bool, MEq m Bool, Type m Real) => m (Measure Bool)
prog_mixture = 
  unconditioned (bern (real (1 % 2)))                `bind` \c ->
  conditioned (unbool c (normal  (real 1) (real 1))
                        (uniform (real 0) (real 4))) `bind` \_ ->
  ret c
    
eq :: Double -> Bool
eq x = x == x

qtest = testProperty "STUB test" eq

tests :: IO [Test]
tests = return [ qtest ]
