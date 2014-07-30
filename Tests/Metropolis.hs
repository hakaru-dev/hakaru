{-# LANGUAGE BangPatterns #-}

module Tests.Metropolis where

import Data.Dynamic

import Language.Hakaru.Types
import Language.Hakaru.Lambda
import Language.Hakaru.Metropolis
import Language.Hakaru.Distribution (bern, normal, uniform, beta)

-- import Test.QuickCheck.Monadic
-- import Distribution.TestSuite.QuickCheck
import Tests.Models

test_mixture :: IO [Bool]
test_mixture = mcmc prog_mixture [Just (toDyn (Lebesgue (-2) :: Density Double))]

test_multiple_conditions :: IO [Double]
test_multiple_conditions = do
  mcmc prog_multiple_conditions [Just (toDyn (Discrete True)),
                                 Just (toDyn (Discrete False))]

prog_two_normals :: Measure Bool
prog_two_normals = unconditioned (bern 0.5) `bind` \coin ->
       ifThenElse coin (conditioned (normal 0 1))
                       (conditioned (normal 100 1)) `bind` \_ ->
       return coin

test_two_normals :: IO [Bool]
test_two_normals = mcmc prog_two_normals [Just (toDyn (Lebesgue 1 :: Density Double))]

test_normal :: IO [Double]
test_normal = mcmc (unconditioned (normal 1 3)) []

prog_joint =  do
  bias <- unconditioned $ beta 1 1
  coin <- unconditioned $ bern bias
  return (bias, coin)

prog_condition = condition prog_joint True

test_condition :: IO [Double]
test_condition = mcmc prog_condition []

