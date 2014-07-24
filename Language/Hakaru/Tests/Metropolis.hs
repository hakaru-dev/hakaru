{-# LANGUAGE BangPatterns #-}

module Language.Hakaru.Tests.Metropolis where

import Data.Dynamic

import Language.Hakaru.Types
import Language.Hakaru.Lambda
import Language.Hakaru.Metropolis
import Language.Hakaru.Distribution (bern, normal, uniform, beta)

import Test.QuickCheck.Monadic
import Distribution.TestSuite.QuickCheck

prog_mixture :: Measure Bool
prog_mixture = do
  c <- unconditioned (bern 0.5)
  _ <- conditioned (ifThenElse c (normal  1 1)
                                 (uniform 0 3))
  return c

test_mixture :: IO [Bool]
test_mixture = mcmc prog_mixture [Just (toDyn (Lebesgue (-2) :: Density Double))]

prog_multiple_conditions :: Measure Double
prog_multiple_conditions = do
  b <- unconditioned (beta 1 1)
  _ <- conditioned (bern b)
  _ <- conditioned (bern b)
  return b

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
