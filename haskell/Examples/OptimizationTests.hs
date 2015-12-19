{-# LANGUAGE NoMonomorphismRestriction #-}

-- The following are program transformations I would like us to be able to do
-- They might not require many rules
--
-- NOTE: no support for beta, gamma, dirichlet distributions yet, hence
--       some of these examples won't work

module Examples.OptimizationTests where

import Language.Hakaru.Types
import Language.Hakaru.Distribution
import Language.Hakaru.Metropolis

import Data.Dynamic
import Control.Monad
import qualified Data.Map.Strict as M

-- Turn observe into constant

prog1_before = return $ conditioned (normal 0 1) 

run1_before  = sample prog1_before conds
  where conds = [Just (toDyn (Lebesgue 4 :: Density Double))]

prog1_after = return 4

run1_after  = sample prog1_after []

-- Conjugacy rewrite

coin2 = True
prog2_before = do
    bias <- unconditioned (beta 1 1)
    coin <- conditioned (bern bias)
    return (coin, bias)

run2_before = sample prog2_before [Just (toDyn (Discrete coin2))] 

prog2_after = do
    coin <- conditioned (bern 0.5)
    bias <- unconditioned (if coin2 then beta 2 1 else beta 1 2)
    return (coin, bias)

run2_after = sample prog2_after [Just (toDyn (Discrete coin2))] 

-- Transform Monte Carlo into Sequential Monte Carlo

prog3_before = do
    coin1 <- unconditioned (bern 0.5)
    coin2 <- unconditioned $ if coin1 then bern 0.9 else bern 0.2
    return coin2

run3_before  = sample prog3_before []

prog3_after1 = unconditioned (bern 0.5)

run3_after1  = sample prog3_after1 []

prog3_after2 prev = do
    coin1 <- unconditioned $ categorical prev
    coin2 <- unconditioned $ if coin1 then bern 0.9 else bern 0.2
    return coin2

run3_after2 = do
    prev <- run3_after1
    sample (prog3_after2 (take 10 prev)) []

-- Transform loop through lifted inference

coin4 = True
flips = 20
prog4_before = do
    bias <- unconditioned (beta 1 1)
    replicateM flips (conditioned (bern bias))
    return bias

run4_before =
    sample prog4_before $ replicate flips (Just (toDyn (Discrete coin4)))

prog4_after = do
    bias <- unconditioned (if coin4
        then beta (1 + flips) 1
        else beta 1 (1 + flips))
    return bias
run4_after = sample prog4_after []
