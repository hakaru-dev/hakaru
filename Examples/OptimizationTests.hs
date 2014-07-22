{-# LANGUAGE RankNTypes, NoMonomorphismRestriction, BangPatterns #-}

-- The following are program transformations I would like us to be able to do
-- They might not require many rules
--
-- NOTE: no support for beta, gamma, dirichlet distributions yet, hence
--       some of these examples won't work

import InterpreterDynamic
import Types
import Mixture

import Data.Dynamic
import Control.Monad
import qualified Data.Map.Strict as M

beta = undefined

-- Turn observe into constant

prog1_before = return $ conditioned (normal 0 1) 

run1_before  = sample 10 prog1_before conds
  where conds = [Lebesgue (toDyn (4 :: Double))]

prog1_after = return 4

run1_after  = sample 10 prog1_after []

-- Conjugacy rewrite

coin2 = True
prog2_before = do bias <- unconditioned (beta 1 1)
                  conditioned (bern bias)
                  return bias

run2_before = sample 10 prog2_before [Discrete (toDyn coin2)]

prog2_after = do bias <- unconditioned (if coin2
                                        then beta 2 1
                                        else beta 1 2)
                 return bias

run2_after = sample 10 prog2_after []

-- Transform Monte Carlo into Sequential Monte Carlo

prog3_before = do coin1 <- unconditioned (bern 0.5)
                  coin2 <- unconditioned $ if coin1
                                           then bern 0.9
                                           else bern 0.2
                  return coin2

run3_before = sample 10 prog3_before []

prog3_after1 = do coin1 <- unconditioned (bern 0.5)
                  return coin1

run3_after1  = sample 10 prog3_after1 []

prog3_after2 prev = do coin1 <- unconditioned $ categorical $ M.toList $ unMixture prev
                       coin2 <- unconditioned $ if coin1
                                                then bern 0.9
                                                else bern 0.2
                       return coin2

run3_after2 = do
  prev <- run3_after1
  sample 10 (prog3_after2 prev) []

-- Transform loop through lifted inference

coin4 = True
flips = 20
prog4_before = do bias <- unconditioned (beta 1 1)
                  replicateM flips (conditioned (bern bias))
                  return bias

run4_before = sample 10 prog4_before $ replicate flips (Discrete (toDyn coin4))

prog4_after = do bias <- unconditioned (if coin4
                                        then beta (1 + flips) 1
                                        else beta 1 (1 + flips))
                 return bias
run4_after = sample 10 prog4_after []