{-# LANGUAGE BangPatterns #-}

module Language.Hakaru.Tests.ImportanceSampler where

import Data.Dynamic
import Language.Hakaru.Types
import Language.Hakaru.Lambda
import Language.Hakaru.ImportanceSampler

import Test.QuickCheck.Monadic

-- Some example/test programs in our language
prog_mixture :: Measure Bool
prog_mixture = do
  c <- unconditioned (bern 0.5)
  _ <- conditioned (ifThenElse c (normal (lit (1 :: Double)) (lit 1))
                                 (uniform (lit 0) (lit 3)))
  return c

test_mixture :: IO ()
test_mixture = sample_ 3 prog_mixture conds >>
       putChar '\n' >>
       empiricalMeasure 1000 prog_mixture conds >>=
       print
  where conds = [Lebesgue (toDyn (2 :: Double))]

prog_dup :: Measure (Bool, Bool)
prog_dup = do
  let c = unconditioned (bern 0.5)
  x <- c
  y <- c
  return (x,y)

prog_dbn :: Measure Bool
prog_dbn = do
  s0 <- unconditioned (bern 0.75)
  s1 <- unconditioned (if s0 then bern 0.75 else bern 0.25)
  _  <- conditioned   (if s1 then bern 0.90 else bern 0.10)
  s2 <- unconditioned (if s1 then bern 0.75 else bern 0.25)
  _  <- conditioned   (if s2 then bern 0.90 else bern 0.10)
  return s2

test_dbn :: IO ()
test_dbn = sample_ 10 prog_dbn conds >>
           putChar '\n' >>
           empiricalMeasure 1000 prog_dbn conds >>=
           print 
  where conds = [Discrete (toDyn (True :: Bool)),
                 Discrete (toDyn (True :: Bool))]

prog_hmm :: Integer -> Measure Bool
prog_hmm n = do
  s <- unconditioned (bern 0.75) 
  loop_hmm n s

loop_hmm :: Integer -> (Bool -> Measure Bool)
loop_hmm !numLoops s = do
    _ <- conditioned   (if s then bern 0.90 else bern 0.10)
    u <- unconditioned (if s then bern 0.75 else bern 0.25)
    if (numLoops > 1) then loop_hmm (numLoops - 1) u 
                      else return s

test_hmm :: IO ()
test_hmm = sample_ 10 (prog_hmm 2) conds >>
           putChar '\n' >>
           empiricalMeasure 1000 (prog_hmm 2) conds >>=
           print 
  where conds = [Discrete (toDyn (True :: Bool)),
                 Discrete (toDyn (True :: Bool))]

prog_carRoadModel :: Measure (Double, Double)
prog_carRoadModel = do
  speed <- unconditioned (uniform 5 15)
  let z0 = lit 0 
  _ <- conditioned    (normal z0 1)
  z1 <- unconditioned (normal (z0 + speed) 1)
  _ <- conditioned    (normal z1 1)
  z2 <- unconditioned (normal (z1 + speed) 1)	
  _ <- conditioned    (normal z2 1)
  z3 <- unconditioned (normal (z2 + speed) 1)	
  _ <- conditioned    (normal z3 1)
  z4 <- unconditioned (normal (z3 + speed) 1)	
  return (z4, z3)

test_carRoadModel :: IO ()
test_carRoadModel = sample_ 10 prog_carRoadModel conds >>
                    putChar '\n' >>
                    empiricalMeasure 1000 prog_carRoadModel conds >>=
                    print 
  where conds = [Lebesgue (toDyn (0 :: Double)),
                 Lebesgue (toDyn (11 :: Double)), 
                 Lebesgue (toDyn (19 :: Double)),
                 Lebesgue (toDyn (33 :: Double))]

prog_categorical :: Measure Bool
prog_categorical = do 
  rain <- unconditioned (categorical [(True, 0.2), (False, 0.8)]) 
  sprinkler <- unconditioned (if rain
                              then bern 0.01 else bern 0.4)
  _ <- conditioned (if rain
                    then (if sprinkler then bern 0.99 else bern 0.8)
	            else (if sprinkler then bern 0.90 else bern 0.1))
  return rain

test_categorical :: IO ()
test_categorical = sample_ 10 prog_categorical conds >>
           putChar '\n' >>
           empiricalMeasure 1000 prog_categorical conds >>=
           print 
  where conds = [Discrete (toDyn (True :: Bool))]

prog_multiple_conditions :: Measure Double
prog_multiple_conditions = do
  b <- unconditioned (beta 1 1)
  _ <- conditioned (bern b)
  _ <- conditioned (bern b)
  return b
