{-# LANGUAGE BangPatterns #-}

module Language.Hakaru.Examples.Tests where

import Data.Dynamic
import Language.Hakaru.Types
import qualified Language.Hakaru.ImportanceSampler as IS
import qualified Language.Hakaru.Metropolis as MH

import Language.Hakaru.Lambda
import Language.Hakaru.Util.Visual

-- Some example/test programs in our language
test_mixture :: Measure Bool
test_mixture = do
  c <- unconditioned (bern 0.5)
  _ <- conditioned (ifThenElse c (normal (lit (1 :: Double)) (lit 1))
                                 (uniform (lit 0) (lit 3)))
  return c

test_dup :: Measure (Bool, Bool)
test_dup = do
  let c = unconditioned (MH.bern 0.5)
  x <- c
  y <- c
  return (x,y)

test_dbn :: Measure Bool
test_dbn = do
  s0 <- unconditioned (bern 0.75)
  s1 <- unconditioned (if s0 then bern 0.75 else bern 0.25)
  _  <- conditioned (if s1 then bern 0.9 else bern 0.1)
  s2 <- unconditioned (if s1 then bern 0.75 else bern 0.25)
  _  <- conditioned (if s2 then bern 0.9 else bern 0.1)
  return s2

test_hmm :: Integer -> Measure Bool
test_hmm n = do
  s <- unconditioned (bern 0.75) 
  loop_hmm n s

loop_hmm :: Integer -> (Bool -> Measure Bool)
loop_hmm !numLoops s = do
    _ <- conditioned (if s then bern 0.9 else bern 0.1)
    u <- unconditioned (if s then bern 0.75 else bern 0.25)
    if (numLoops > 1) then loop_hmm (numLoops - 1) u 
                      else return s

test_carRoadModel :: Measure (Double, Double)
test_carRoadModel = do
  speed <- unconditioned (uniform (lit (5::Double)) (lit (15::Double)))
  let z0 = lit 0 
  _ <- conditioned (normal (z0 :: Double) (lit 1))
  z1 <- unconditioned (normal (z0 + speed) (lit 1))
  _ <- conditioned (normal z1 (lit 1))
  z2 <- unconditioned (normal (z1 + speed) (lit 1))	
  _ <- conditioned (normal z2 (lit 1))
  z3 <- unconditioned (normal (z2 + speed) (lit 1))	
  _ <- conditioned (normal z3 (lit 1))
  z4 <- unconditioned (normal (z3 + speed) (lit 1))	
  return (z4, z3)

test_categorical :: Measure Bool
test_categorical = do 
  rain <- unconditioned (categorical [(lit True, 0.2), (lit False, 0.8)]) 
  sprinkler <- unconditioned (if rain then bern 0.01 else bern 0.4)
  _ <- conditioned (if rain then (if sprinkler then bern 0.99 else bern 0.8)
	                else (if sprinkler then bern 0.9 else bern 0.1))
  return rain

-- printing test results
main_mixture :: IO ()
main_mixture = IS.sample_ 3 test_mixture conds >>
       putChar '\n' >>
       IS.empiricalMeasure 1000 test_mixture conds >>=
       print
  where conds = [Lebesgue (toDyn (2 :: Double))]

main_dbn :: IO ()
main_dbn = IS.sample_ 10 test_dbn conds >>
           putChar '\n' >>
           IS.empiricalMeasure 1000 test_dbn conds >>=
           print 
  where conds = [Discrete (toDyn (True :: Bool)),
                 Discrete (toDyn (True :: Bool))]

main_hmm :: IO ()
main_hmm = IS.sample_ 10 (test_hmm 2) conds >>
           putChar '\n' >>
           IS.empiricalMeasure 1000 (test_hmm 2) conds >>=
           print 
  where conds = [Discrete (toDyn (True :: Bool)),
                 Discrete (toDyn (True :: Bool))]

main_carRoadModel :: IO ()
main_carRoadModel = IS.sample_ 10 test_carRoadModel conds >>
                    putChar '\n' >>
                    IS.empiricalMeasure 1000 test_carRoadModel conds >>=
                    print 
  where conds = [Lebesgue (toDyn (0 :: Double)),
                 Lebesgue (toDyn (11 :: Double)), 
                 Lebesgue (toDyn (19 :: Double)),
                 Lebesgue (toDyn (33 :: Double))]

main_categorical :: IO ()
main_categorical = IS.sample_ 10 test_categorical conds >>
           putChar '\n' >>
           IS.empiricalMeasure 1000 test_categorical conds >>=
           print 
  where conds = [Discrete (toDyn (True :: Bool))]


test_multiple_conditions :: Measure Double
test_multiple_conditions = do
  b <- unconditioned (MH.beta 1 1)
  _ <- conditioned (MH.bern b)
  _ <- conditioned (MH.bern b)
  return b

main_run_test :: IO (Bool, MH.Database, MH.Likelihood)
main_run_test = MH.run test_mixture [Just (toDyn (-2 :: Double))]

main_test :: IO [Bool]
main_test = MH.mcmc test_mixture [Just (toDyn (-2 :: Double))]

test_two_normals :: Measure Bool
test_two_normals = unconditioned (bern 0.5) `bind` \coin ->
       ifThenElse coin (conditioned (normal 0 1))
                       (conditioned (normal 100 1)) `bind` \_ ->
       return coin

main_test2 :: IO [Bool]
main_test2 = MH.mcmc test_two_normals [Just (toDyn (1 :: Double))]

test_viz :: IO ()
test_viz = do
  l <- MH.mcmc test_multiple_conditions [Just (toDyn True), Just (toDyn False)]
  viz 10000 ["beta"] (map return l)

test_viz_2 :: IO ()
test_viz_2 = do
  l <- MH.mcmc (unconditioned (normal 1 3)) [] :: IO [Double]
  viz 10000 ["normal"] (map return l)
