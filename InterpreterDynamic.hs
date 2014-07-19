{-# LANGUAGE RankNTypes, NoMonomorphismRestriction, BangPatterns #-}
{-# OPTIONS -W #-}

module InterpreterDynamic where

-- This is an interpreter that's like Interpreter except conditioning is
-- checked at run time rather than by static types.  In other words, we allow
-- models to be compiled whose conditioned parts do not match the observation
-- inputs.  In exchange, we get to make Measure an instance of Monad, and we
-- can express models whose number of observations is unknown at compile time.

import Types (Cond(..), CSampler(CSampler))
import RandomChoice (normal_rng, chooseIndex)
import Mixture (Prob, empty, point, Mixture(..))
import Sampler (Sampler, deterministic, smap, sbind)

import System.Random
import Data.Monoid
import Data.Ix
import Data.Dynamic
import Data.List
import Control.Monad
import qualified Data.Map.Strict as M

import qualified Data.Number.LogFloat as LF

dirac :: (Eq a, Typeable a) => a -> CSampler a
dirac x = CSampler c where
  c Unconditioned = deterministic (point x 1)
  c (Discrete y) = case fromDynamic y of
    Just y  -> deterministic (if x == y then point x 1 else empty)
    Nothing -> error "dirac: did not get data from dynamic source"
  c _ = error "dirac: got a non-discrete sampler"

bern :: Double -> CSampler Bool
bern theta | 0 <= theta && theta <= 1 = CSampler c where
  c Unconditioned = \g0 -> case randomR (0, 1) g0 of
    (x, g) -> (point (x <= theta) 1, g)
  c (Discrete y) = case fromDynamic y of
    Just y -> deterministic (point y (LF.logFloat (if y then theta else 1 - theta)))
    Nothing -> error "bern: did not get data from dynamic source"
  c _ = error "bern: got a non-discrete sampler"
bern theta = error ("bernoulli: invalid parameter " ++ show theta)

uniform :: (Fractional a, Real a, Random a, Typeable a) => a -> a -> CSampler a
uniform lo hi | lo < hi = CSampler c where
  c Unconditioned = \g0 -> case randomR (lo,hi) g0 of
    (x, g) -> (point x 1, g)
  c (Lebesgue y) = case fromDynamic y of
    Just y -> deterministic (if lo < y && y < hi then point y density else empty)
    Nothing -> error "uniform: did not get data from dynamic source"
  c _ = error "uniform: got a discrete sampler"
  density = fromRational (toRational (recip (hi - lo)))
uniform _ _ = error "uniform: invalid parameters"

uniformD :: (Ix a, Random a, Typeable a) => a -> a -> CSampler a
uniformD lo hi | lo <= hi = CSampler c where
  c Unconditioned = \g0 -> case randomR (lo,hi) g0 of
    (x, g) -> (point x 1, g)
  c (Discrete y) = case fromDynamic y of
    Just y -> deterministic (if lo <= y && y <= hi then point y density else empty)
    Nothing -> error "uniformD: did not get data from dynamic source"
  c _ = error "uniformD: got a non-discrete sampler"
  density = recip (fromInteger (toInteger (rangeSize (lo,hi))))
uniformD _ _ = error "uniformD: invalid parameters"

poisson :: (Integral a, Typeable a) => Double -> CSampler a
poisson !l | 0 <= l = CSampler c where
  c Unconditioned = \g0 ->
    let probs = exp (-l) : zipWith (\k p -> p * l / k) [1..] probs
        (k, g) = chooseIndex probs g0
    in (point (fromInteger (toInteger k)) 1, g)
  c (Discrete k) = case fromDynamic k of
    Just k ->
      deterministic
        (if 0 <= k then point k (LF.logToLogFloat (-l)
                                 * LF.logFloat l ^ k
                                 / product (map fromIntegral [1..k]))
                   else empty)
    Nothing -> error "poisson: did not get data from dynamic source"
  c _ = error "poisson: got a non-discrete sampler"
poisson _ = error "poisson: invalid parameter"

normal :: (Real a, Floating a, Random a, Typeable a) => a -> a -> CSampler a
normal !mean !std | std > 0 = CSampler c where
  c Unconditioned = \g0 -> let (x, g) = normal_rng mean std g0
                           in (point (mean + std * x) 1, g)
  c (Lebesgue y) = case fromDynamic y of
    Just y ->
      let density  = exp (square ((y - mean) / std) / (-2)) / std / sqrt (2 * pi)
          square y = y * y
      in deterministic (point y (fromRational (toRational density))) -- TODO: use log-density and LogFloat directly
    Nothing -> error "normal: did not get data from dynamic source"
  c _ = error "normal: got a discrete sampler"
normal _ _ = error "normal: invalid parameters"

categorical :: (Typeable a, Eq a) => [(a, Prob)] -> CSampler a
categorical list = CSampler c where
  peak :: LF.LogFloat
  peak = maximum (map snd list)
  total :: Double
  (total, list') = mapAccumL f 0 list
    where f acc (a,b) = (acc', (a, (b', acc')))
            where b' = b/peak
                  acc' :: Double
                  acc' = acc + LF.fromLogFloat b'
  c Unconditioned =
    \g0 -> let (p, g) = randomR (0, total) g0
               (elem, _) : _ = filter (\(_,(_,p0)) -> p <= p0) list' in
           (point elem 1, g)
  c (Discrete y) = case fromDynamic y of
    Just y -> deterministic (maybe empty (point y . (/ LF.logFloat total) . fst)
                                         (lookup y list'))
    Nothing -> error "categorical: did not get data from dynamic source"
  c _ = error "categorical: got a non-discrete sampler"

-- Conditioned sampling
newtype Measure a = Measure { unMeasure :: [Cond] -> Sampler (a, [Cond]) }

bind :: Measure a -> (a -> Measure b) -> Measure b
bind measure continuation =
  Measure (\conds ->
    sbind (unMeasure measure conds)
          (\(a,conds) -> unMeasure (continuation a) conds))

instance Monad Measure where
  return x = Measure (\conds -> deterministic (point (x,conds) 1))
  (>>=)    = bind

conditioned, unconditioned :: CSampler a -> Measure a
conditioned   (CSampler f) = Measure (\(cond:conds) -> smap (\a->(a,conds)) (f cond         ))
unconditioned (CSampler f) = Measure (\      conds  -> smap (\a->(a,conds)) (f Unconditioned))

factor :: Prob -> Measure ()
factor p = Measure (\conds -> deterministic (point ((), conds) p))

-- Drivers for testing
finish :: Mixture (a, [Cond]) -> Mixture a
finish (Mixture m) = Mixture (M.mapKeysMonotonic (\(a,[]) -> a) m)

sample :: (Ord a) => Int -> Measure a -> [Cond] -> IO (Mixture a)
sample !n measure conds = go n empty where
  once = getStdRandom (unMeasure measure conds)
  go 0 m = return m
  go n m = once >>= \result -> go (n - 1) $! mappend m (finish result)

sample_ :: (Ord a, Show a) => Int -> Measure a -> [Cond] -> IO ()
sample_ !n measure conds = replicateM_ n (once >>= pr) where
  once = getStdRandom (unMeasure measure conds)
  pr   = print . finish

logit :: Floating a => a -> a
logit !x = 1 / (1 + exp (- x))

