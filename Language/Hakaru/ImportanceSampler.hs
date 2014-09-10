{-# LANGUAGE RankNTypes, NoMonomorphismRestriction, BangPatterns #-}
{-# OPTIONS -W #-}

module Language.Hakaru.ImportanceSampler where

-- This is an interpreter that's like Interpreter except conditioning is
-- checked at run time rather than by static types.  In other words, we allow
-- models to be compiled whose conditioned parts do not match the observation
-- inputs.  In exchange, we get to make Measure an instance of Monad, and we
-- can express models whose number of observations is unknown at compile time.

import Language.Hakaru.Types
import Language.Hakaru.Mixture (Prob, empty, point, Mixture(..))
import Language.Hakaru.Sampler (Sampler, deterministic, smap, sbind)

import qualified System.Random.MWC as MWC
import Control.Monad.Primitive
import Data.Monoid
import Data.Dynamic
import System.IO.Unsafe
import qualified Data.Map.Strict as M

import qualified Data.Number.LogFloat as LF

-- Conditioned sampling
newtype Measure a = Measure { unMeasure :: [Cond] -> Sampler (a, [Cond]) }

bind :: Measure a -> (a -> Measure b) -> Measure b
bind measure continuation =
  Measure (\conds ->
    sbind (unMeasure measure conds)
          (\(a,cds) -> unMeasure (continuation a) cds))

instance Monad Measure where
  return x = Measure (\conds -> deterministic (point (x,conds) 1))
  (>>=)    = bind

updateMixture :: Typeable a => Cond -> Dist a -> Sampler a
updateMixture (Just cond) dist =
    case fromDynamic cond of
      Just y  -> deterministic (point (fromDensity y) density)
          where density = LF.logToLogFloat $ logDensity dist y
      Nothing -> error "did not get data from dynamic source"
updateMixture Nothing     dist = \g -> do e <- distSample dist g
                                          return $ point (fromDensity e) 1
    
conditioned, unconditioned :: Typeable a => Dist a -> Measure a
conditioned   dist = Measure (\(cond:conds) -> smap (\a->(a,conds))
                                               (updateMixture cond    dist))
unconditioned dist = Measure (\      conds  -> smap (\a->(a,conds))
                                               (updateMixture Nothing dist))

factor :: Prob -> Measure ()
factor p = Measure (\conds -> deterministic (point ((), conds) p))

condition :: Eq b => Measure (a, b) -> b -> Measure a
condition m b' =
    Measure (\ conds -> 
      sbind (unMeasure m conds)
            (\ ((a,b), cds) ->
                 deterministic (if b==b' then point (a,cds) 1 else empty)))

-- Drivers for testing
finish :: Mixture (a, [Cond]) -> Mixture a
finish (Mixture m) = Mixture (M.mapKeysMonotonic (\(a,[]) -> a) m)

empiricalMeasure :: (PrimMonad m, Ord a) => Int -> Measure a -> [Cond] -> m (Mixture a)
empiricalMeasure !n measure conds = do
  gen <- MWC.create
  go n gen empty
    where once = unMeasure measure conds
          go 0 _ m = return m
          go k g m = once g >>= \result -> go (k - 1) g $! mappend m (finish result)

sample :: Measure a -> [Cond] -> IO [(a, Prob)]
sample measure conds = do
  gen <- MWC.create
  unsafeInterleaveIO $ sampleNext gen
 where once = unMeasure measure conds
       mixToTuple = head . M.toList . unMixture
       sampleNext g = do
          u <- once g
          let x = mixToTuple (finish u)
          xs <- unsafeInterleaveIO $ sampleNext g
          return (x : xs)

logit :: Floating a => a -> a
logit !x = 1 / (1 + exp (- x))
