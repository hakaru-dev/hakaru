{-# LANGUAGE BangPatterns #-}
module RandomChoice where

import System.Random
import Mixture
import Data.Maybe (fromMaybe)
import Data.List (findIndex)
import qualified Data.Vector.Unboxed as U
import qualified Data.Map.Strict as M
import qualified Data.Number.LogFloat as LF

marsaglia :: (RandomGen g, Random a, Ord a, Floating a) => g -> ((a, a), g)
marsaglia g0 = -- "Marsaglia polar method"
  let (x, g1) = randomR (-1,1) g0
      (y, g ) = randomR (-1,1) g1
      s       = x * x + y * y
      q       = sqrt ((-2) * log s / s)
  in if 1 >= s && s > 0 then ((x * q, y * q), g) else marsaglia g

choose :: (RandomGen g) => Mixture k -> g -> (k, Prob, g)
choose (Mixture m) g0 =
  let peak = maximum (M.elems m)
      unMix = M.map (LF.fromLogFloat . (/peak)) m
      total = M.foldl' (+) (0::Double) unMix
      (p, g) = randomR (0, total) g0
      f !k !v b !p0 = let p1 = p0 + v in if p <= p1 then k else b p1
      err p0 = error ("choose: failure p0=" ++ show p0 ++
                      " total=" ++ show total ++
                      " size=" ++ show (M.size m))
  in (M.foldrWithKey f err unMix 0, LF.logFloat total * peak, g)

chooseIndex :: (RandomGen g) => [Double] -> g -> (Int, g)
chooseIndex probs g0 =
  let (p, g) = random g0
      k = fromMaybe (error ("chooseIndex: failure p=" ++ show p))
                    (findIndex (p <=) (scanl1 (+) probs))
  in (k, g)

-- Borrowed from package math-functions
factorial :: Int -> Double
factorial n
    | n < 0     = error "Statistics.Math.factorial: negative input"
    | n <= 1    = 1
    | n <= 170  = U.product $ U.map fromIntegral $ U.enumFromTo 2 n
    | otherwise = 1 / 0

-- Borrowed from package math-functions
lnFact :: Int -> Double
lnFact n
    | n <= 14   = log (factorial n)
    | otherwise = (x - 0.5) * log x - x + 9.1893853320467e-1 + z / x
    where x = fromIntegral (n + 1)
          y = 1 / (x * x)
          z = ((-(5.95238095238e-4 * y) + 7.936500793651e-4) * y -
               2.7777777777778e-3) * y + 8.3333333333333e-2

-- Makes use of Atkinson's algorithm as described in:
-- Monte Carlo Statistical Methods pg. 55
--
-- Further discussion at:
-- http://www.johndcook.com/blog/2010/06/14/generating-poisson-random-values/
poisson_rng :: (RandomGen g) => Double -> g -> (Int, g)
poisson_rng lambda g0 = make_poisson g0
   where smu = sqrt lambda
         b  = 0.931 + 2.53*smu
         a  = -0.059 + 0.02483*b
         vr = 0.9277 - 3.6224/(b - 2)
         arep  = 1.1239 + 1.1368/(b-3.4)
         lnlam = log lambda

         make_poisson :: (RandomGen g) => g -> (Int,g)
         make_poisson g = let (u, g1) = randomR (-0.5,0.5) g
                              (v, g2) = randomR (0,1) g1
                              us = 0.5 - abs u
                              k = floor $ (2*a / us + b)*u + lambda + 0.43 in
                          case (us, v, k) of
                            (us,v,k) | us >= 0.07 && v <= vr -> (k, g2)
                            (_,_, k) | k < 0 -> make_poisson g2
                            (us,v,k) | us <= 0.013 && v > us -> make_poisson g2
                            (us,v,k) | accept_region us v k -> (k, g2)
                            _        -> make_poisson g2

         accept_region us v k = log (v * arep / (a/(us*us)+b)) <=
                                -lambda + (fromIntegral k)*lnlam - lnFact k

-- Direct implementation of  "A Simple Method for Generating Gamma Variables"
-- by George Marsaglia and Wai Wan Tsang.
gamma_rng :: (RandomGen g) => Double -> Double -> g -> (Double, g)
gamma_rng = undefined
-- Algorithm recommends inlining normal generator