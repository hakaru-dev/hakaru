{-# LANGUAGE BangPatterns #-}
module Language.Hakaru.RandomChoice where

import System.Random
import Language.Hakaru.Mixture
import Data.Maybe (fromMaybe)
import Data.List (findIndex, foldl')
import Numeric.SpecFunctions
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

normal_rng :: (Real a, Floating a, Random a, RandomGen g) =>
              a -> a -> g -> (a, g)
normal_rng mu sd g | sd > 0 = case marsaglia g of
                                ((x, _), g1) -> (mu + sd * x, g1)
normal_rng _ _ _ = error "normal: invalid parameters"

normalLogDensity mu sd x = (-tau * square (x - mu)
                            + log (tau / pi / 2)) / 2
  where square y = y * y
        tau = 1 / square sd

categoricalLogDensity list x = log $ fromMaybe 0 (lookup x list)
categoricalSample list g = (elem', g1)
    where
      (p, g1) = randomR (0, total) g
      elem' = fst $ head $ filter (\(_,p0) -> p <= p0) sumList
      sumList = scanl1 (\acc (a, b) -> (a, b + snd(acc))) list
      total = sum $ map snd list


lnFact = logFactorial

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
gamma_rng shape scale g | shape <= 0.0  = error "gamma: got a negative shape paramater"
gamma_rng shape scale g | scale <= 0.0  = error "gamma: got a negative scale paramater"
gamma_rng shape scale g | shape <  1.0  = (gvar2, g2)
                      where (gvar1, g1) = gamma_rng (shape + 1) scale g
                            (w,  g2) = randomR (0,1) g1
                            gvar2 = scale * gvar1 * (w ** recip shape) 
gamma_rng shape scale g = 
    let d = shape - 1/3
        c = recip $ sqrt $ 9*d
        -- Algorithm recommends inlining normal generator
        n g = normal_rng 1 c g
        (v, g2) = until (\x -> fst x > 0.0) (\ (_, g) -> normal_rng 1 c g) (n g)
        x = (v - 1) / c
        sqr = x * x
        v3 = v * v * v
        (u, g3) = randomR (0.0, 1.0) g2
        accept  = u < 1.0 - 0.0331*(sqr*sqr) || log u < 0.5*sqr + d*(1.0 - v3 + log v3)
    in case accept of
         True -> (scale*d*v3, g3)
         False -> gamma_rng shape scale g3

gammaLogDensity shape scale x | x>= 0 && shape > 0 && scale > 0 =
     scale * log shape - scale * x + (shape - 1) * log x - logGamma shape
gammaLogDensity _ _ _ = log 0

beta_rng :: (RandomGen g) => Double -> Double -> g -> (Double, g)
beta_rng a b g | a <= 1.0 && b <= 1.0 =
                 let (u, g1) = randomR (0.0, 1.0) g
                     (v, g2) = randomR (0.0, 1.0) g1
                     x = u ** (recip a)
                     y = v ** (recip b)
                 in  case (x+y) <= 1.0 of
                       True -> (x / (x + y), g2)
                       False -> beta_rng a b g2
beta_rng a b g = let (ga, g1) = gamma_rng a 1 g
                     (gb, g2) = gamma_rng b 1 g1
                 in (ga / (ga + gb), g2)

betaLogDensity a b x | x < 0 || x > 1 = error "beta: value must be between 0 and 1"
betaLogDensity a b x | a <= 0 || b <= 0 = error "beta: parameters must be positve" 
betaLogDensity a b x = (logGamma (a + b)
                        - logGamma a
                        - logGamma b
                        + (a - 1) * log x
                        + (b - 1) * log (1 - x))

laplace_rng :: (RandomGen g) => Double -> Double -> g -> (Double, g)
laplace_rng mu sd g = sample (randomR (0.0, 1.0) g)
   where sample (u, g1) = case u < 0.5 of
                            True  -> (mu + sd * log (u + u), g1)
                            False -> (mu - sd * log (2.0 - u - u), g1)

laplaceLogDensity mu sd x = - log (2 * sd) - abs (x - mu) / sd

-- Consider having dirichlet return Vector
-- Note: This is acutally symmetric dirichlet
dirichlet_rng :: (RandomGen g) => Int ->  Double -> g -> ([Double], g)
dirichlet_rng n a g = normalize (gammas g n)
  where gammas g 0 = ([], 0, g)
        gammas g n = let (xs, total, g1) = gammas g (n-1)
                         ( x, g2) = gamma_rng a 1 g1 
                     in ((x : xs), x+total, g2)
        normalize (a, total, g) = (map (/ total) a, g)

dirichletLogDensity a x | all (> 0) x = sum (zipWith logTerm a x) + logGamma (sum a)
  where sum a = foldl' (+) 0 a
        logTerm a x = (a-1) * log x - logGamma a
dirichletLogDensity _ _ = error "dirichlet: all values must be between 0 and 1"
