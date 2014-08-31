{-# LANGUAGE BangPatterns #-}

module Tests.Distribution where

import Control.Monad
import qualified System.Random.MWC as MWC

import Language.Hakaru.Types
import Language.Hakaru.Util.Coda
import Language.Hakaru.Distribution hiding (choose)

import Test.QuickCheck
import Test.QuickCheck.Monadic as QM
import Test.Framework.Providers.QuickCheck2 (testProperty)

fromDiscreteToNum = fromIntegral . fromEnum . fromDiscrete
sq x = x * x

almostEqual :: (Fractional a, Ord a) => a -> a -> a -> Bool
almostEqual tol x y | abs (x - y) < tol = True
almostEqual tol x y = (abs $ (x - y) / (x + y)) < tol

quickArg :: IO ()
quickArg = quickCheckWith stdArgs {maxSuccess = 2000} (\ x -> almostEqual tol x x)
  where tol :: Double
        tol = 1e-5

qtest = [testProperty "checking beta" $ QM.monadicIO betaTest,
         testProperty "checking bern" $ QM.monadicIO bernTest,
         testProperty "checking gamma" $ QM.monadicIO gammaTest,
         testProperty "checking normal" $ QM.monadicIO normalTest,
         testProperty "checking laplace" $ QM.monadicIO laplaceTest,
         testProperty "checking poisson" $ QM.monadicIO poissonTest]

betaTest = do
  Positive a <- QM.pick arbitrary
  Positive b <- QM.pick arbitrary
  g <- QM.run $ MWC.create
  samples <- QM.run $ replicateM 1000 $ distSample (beta a b) g
  let (mean, variance) = meanVariance (map fromLebesgue samples)
  QM.assert $ (almostEqual tol mean     (mu  a b)) && 
              (almostEqual tol variance (var a b))
  where tol     = 1e-1
        mu a b  = a / (a + b)
        var a b = a*b / ((sq $ a + b) * (a + b + 1))

bernTest = do
   p <- QM.pick $ choose (0, 1)
   g <- QM.run $ MWC.create
   samples <- QM.run $ replicateM 1000 $ distSample (bern p) g
   let (mean, variance) = meanVariance (map fromDiscreteToNum samples)
   QM.assert $ (almostEqual tol mean     (mu  p)) && 
               (almostEqual tol variance (var p))
   where tol   = 1e-1
         mu p  = p
         var p = p*(1-p)

poissonTest = do
   lam <- QM.pick $ choose (1, 10)
   g <- QM.run $ MWC.create
   samples <- QM.run $ replicateM 1000 $ distSample (poisson lam) g
   let (mean, variance) = meanVariance (map (fromIntegral . fromDiscrete) samples)
   QM.assert $ (almostEqual tol mean     (mu  lam)) && 
               (almostEqual tol variance (var lam))
   where tol     = 1e-1
         mu  lam = lam
         var lam = lam

normalTest = do
  mu <- QM.pick arbitrary
  sd <- QM.pick $ choose (1, 10)
  g <- QM.run $ MWC.create
  let nsamples = floor (1000 * sd)  -- larger standard deviations need more samples
                                    -- to be shown as correct
  samples <- QM.run $ replicateM nsamples $ distSample (normal mu sd) g
  let (mean, variance) = meanVariance (map fromLebesgue samples)
  QM.assert $ (almostEqual tol mean     mu ) && 
              (almostEqual tol variance (var sd))
  where tol = 1e-1
        var sd = sq sd

laplaceTest = do
  mu <- QM.pick arbitrary
  sd <- QM.pick $ choose (1, 10)
  g <- QM.run $ MWC.create
  let nsamples = floor (1000 * sd)  -- larger standard deviations need more samples
                                    -- to be shown as correct
  samples <- QM.run $ replicateM nsamples $ distSample (laplace mu sd) g
  let (mean, variance) = meanVariance (map fromLebesgue samples)
  QM.assert $ (almostEqual tol mean     mu ) && 
              (almostEqual tol variance (var sd))
  where tol = 1e-1
        var sd = 2*(sq sd)

gammaTest = do
  a <- QM.pick $ choose (1, 10)
  b <- QM.pick $ choose (1, 10)
  g <- QM.run $ MWC.create
  samples <- QM.run $ replicateM 1000 $ distSample (gamma a b) g
  let (mean, variance) = meanVariance (map fromLebesgue samples)
  QM.assert $ (almostEqual tol mean     (mu  a b)) && 
              (almostEqual tol variance (var a b))
  where tol     = 1e-1
        mu a b  = a * b
        var a b = a * (b * b)

