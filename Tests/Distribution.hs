{-# LANGUAGE BangPatterns #-}

module Tests.Distribution where

import Control.Monad
import System.Random

import Language.Hakaru.Types
import Language.Hakaru.Util.Coda
import Language.Hakaru.Distribution hiding (choose)

import Test.QuickCheck
import qualified Test.QuickCheck.Monadic as QM

import Test.Framework.Providers.QuickCheck2 (testProperty)

fromDiscreteToNum = fromIntegral . fromEnum . fromDiscrete
sq x = x * x

almostEqual :: (Num a, Ord a) => a -> a -> a -> Bool
almostEqual tol x y = abs (x - y) < tol

quickArg :: IO ()
quickArg = quickCheckWith stdArgs {maxSuccess = 2000} (\ x -> almostEqual tol x x)
  where tol :: Double
        tol = 1e-5

qtest = [testProperty "checking beta" $ QM.monadicIO betaTest,
         testProperty "checking bern" $ QM.monadicIO bernTest]

betaTest = do
  Positive a <- QM.pick arbitrary
  Positive b <- QM.pick arbitrary
  samples <- QM.run $ replicateM 1000 $ getStdRandom $ distSample (beta a b)
  let (mean, variance) = meanVariance (map fromLebesgue samples)
  QM.assert $ (almostEqual tol mean     (mu  a b)) && 
              (almostEqual tol variance (var a b))
  where tol     = 1e-1
        mu a b  = a / (a + b)
        var a b = a*b / ((sq $ a + b) * (a + b + 1))

bernTest = do
   p <- QM.pick $ choose (0, 1)
   samples <- QM.run $ replicateM 1000 $ getStdRandom $ distSample (bern p)
   let (mean, variance) = meanVariance (map fromDiscreteToNum samples)
   QM.assert $ (almostEqual tol mean     (mu  p)) && 
               (almostEqual tol variance (var p))
   where tol   = 1e-1
         mu p  = p
         var p = p*(1-p)
