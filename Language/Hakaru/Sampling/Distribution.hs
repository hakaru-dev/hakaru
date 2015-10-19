{-# LANGUAGE RankNTypes, BangPatterns, GADTs #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.18
-- |
-- Module      :  Language.Hakaru.Sampling.Distribution
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
----------------------------------------------------------------
module Language.Hakaru.Sampling.Distribution where

import Control.Monad.Primitive
import Control.Monad.Loops
import Data.Functor                   ((<$>))
import Data.Ix
import Data.Maybe                     (fromMaybe)
import Data.List                      (findIndex, foldl')
import Numeric.SpecFunctions
import qualified System.Random.MWC    as MWC
import qualified Data.Map.Strict      as M
import qualified Data.Number.LogFloat as LF

import Language.Hakaru.Sampling.Mixture
import Language.Hakaru.Sampling.Types
----------------------------------------------------------------

dirac :: (Eq a) => a -> Dist a
dirac theta = Dist
    { logDensity = \ (Discrete x) -> if x == theta then 0 else log 0
    , distSample = \ _ -> return $ Discrete theta
    }

bern :: Double -> Dist Bool
bern p = Dist
    { logDensity = \ (Discrete x) -> log (if x then p else 1 - p)
    , distSample = \ g -> do
        t <- MWC.uniformR (0,1) g
        return $ Discrete (t <= p)
    }

uniform :: Double -> Double -> Dist Double
uniform lo hi =
    let uniformLogDensity lo' hi' x
            | lo' <= x && x <= hi' = log (recip (hi' - lo'))
            | otherwise            = log 0
    in Dist
        { logDensity = \ (Lebesgue x) -> uniformLogDensity lo hi x
        , distSample = \ g -> Lebesgue <$> MWC.uniformR (lo, hi) g
        }

uniformD :: (Ix a, MWC.Variate a) => a -> a -> Dist a
uniformD lo hi =
    let uniformLogDensity lo' hi' x
            | lo' <= x && x <= hi' = log density
            | otherwise            = log 0
        density = recip . fromInteger . toInteger $ rangeSize (lo,hi)
    in Dist
        { logDensity = \ (Discrete x) -> uniformLogDensity lo hi x
        , distSample = \ g -> Discrete <$> MWC.uniformR (lo, hi) g
        }

-- | "Marsaglia polar method"
marsaglia
    :: (MWC.Variate a, Ord a, Floating a, Functor m, PrimMonad m)
    => PRNG m -> m (a, a)
marsaglia g = do
    x <- MWC.uniformR (-1,1) g
    y <- MWC.uniformR (-1,1) g
    let s = x * x + y * y
        q = sqrt ((-2) * log s / s)
    if 1 >= s && s > 0
        then return (x * q, y * q)
        else marsaglia g

choose :: (Functor m, PrimMonad m) => Mixture k -> PRNG m -> m (k, Prob)
choose (Mixture m) g = do
    let peak = maximum (M.elems m)
        unMix = M.map (LF.fromLogFloat . (/peak)) m
        total = M.foldl' (+) 0 unMix
    p <- MWC.uniformR (0, total) g
    let f !k !v b !p0 = let p1 = p0 + v in if p <= p1 then k else b p1
        err p0 = error $
            "choose: failure p0=" ++ show p0 ++
            " total=" ++ show total ++
            " size=" ++ show (M.size m)
    return (M.foldrWithKey f err unMix 0, LF.logFloat total * peak)

chooseIndex :: (Functor m, PrimMonad m) => [Double] -> PRNG m -> m Int
chooseIndex probs g = do
    p <- MWC.uniform g
    return
        . fromMaybe (error $ "chooseIndex: failure p=" ++ show p)
        . findIndex (p <=)
        $ scanl1 (+) probs

normal_rng
    :: (Real a, Floating a, MWC.Variate a, Functor m, PrimMonad m)
    => a -> a -> PRNG m -> m a
normal_rng mu sd g
    | sd > 0    = marsaglia g >>= \ (x,_) -> return (mu + sd * x)
    | otherwise = error "normal: invalid parameters"

normalLogDensity :: Floating a => a -> a -> a -> a
normalLogDensity mu sd x =
    (-tau * square (x - mu) + log (tau / pi / 2)) / 2
    where
    square y = y * y
    tau = 1 / square sd

normal :: Double -> Double -> Dist Double 
normal mu sd = Dist
    { logDensity = normalLogDensity mu sd . fromLebesgue
    , distSample = \ g -> Lebesgue <$> normal_rng mu sd g
    }

categoricalLogDensity :: (Eq b, Floating a) => [(b, a)] -> b -> a
categoricalLogDensity list x = log . fromMaybe 0 $ lookup x list

categoricalSample
    :: (Num b, Ord b, Functor m, PrimMonad m, MWC.Variate b)
    => [(t,b)] -> PRNG m -> m t
categoricalSample list g = do
    let total = sum $ map snd list
    p <- MWC.uniformR (0, total) g
    return
        . fst
        . head
        . filter (\ (_,p0) -> p <= p0)
        . scanl1 (\ acc (a,b) -> (a, b + snd acc))
        $ list

categorical :: Eq a => [(a,Double)] -> Dist a
categorical list = Dist
    { logDensity = categoricalLogDensity list . fromDiscrete
    , distSample = \g -> Discrete <$> categoricalSample list g
    }

-- Makes use of Atkinson's algorithm as described in:
-- Monte Carlo Statistical Methods pg. 55
--
-- Further discussion at:
-- http://www.johndcook.com/blog/2010/06/14/generating-poisson-random-values/
poisson_rng :: (Functor m, PrimMonad m) => Double -> PRNG m -> m Int
poisson_rng lambda g' = make_poisson g'
    where
    smu   = sqrt lambda
    b     = 0.931 + 2.53*smu
    a     = -0.059 + 0.02483*b
    vr    = 0.9277 - 3.6224/(b - 2)
    arep  = 1.1239 + 1.1368/(b - 3.4)
    lnlam = log lambda

    make_poisson :: (Functor m, PrimMonad m) => PRNG m -> m Int
    make_poisson g = do
        u <- MWC.uniformR (-0.5,0.5) g
        v <- MWC.uniformR (0,1) g
        let us = 0.5 - abs u
            k = floor $ (2*a / us + b)*u + lambda + 0.43
        case () of
            () | us >= 0.07 && v <= vr -> return k
            () | k < 0                 -> make_poisson g
            () | us <= 0.013 && v > us -> make_poisson g
            () | accept_region us v k  -> return k
            _                          -> make_poisson g

    accept_region :: Double -> Double -> Int -> Bool
    accept_region us v k =
        log (v * arep / (a/(us*us)+b))
        <=
        -lambda + fromIntegral k * lnlam - logFactorial k

poisson :: Double -> Dist Int
poisson l =
    let poissonLogDensity l' x
            | l' > 0 && x >= 0 = fromIntegral x * log l' - logFactorial x - l'
            | otherwise        = log 0
    in Dist
        { logDensity = poissonLogDensity l . fromDiscrete
        , distSample = \g -> Discrete <$> poisson_rng l g
        }

-- | Direct implementation of \"A Simple Method for Generating Gamma Variables\" by George Marsaglia and Wai Wan Tsang.
gamma_rng
    :: (Functor m, PrimMonad m) => Double -> Double -> PRNG m -> m Double
gamma_rng shape scl g
    | shape <= 0  = error "gamma: got a negative shape paramater"
    | scl   <= 0  = error "gamma: got a negative scale paramater"
    | shape <  1  = do
        gvar1 <- gamma_rng (shape + 1) scl g
        w <- MWC.uniformR (0,1) g
        return $ scl * gvar1 * (w ** recip shape)
    | otherwise = do
        let d = shape - 1/3
            c = recip $ sqrt $ 9*d
            n = normal_rng 1 c -- Algorithm recommends inlining normal generator
        v <- iterateUntil (> 0) $ n g
        let x   = (v - 1) / c
            sqr = x * x
            v3  = v * v * v
        u <- MWC.uniformR (0,1) g
        if u < 1 - 0.0331*(sqr*sqr) || log u < 0.5*sqr + d*(1 - v3 + log v3)
            then return $ scl*d*v3
            else gamma_rng shape scl g

gammaLogDensity :: Double -> Double -> Double -> Double
gammaLogDensity shape scl x
    | x >= 0 && shape > 0 && scl > 0 =
        scl * log shape - scl * x + (shape - 1) * log x - logGamma shape
    | otherwise = log 0

gamma :: Double -> Double -> Dist Double
gamma shape scl = Dist
    { logDensity = gammaLogDensity shape scl . fromLebesgue
    , distSample = \g -> Lebesgue <$> gamma_rng shape scl g
    }

beta_rng
    :: (Functor m, PrimMonad m) => Double -> Double -> PRNG m -> m Double
beta_rng a b g
    | a <= 1 && b <= 1 = do
        u <- MWC.uniformR (0,1) g
        v <- MWC.uniformR (0,1) g
        let x = u ** recip a
            y = v ** recip b
        if x+y <= 1
            then return $ x / (x + y)
            else beta_rng a b g
    | otherwise = do
        ga <- gamma_rng a 1 g
        gb <- gamma_rng b 1 g
        return $ ga / (ga + gb)

betaLogDensity :: Double -> Double -> Double -> Double
betaLogDensity a b x
    | x <  0 || x >  1 = error $ "beta: value must be between 0 and 1" ++ show x
    | a <= 0 || b <= 0 = error "beta: parameters must be positve" 
    | otherwise =
        ( logGamma (a + b)
        - logGamma a
        - logGamma b
        + (a - 1) * log x
        + (b - 1) * log (1 - x)
        )

beta :: Double -> Double -> Dist Double
beta a b = Dist
    { logDensity = betaLogDensity a b . fromLebesgue
    , distSample = \g -> Lebesgue <$> beta_rng a b g
    }

laplace_rng
    :: (Functor m, PrimMonad m) => Double -> Double -> PRNG m -> m Double
laplace_rng mu sd g =
    sample <$> MWC.uniformR (0,1) g
    where
    sample u
        | u < 0.5   = mu + sd * log (u + u)
        | otherwise = mu - sd * log (2 - u - u)

laplaceLogDensity :: Floating a => a -> a -> a -> a
laplaceLogDensity mu sd x = - log (2 * sd) - abs (x - mu) / sd

laplace :: Double -> Double -> Dist Double
laplace mu sd = Dist
    { logDensity = laplaceLogDensity mu sd . fromLebesgue
    , distSample = \g -> Lebesgue <$> laplace_rng mu sd g
    }

-- Consider having dirichlet return Vector
-- Note: This is actually symmetric dirichlet
dirichlet_rng
    :: (Functor m, PrimMonad m) => Int ->  Double -> PRNG m -> m [Double]
dirichlet_rng n' a g' = normalize <$> gammas g' n'
    where
    gammas _ 0 = return ([], 0)
    gammas g n = do
        (xs, total) <- gammas g (n-1)
        x <- gamma_rng a 1 g
        return (x:xs, x+total)
    normalize (b, total) = map (/ total) b

dirichletLogDensity :: [Double] -> [Double] -> Double
dirichletLogDensity a x
    | any (<= 0) x = error "dirichlet: all values must be between 0 and 1"
    | otherwise    = sum' (zipWith logTerm a x) + logGamma (sum a)
    where
    sum'        = foldl' (+) 0
    logTerm b y = (b-1) * log y - logGamma b

dirichlet :: Int -> Double -> Dist [Double]
dirichlet n a = Dist
    { logDensity = dirichletLogDensity (replicate n a) . fromLebesgue
    , distSample = \ g -> Lebesgue <$> dirichlet_rng n a g
    }

-- Consider making multinomial match categorical
multinomial_rng
    :: (Functor m, PrimMonad m) => Int -> [Double] -> PRNG m -> m [Int]
multinomial_rng _n _theta _g = undefined

-- TODO: check the sum and the @0 < y && y < n@ in a single pass
multinomialLogDensity :: Int -> [Double] -> [Int] -> Double
multinomialLogDensity n theta' x'
    | n > 0 && sum x' == n && all (\y -> 0 < y && y < n) x' =
        logFactorial n
        + sum [ fromIntegral x * log theta - logFactorial x
            | (theta, x) <- zip theta' x']
    | otherwise = log 0

multinomial :: Int -> [Double] -> Dist [Int]
multinomial n theta = Dist
    { logDensity = multinomialLogDensity n theta . fromDiscrete
    , distSample = \g -> Discrete <$> multinomial_rng n theta g
    }

----------------------------------------------------------------
----------------------------------------------------------- fin.