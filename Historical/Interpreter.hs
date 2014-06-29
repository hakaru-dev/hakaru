{-# LANGUAGE FlexibleInstances, TypeFamilies, RankNTypes, FlexibleContexts, DataKinds, TypeOperators #-}
{-# OPTIONS -W #-}

module Historical.Interpreter where

import Util.HList
import Sampler
import Mixture
import RandomChoice
import System.Random
import Data.Monoid
import Data.Ix
import Control.Monad

-- Ambient measures and absolute continuity

data    Unconditioned a = Unconditioned deriving (Show)
newtype Lebesgue      a = Lebesgue a    deriving (Show)
newtype Discrete      a = Discrete a    deriving (Show)

type family Element cond
type instance Element (Unconditioned a) = a
type instance Element (Lebesgue      a) = a
type instance Element (Discrete      a) = a
type instance Element (cond1, cond2)    = (Element cond1, Element cond2)
type instance Element (Maybe cond)      = Element cond

class Dirac cond where
  dirac :: Element cond -> cond -> Sampler (Element cond)

instance (Dirac cond) => Dirac (Maybe cond) where
  dirac x Nothing     = dirac x Unconditioned
  dirac x (Just cond) = dirac x cond

instance Dirac (Unconditioned a) where
  dirac x _ = deterministic (point x 1)

instance (Eq a) => Dirac (Discrete a) where
  dirac x (Discrete y) = deterministic (if x == y then point x 1 else empty)

instance (Ord (Element cond1), Ord (Element cond2), Dirac cond1, Dirac cond2) =>
         Dirac (cond1, cond2) where
  dirac (x1, x2) (cond1, cond2) g0 =
    let (m1, g1) = dirac x1 cond1 g0
        (m2, g ) = dirac x2 cond2 g1
    in (cross (,) m1 m2, g)

class (Element cond ~ Bool) => Bernoulli cond where
  bern :: Double -> cond -> Sampler Bool

instance (Bernoulli cond) => Bernoulli (Maybe cond) where
  bern theta Nothing     = bern theta Unconditioned
  bern theta (Just cond) = bern theta cond

instance Bernoulli (Unconditioned Bool) where
  bern theta | 0 <= theta && theta <= 1 = \_ g0 ->
   case randomR (0, 1) g0 of (x, g) -> (point (x <= theta) 1, g)
  bern _ = error "unconditioned bernoulli: invalid parameter"

instance Bernoulli (Discrete Bool) where
  bern theta | 0 <= theta && theta <= 1 = \(Discrete y) ->
    deterministic (if y then point y theta else point y (1 - theta))
  bern _ = error "conditioned bernoulli: invalid parameter"

class (Ord (Element cond), Random (Element cond)) => Uniform cond where
  uniform :: Element cond -> Element cond -> cond -> Sampler (Element cond)

instance (Uniform cond) => Uniform (Maybe cond) where
  uniform lo hi Nothing     = uniform lo hi Unconditioned
  uniform lo hi (Just cond) = uniform lo hi cond

instance (Ord a, Random a) => Uniform (Unconditioned a) where
  uniform lo hi | lo < hi = \_ g0 ->
    case randomR (lo,hi) g0 of (x, g) -> (point x 1, g)
  uniform _ _ = error "unconditioned uniform: invalid parameters"

instance (Random a, Fractional a, Real a) => Uniform (Lebesgue a) where
  uniform lo hi | lo < hi = \(Lebesgue y) ->
    deterministic (if lo < y && y < hi then point y density else empty)
    where density = fromRational (toRational (recip (hi - lo)))
  uniform _ _ = error "continuous uniform: invalid parameters"

instance (Random a, Ix a) => Uniform (Discrete a) where
  uniform lo hi | lo <= hi = \(Discrete y) ->
    deterministic (if lo <= y && y <= hi then point y density else empty)
    where density = recip (fromInteger (toInteger (rangeSize (lo,hi))))
  uniform _ _ = error "discrete uniform: invalid parameters"

class (Integral (Element cond)) => Poisson cond where
  poisson :: Double -> cond -> Sampler (Element cond)

instance (Poisson cond) => Poisson (Maybe cond) where
  poisson l Nothing     = poisson l Unconditioned
  poisson l (Just cond) = poisson l cond

instance (Integral a) => Poisson (Unconditioned a) where
  poisson l | 0 <= l = \_ g0 ->
    let probs = exp (-l) : zipWith (\k p -> p * l / k) [1..] probs
        (k, g) = chooseIndex probs g0
    in (point (fromInteger (toInteger k)) 1, g)
  poisson _ = error "unconditioned poisson: invalid parameter"

instance (Integral a) => Poisson (Discrete a) where
  poisson l | 0 <= l = \(Discrete k) ->
    deterministic
      (if 0 <= k then point k (exp (-l) * l^k / product [1..fromIntegral k])
                 else empty)
  poisson _ = error "conditioned poisson: invalid parameter"

class (Ord (Element cond), Random (Element cond), Floating (Element cond)) =>
      Normal cond where
  normal :: Element cond -> Element cond -> cond -> Sampler (Element cond)

instance (Normal cond) => Normal (Maybe cond) where
  normal mean std Nothing     = normal mean std Unconditioned
  normal mean std (Just cond) = normal mean std cond

instance (Random a, Ord a, Floating a) => Normal (Unconditioned a) where
  normal mean std | std > 0 = \_ g0 ->
    case marsaglia g0 of ((x, _), g) -> (point (mean + std * x) 1, g)
  normal _ _ = error "unconditioned normal: invalid parameters"

instance (Random a, Real a, Floating a) => Normal (Lebesgue a) where
  normal mean std | std > 0 = \(Lebesgue y) ->
    let density  = exp (square ((y - mean) / std) / (-2)) / std / sqrt (2 * pi)
        square y = y * y
    in deterministic (point y (fromRational (toRational density)))
  normal _ _ = error "continuous normal: invalid parameters"

-- Conditioned sampling

newtype Measure conds a = Measure { unMeasure :: VList conds -> Sampler a }

bind :: (TList conds1, TList conds2) =>
        Measure conds1 a ->
        (a -> Measure conds2 b) ->
        Measure (Append conds1 conds2) b
bind measure continuation =
  Measure (\conds ->
    case vsplit conds of
      (conds1, conds2) ->
        sbind (unMeasure measure conds1)
              (\a -> unMeasure (continuation a) conds2))

conditioned :: (cond -> Sampler a) -> Measure '[cond] a
conditioned f = Measure (\(VCons cond VNil) -> f cond)

unconditioned :: (Unconditioned b -> Sampler a) -> Measure '[] a
unconditioned f = Measure (\_ -> f Unconditioned)

-- Our language also includes the usual goodies of a lambda calculus

var :: a -> a
var = id

lit :: a -> a
lit = id

lam :: (a -> b) -> (a -> b)
lam f = f

app :: (a -> b) -> a -> b
app f x = f x

fix :: ((a -> b) -> (a -> b)) -> (a -> b)
fix g = f where f = g f

ifThenElse :: Bool -> a -> a -> a
ifThenElse True  t _ = t
ifThenElse False _ e = e

-- Some example/test programs in our language

test :: Measure '[Lebesgue Double] Bool
test = unconditioned (uniform (lit False) (lit True)) `bind` \c ->
       conditioned (ifThenElse c (normal (lit 1) (lit 1))
                                 (uniform (lit 0) (lit 3))) `bind` \_ ->
       unconditioned (dirac c)

test_two_normals :: Measure '[Lebesgue Double] Bool
test_two_normals = unconditioned (uniform False True) `bind` \coin ->
       conditioned (ifThenElse coin (normal 0 1) (normal 100 1)) `bind` \_ ->
       unconditioned (dirac coin)

test_overlapping_normals :: Measure '[Lebesgue Double, Lebesgue Double] Bool
test_overlapping_normals = unconditioned (uniform False True) `bind` \coin ->
       conditioned (ifThenElse coin (normal 0 0.01) (normal 0 100)) `bind` \_ ->
       conditioned (ifThenElse coin (normal 0 0.01) (normal 0 100)) `bind` \_ ->
       unconditioned (dirac coin)

test_bool :: Measure '[Lebesgue Double] Bool
test_bool = unconditioned (bern 0.9) `bind` \coin ->
            conditioned (ifThenElse coin (normal 0 1) (normal 20 1)) `bind` \_ ->
            unconditioned (dirac coin)

test_bayes :: Measure '[Discrete Bool] Bool
test_bayes = unconditioned (bern 0.2) `bind` \rain ->
       unconditioned (ifThenElse rain (bern 0.01) (bern 0.4)) `bind` \sprinkler ->
       conditioned (ifThenElse rain (ifThenElse sprinkler (bern 0.99) (bern 0.8))
                                    (ifThenElse sprinkler (bern 0.9) (bern 0.1))) `bind` \_ ->
       unconditioned (dirac rain)

-- Drivers for testing

sample :: (Ord a) => Int -> Measure conds a -> VList conds -> IO (Mixture a)
sample n measure conds = go n empty where
  once = getStdRandom (unMeasure measure conds)
  go 0 m = return m
  go n m = once >>= \result -> go (n - 1) $! mappend m result

sample_ :: (Ord a, Show a) => Int -> Measure conds a -> VList conds -> IO ()
sample_ n measure conds = replicateM_ n (once >>= pr) where
  once = getStdRandom (unMeasure measure conds)
  pr   = print . toList

main :: IO ()
main = sample_ 3 test conds >> putChar '\n' >> sample 1000 test conds >>= print
  where conds = VCons (Lebesgue 2) VNil

main_test_2p1 :: IO ()
main_test_2p1 = sample_ 10 test_two_normals conds >> putChar '\n' >> sample 1000 test conds >>= print
  where conds = VCons (Lebesgue 50) VNil

main_test_2p2 :: IO ()
main_test_2p2 = sample_ 10 test_two_normals conds >> putChar '\n' >> sample 1000 test conds >>= print
  where conds = VCons (Lebesgue 80) VNil

main_test_3 :: IO ()
main_test_3 = sample_ 10 test_overlapping_normals conds >> putChar '\n' >> sample 1000 test_overlapping_normals conds >>= print
  where conds = VCons (Lebesgue 0.0) $ VCons (Lebesgue 0.0) $ VNil

main_test_4 :: IO ()
main_test_4 = sample_ 3 test_bool conds >> putChar '\n' >> sample 1000 test_bool conds >>= print
  where conds = VCons (Lebesgue 1) VNil

main_bayes :: IO ()
main_bayes = sample_ 10 test_bayes conds >> putChar '\n' >> sample 1000 test_bayes conds >>= print
  where conds = VCons (Discrete True) VNil
