{-# LANGUAGE RankNTypes, TypeOperators, ScopedTypeVariables, TypeFamilies, FlexibleContexts #-}

module Examples.BenchmarkProblems where

import Prelude hiding (Real)
import qualified Control.Monad
import Data.Char
import Data.Csv (encode)
import Language.Hakaru.Util.Csv
import qualified Data.Number.LogFloat as LF

import qualified Data.Vector as V

import Language.Hakaru.Syntax
import Language.Hakaru.Sample
import Language.Hakaru.Expect
import Language.Hakaru.Disintegrate
import Language.Hakaru.PrettyPrint
import Language.Hakaru.Partial
import Language.Hakaru.Simplify
import Language.Hakaru.Any
import Language.Hakaru.Embed

import qualified Language.Hakaru.Vector as LV

import System.Random.MWC as MWC hiding (uniform)

type Cont repr a = forall w. (a -> repr (Measure w)) -> repr (Measure w)

replicateH :: (Mochastic repr) => Int -> repr (Measure a) -> Cont repr [repr a]
replicateH 0 _ k = k []
replicateH n m k = m `bind` \x -> replicateH (n-1) m (\xs -> k (x:xs))

noisyOr :: (Mochastic repr) => repr Prob -> repr Bool -> repr Bool -> repr (Measure Bool)
noisyOr noise x y = if_ (or_ [x, y])
                    (bern (1 - noise))
                    (bern noise)

tester prog = do
  g <- MWC.create
  Control.Monad.replicateM 10 (unSample prog 1 g)

xor :: Base repr => repr Bool -> repr Bool -> repr Bool
xor a b = or_ [and_ [a, not_ b], and_ [not_ a, b]]

eq_ :: Base repr => repr Bool -> repr Bool -> repr Bool
eq_ a b = if_ a b (not_ b)

runExpect :: (Lambda repr, Base repr) =>
              Expect repr (Measure Prob) -> repr Prob
runExpect (Expect m) = unpair m (\ m1 m2 -> m2 `app` lam id)

reflect' :: (Lambda repr, Mochastic repr, Integrate repr) =>
            repr (Vector (Vector Prob)) -> Expect repr (Int -> Measure Int)
reflect' m = lam (\ x -> categorical (index (Expect m) x))

reflectV :: (Lambda repr, Integrate repr, Mochastic repr) =>
             repr (Vector Prob) -> Expect repr (Measure Int)
reflectV m = categorical (Expect m)

reify' :: (Lambda repr, Mochastic repr) => repr Int -> repr Int ->
          Expect repr (Int -> Measure Int) -> repr (Vector (Vector Prob))
reify' size1 size2 (Expect m) =
    vector size1 (\ s  ->
    vector size2 (\ s' ->
    unpair (app m s)
      (\ m1 m2 ->
        (app m2 $ lam
             (\x -> if_ (equal_ x s') 1 0)))))

reifyV :: (Lambda repr, Mochastic repr) => repr Int ->
           Expect repr (Measure Int) -> repr (Vector Prob)
reifyV s1 (Expect m) =
    vector s1 (\ s' ->
    unpair m
      (\ m1 m2 ->
        (app m2 $ lam
             (\x -> if_ (equal_ x s') 1 0))))

condition d = head (runDisintegrate (\ _ -> d)) unit

-- CP4 Problem 1

make5Pair :: (Base repr) => [repr a] -> repr (a,(a,(a,(a,a))))
make5Pair [x1,x2,x3,x4,x5] = pair x1
                                (pair x2
                                 (pair x3
                                  (pair x4
                                         x5)))

make6Pair :: (Base repr) => [repr a] -> repr (a,(a,(a,(a,(a,a)))))
make6Pair [x1,x2,x3,x4,x5,x6] = pair x1
                                (pair x2
                                 (pair x3
                                  (pair x4
                                   (pair x5
                                         x6))))

type Real5 = (Real, (Real, (Real, (Real, Real))))
type Real6 = (Real, (Real, (Real, (Real, (Real, Real)))))

type Double5 = (Double, (Double, (Double, (Double, Double))))

-- Bayesian Linear Regression
readLinreg :: FilePath -> IO [[Double]]
readLinreg problem1 = do
   rows <- decodeFileStream problem1
   return [[x1,x2,x3,x4,x5,y] | (i::String,x1,x2,x3,x4,x5,y) <- rows]

linreg :: Mochastic repr => repr (Measure (Real6, Real5))
linreg = normal 0 2 `bind` \w1 ->
         normal 0 2 `bind` \w2 ->
         normal 0 2 `bind` \w3 ->
         normal 0 2 `bind` \w4 ->
         normal 0 2 `bind` \w5 ->
         uniform (-1) 1 `bind` \x1 ->
         uniform (-1) 1 `bind` \x2 ->
         uniform (-1) 1 `bind` \x3 ->
         uniform (-1) 1 `bind` \x4 ->
         uniform (-1) 1 `bind` \x5 ->
         normal (x1*w1 + x2*w2 + x3*w3 + x4*w4 + x5*w5) 1 `bind` \y ->
         dirac (pair (make6Pair [x1,x2,x3,x4,x5,y]) (make5Pair [w1,w2,w3,w4,w5]))

distLinreg :: (Lambda repr, Mochastic repr) => repr (Real6 -> (Measure Real5))
distLinreg = runPartial (lam $ \ x -> (runDisintegrate (\ env -> linreg) !! 0) unit x)

simpLinreg :: (Embed repr, Lambda repr, Integrate repr, Mochastic repr) =>
              IO (repr (Real6 -> (Measure Real5)))
simpLinreg = Control.Monad.liftM unAny (simplify distLinreg)

testLinreg :: IO (Maybe (Double5, LF.LogFloat))
testLinreg = do
  g <- MWC.create
  rawData <- readLinreg "CP4-SmallProblems/small-problems-v2.0/problem-1-data.csv"
  let [x1,x2,x3,x4,x5,y] = head rawData
  --simplified <- simpLinreg
  unSample distLinreg (x1,(x2,(x3,(x4,(x5,y))))) 1 g

-- QMR

qmr :: Mochastic repr => repr (Measure (Bool, Bool))
qmr =
 bern (1/40)   `bind` \cold ->
 bern (1/80)   `bind` \flu  ->
 bern (1/1200) `bind` \ebola ->
 noisyOr (1/10) cold flu `bind` \cough ->
 noisyOr (1/20) flu ebola `bind` \fever ->
 dirac (pair flu cold)

-- Discrete-time HMM

symDirichlet :: (Lambda repr, Integrate repr, Mochastic repr) =>
                repr Int -> repr Prob -> repr (Measure (Vector Prob))
symDirichlet n a = liftM normalizeV (plate (constV n (gamma a 1)))

start :: Base repr => repr Int
start = 0

transition :: Mochastic repr => repr Int -> repr (Measure Int)
transition s = categorical
               (vector 5 (\ i ->
                 if_ (equal_ i s) 1
                  (if_ (or_ [equal_ i (s+1), equal_ i (s-4)])
                   1
                   (if_ (or_ [equal_ i (s+2), equal_ i (s-3)])
                    1 0))))

emission   :: Mochastic repr => repr Int -> repr (Measure Int)
emission s =  categorical
              (vector 5 (\ i ->
                if_ (equal_ i s) 0.6 0.1))

hmm :: (Lambda repr, Mochastic repr) => repr (Measure (Vector Int, Vector Int))
hmm = app (chain (vector 20
                  (\ _ -> lam $ \s ->
                   transition s `bind` \s' ->
                   emission s' `bind` \o ->
                   dirac $ pair (pair s' o) s'
                  ))) start `bind` \x ->
      dirac (unzipV (fst_ x))

mh :: (Mochastic repr, Integrate repr, Lambda repr,
       a ~ Expect' a, Order_ a) =>
      (forall repr'. (Mochastic repr') => repr' a -> repr' (Measure a)) ->
      (forall repr'. (Mochastic repr') => repr' (Measure a)) ->
      repr (a -> Measure (a, Prob))
mh proposal target =
  let_ (lam (d unit)) $ \mu ->
  lam $ \old ->
    proposal old `bind` \new ->
    dirac (pair new (mu `app` pair new old / mu `app` pair old new))
  where d:_ = density (\dummy -> ununit dummy $ bindx target proposal)

mcmc :: (Mochastic repr, Integrate repr, Lambda repr,
         a ~ Expect' a, Order_ a) =>
        (forall repr'. (Mochastic repr') => repr' a -> repr' (Measure a)) ->
        (forall repr'. (Mochastic repr') => repr' (Measure a)) ->
        repr (a -> Measure a)
mcmc proposal target =
  let_ (mh proposal target) $ \f ->
  lam $ \old ->
    app f old `bind` \new_ratio ->
    unpair new_ratio $ \new ratio ->
    bern (min_ 1 ratio) `bind` \accept ->
    dirac (if_ accept new old)

dummyProp :: Mochastic repr => repr a -> repr (Measure a)
dummyProp = dirac

-- True type doesn't have pairs due to disintegrate
roadmapProg1 :: (Mochastic repr, Integrate repr, Lambda repr) =>
                repr ((Vector Int, Vector Int) -> Measure (Vector Int, Vector Int))
roadmapProg1 = mcmc dummyProp hmm

step  :: (Lambda repr, Integrate repr, Mochastic repr) =>
         Expect repr (Int -> Measure Int) ->
         Expect repr (Int -> Measure Int) ->
         Expect repr (Int -> Measure Int)
step m1 m2 = lam $ \x -> reflectV (reifyV 5 (app m1 x `bind` app m2))

-- P (s_20 = x | s_0 = y)
forwardBackward :: (Lambda repr, Integrate repr, Mochastic repr) =>
                   Expect repr (Int -> Measure Int)
forwardBackward = reduce step (lam dirac)
                  (vector 20 (\_ -> lam $ \s ->
                                transition s `bind` \s' ->
                                emission s'))

-- HDP-LDA

y  = 1
a0 = 1
nu = 0.01
w  = 10473

ldaVec = undefined

sampleV :: (Lambda repr, Mochastic repr) =>
            repr (Int -> Vector Real -> Measure (Vector Int))
sampleV = lam (\n ->
          lam (\x -> plate (vector n (\i ->
                            categorical (mapV unsafeProb x)))))

vocab :: V.Vector String
vocab = V.fromList ["sports", "food", "lifestyle"]

runSampleV :: Int -> IO (V.Vector String) --(Maybe (Vec Int, LF.LogFloat))
runSampleV n = do
   let v = V.fromList [0.4, 0.3, 0.2]
   g <- MWC.create
   Just (v',_) <- unSample sampleV n v 1 g
   return $ V.map (vocab V.!) v'

-- pCFG

-- Network Analysis

preferentialPrior :: Mochastic repr => repr (Measure Real)
preferentialPrior = uniform 0 1

numNodes          :: Mochastic repr => repr (Measure Int)
numNodes          = poisson 5

edgesPerNode      :: Mochastic repr => repr (Measure Int)
edgesPerNode      = poisson 3

-- Friends who Smoke
friendsWhoSmoke :: Mochastic repr => repr (Measure (Bool, Bool))
friendsWhoSmoke =
    bern (1/5) `bind` \smokes1 ->
    bern (1/5) `bind` \smokes2 ->
    bern (1/5) `bind` \smokes3 ->
    (if_ (eq_ smokes1 smokes2)
         (factor 3)
         (factor 1)) `bind_`
    dirac (pair smokes1 smokes3)

-- Seismic event monitoring

a1, b1, aN, bN, aS, bS :: Base repr => repr Prob

a1 = 20; b1 = 2
aN = 3;  bN = 2
aF = 20; bF = 1; aS = 2; bS = 1

uV, sigV, uB, sigB, uv, sigv :: Base repr => repr Prob
uV = 5; sigV = 1
uB = 2; sigB = 1
uv = 1; sigv = 1

uT = 0; lT = 1000; aT = 20; bT = 1
uA = 0; lA = 1;    aA = 2;  bA = 1
un = 0; ln = 1;    an = 2;  bn = 1

logistic :: Base repr => repr Real -> repr Real -> repr Prob -> repr Prob
logistic x v sig = 1 / (1 + exp_ (- (x - v) / fromProb sig))

seismic :: Mochastic repr => repr (Measure Prob)
seismic = gamma a1 b1 `bind` \l0 ->
          dirac l0

-- Recursive reasoning
hiddenState :: Mochastic repr => repr (Measure Int)
hiddenState = categorical (mapV (unsafeProb . fromInt) $ rangeV 3)

-- eTest :: (Integrate repr,
--           Lambda repr,
--           Mochastic repr) =>
--          Expect repr Prob -> repr Prob
-- eTest n = runExpect (dirac n)

-- Lifted inference
n :: Int
n = 10 -- [10,20,40,80,160,320,640,1280,2560,5120]

k :: Base repr => repr Int
k = 2 -- [1,2,4,8,16,32,64]

liftedInference :: Mochastic repr => repr (Measure (Int, Bool))
liftedInference = bern 0.01 `bind` \cause ->
                  replicateH n (if_ cause (bern 0.6) (bern 0.05))
                   (\ effects ->
                    dirac $
                    foldl (\ sum_ e ->
                           sum_ + (if_ e 1 0)) 0 effects) `bind` \sum_ ->
                  dirac (pair sum_ cause)

testLiftedInference :: Mochastic repr => repr (Measure Bool)
testLiftedInference = runPartial ((runDisintegrate (\ env -> liftedInference) !! 0) unit k)
