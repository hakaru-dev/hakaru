{-# LANGUAGE RankNTypes, TypeOperators, ScopedTypeVariables #-}

module Examples.BenchmarkProblems where

import Prelude hiding (Real)
import qualified Control.Monad
import Data.Char
import Data.Csv (encode)
import Language.Hakaru.Util.Csv
import qualified Data.Number.LogFloat as LF

import Language.Hakaru.Syntax
import Language.Hakaru.Sample
import Language.Hakaru.Expect
import Language.Hakaru.Disintegrate
import Language.Hakaru.PrettyPrint
import Language.Hakaru.Partial
import Language.Hakaru.Simplify
import Language.Hakaru.Any
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

--runExpect :: (Lambda repr) => Expect repr (Measure Prob) -> repr Prob
runExpect (Expect m) = m `app` lam id

condition d = head (runDisintegrate (\ _ -> d)) unit

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

simpLinreg :: (Lambda repr, Integrate repr, Mochastic repr) => IO (repr (Real6 -> (Measure Real5)))
simpLinreg = Control.Monad.liftM unAny (simplify distLinreg)

testLinreg :: IO (Maybe (Double5, LF.LogFloat))
testLinreg = do
  g <- MWC.create
  rawData <- readLinreg "/home/zv/programming/research_projects/prob_prog_ppaml/ppaml_repo/problems/CP4-SmallProblems/small-problems-v2.0/problem-1-data.csv"
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

symDirichlet :: (Mochastic repr) => Int -> repr Prob -> [repr (Measure Prob)]
symDirichlet n a = map (liftM2 (/) total) d
   where d = replicate n (gamma a 1)
         total = foldr (liftM2 (+)) (dirac 0) d

symDirichlet2 :: (Mochastic repr) => Int -> repr Prob -> repr ([Measure Prob])
symDirichlet2 0 a = nil 
symDirichlet2 n a = cons (gamma a 1) (symDirichlet2 (n - 1) a)

symDirichlet3 :: (Mochastic repr) => Int -> repr Prob -> repr (Measure [Prob])
symDirichlet3 0 a = dirac nil 
symDirichlet3 n a = gamma a 1 `bind` \x ->
                    symDirichlet3 (n - 1) a `bind` \xs ->
                    dirac (cons x xs)

symDirichlet4 :: (Mochastic repr) => repr Int -> repr Prob -> repr (Vector (Measure Prob))
symDirichlet4 n a = vector 0 n (\_ -> gamma a 1)

symDirichlet5 :: (Mochastic repr) => repr Int -> repr Prob -> repr (Measure (Vector Prob))
symDirichlet5 n a = plate $ symDirichlet4 n a

hmm = undefined
hmmVec = undefined

-- HDP-LDA

y  = 1
a0 = 1
nu = 0.01
w  = 10473

lda = undefined
ldaVec = undefined

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
aF = 20; bF = 1
aS = 2;  bS = 1

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
hiddenState :: Mochastic repr => repr (Measure Real)
hiddenState = categorical [(1, 0),
                           (1, 1),
                           (1, 2),
                           (1, 3)]

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
