{-# LANGUAGE NoImplicitPrelude
           , DataKinds
           , Rank2Types
           , TypeOperators
           , ScopedTypeVariables
           , TypeFamilies
           , FlexibleContexts
           #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Examples.BenchmarkProblems where

import Prelude ((.), id, ($))

import Language.Hakaru.Syntax.Prelude
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Syntax.AST   (Term)
import Language.Hakaru.Syntax.ABT   (ABT)


import qualified Control.Monad
import Data.Char
import Data.Csv (encode)
import Language.Hakaru.Util.Csv
import qualified Data.Number.LogFloat as LF

import qualified Data.Vector as V

import Language.Hakaru.Sample
import Language.Hakaru.Expect
import qualified Language.Hakaru.Lazy as L
import Language.Hakaru.PrettyPrint
import Language.Hakaru.Simplify
import Language.Hakaru.Any
import Language.Hakaru.Embed

import qualified Language.Hakaru.Vector as LV

import System.Random.MWC as MWC hiding (uniform)

type Cont repr a = forall w. (a -> repr ('HMeasure w)) -> repr ('HMeasure w)

replicateH
    :: (ABT Term abt)
    => Int
    -> abt '[] ('HMeasure a)
    -> Cont (abt '[]) [abt '[] a]
replicateH 0 _ k = k []
replicateH n m k = m >>= \x -> replicateH (n-1) m (\xs -> k (x:xs))

noisyOr
    :: (ABT Term abt)
    => abt '[] 'HProb
    -> abt '[] HBool
    -> abt '[] HBool
    -> abt '[] ('HMeasure HBool)
noisyOr noise x y =
    if_ (x || y)
    (bern (one - noise))
    (bern noise)

tester prog = do
    g <- MWC.create
    Control.Monad.replicateM 10 (unSample prog 1 g)

runExpect
    :: (ABT Term abt)
    => Expect (abt '[]) ('HMeasure 'HProb)
    -> abt '[] 'HProb
runExpect (Expect m) = m `unpair` \ m1 m2 -> m2 `app` lam id

reflect'
    :: (ABT Term abt)
    => abt '[] ('HArray ('HArray 'HProb))
    -> Expect (abt '[]) ('HInt ':-> 'HMeasure 'HInt)
reflect' m = lam $ \ x -> categorical (index (Expect m) x)

reflectV
    :: (ABT Term abt)
    => abt '[] ('HArray 'HProb)
    -> Expect (abt '[]) ('HMeasure 'HInt)
reflectV m = categorical (Expect m)

reify'
    :: (ABT Term abt)
    => abt '[] 'HNat
    -> abt '[] 'HNat
    -> Expect (abt '[]) ('HInt ':-> 'HMeasure 'HInt)
    -> abt '[] ('HArray ('HArray 'HProb))
reify' size1 size2 (Expect m) =
    array size1 $ \ s  ->
    array size2 $ \ s' ->
    app m s `unpair` \ m1 m2 ->
    app m2 (lam $ \x -> if_ (x == s') 1 0)

reifyV
    :: (ABT Term abt)
    => abt '[] 'HNat
    -> Expect (abt '[]) ('HMeasure 'HInt)
    -> abt '[] ('HArray 'HProb)
reifyV s1 (Expect m) =
    array s1 $ \ s' ->
    m `unpair` \ m1 m2 ->
    app m2 (lam $ \x -> if_ (x == s') 1 0)

condition
    :: (ABT Term abt, L.Backward a a)
    => L.Cond (abt '[]) () ('HMeasure (HPair a b))
    -> abt '[] (a ':-> 'HMeasure b)
condition d = app (head (L.runDisintegrate d)) unit

-- CP4 Problem 1

type Tuple2 a = HPair a a
type Tuple3 a = HPair a (Tuple2 a)
type Tuple4 a = HPair a (Tuple3 a)
type Tuple5 a = HPair a (Tuple4 a)
type Tuple6 a = HPair a (Tuple5 a)

makeTuple5 :: (ABT Term abt) => [abt '[] a] -> abt '[] (Tuple5 a)
makeTuple5 [x1,x2,x3,x4,x5]
    = pair x1
    . pair x2
    . pair x3
    . pair x4
    $ x5

makeTuple6 :: (ABT Term abt) => [abt '[] a] -> abt '[] (Tuple6 a)
makeTuple6 [x1,x2,x3,x4,x5,x6]
    = pair x1
    . pair x2
    . pair x3
    . pair x4
    . pair x5
    $ x6

type Real5 = Tuple5 'HReal
type Real6 = Tuple6 'HReal

type Double5 = (Double, (Double, (Double, (Double, Double))))

-- Bayesian Linear Regression
readLinreg :: FilePath -> IO [[Double]]
readLinreg problem1 = do
    rows <- decodeFileStream problem1
    return [[x1,x2,x3,x4,x5,y] | (i::String,x1,x2,x3,x4,x5,y) <- rows]

linreg :: (ABT Term abt) => abt '[] ('HMeasure (HPair Real6 Real5))
linreg =
    let normal_0_2   = normal zero (prob_ 2)
        uniform_n1_1 = uniform (negate one) one
    in
    normal_0_2 >>= \w1 ->
    normal_0_2 >>= \w2 ->
    normal_0_2 >>= \w3 ->
    normal_0_2 >>= \w4 ->
    normal_0_2 >>= \w5 ->
    uniform_n1_1 >>= \x1 ->
    uniform_n1_1 >>= \x2 ->
    uniform_n1_1 >>= \x3 ->
    uniform_n1_1 >>= \x4 ->
    uniform_n1_1 >>= \x5 ->
    normal (x1*w1 + x2*w2 + x3*w3 + x4*w4 + x5*w5) 1 >>= \y ->
    dirac (pair
        (makeTuple6 [x1,x2,x3,x4,x5,y])
        (makeTuple5 [w1,w2,w3,w4,w5]))

distLinreg :: (ABT Term abt) => abt '[] (Real6 ':-> 'HMeasure Real5)
distLinreg = app ((L.runDisintegrate (\u -> ununit u $ linreg)) !! 0) unit

-- simpLinreg :: (ABT Term abt) => IO (abt '[] (Real6 ':-> 'HMeasure Real5))
-- simpLinreg = Control.Monad.liftM unAny (simplify distLinreg)

testLinreg :: IO (Maybe (Double5, LF.LogFloat))
testLinreg = do
    g <- MWC.create
    rawData <- readLinreg "CP4-SmallProblems/small-problems-v2.0/problem-1-data.csv"
    let [x1,x2,x3,x4,x5,y] = head rawData
    --simplified <- simpLinreg
    unSample distLinreg (x1,(x2,(x3,(x4,(x5,y))))) 1 g

-- QMR

qmr :: (ABT Term abt) => abt '[] ('HMeasure (HPair HBool HBool))
qmr =
    bern (1/40)   >>= \cold ->
    bern (1/80)   >>= \flu  ->
    bern (1/1200) >>= \ebola ->
    noisyOr (1/10) cold flu >>= \cough ->
    noisyOr (1/20) flu ebola >>= \fever ->
    dirac (pair flu cold)

-- Discrete-time HMM

symDirichlet
    :: (ABT Term abt)
    => abt '[] 'HInt
    -> abt '[] 'HProb
    -> abt '[] ('HMeasure ('HArray 'HProb))
symDirichlet n a = liftM normalizeV (plate (constV n (gamma a one)))

start :: (ABT Term abt) => abt '[] 'HInt
start = 0

transition :: (ABT Term abt) => abt '[] 'HInt -> abt '[] ('HMeasure 'HInt)
transition s =
    categorical . array (nat_ 5) $ \ i ->
        if_ (i == s) one $
        if_ (i == s+one || i == s-4) one $
        if_ (i == s+2 || i == s-3) one $
        zero

emission :: (ABT Term abt) => abt '[] 'HInt -> abt '[] ('HMeasure 'HInt)
emission s =
    categorical . array (nat_ 5) $\ i ->
        if_ (i == s) 0.6 0.1

hmm :: (ABT Term abt) => abt '[] ('HMeasure ('HArray 'HInt, 'HArray 'HInt))
hmm =
    app (chain (array (nat_ 20) $ \ _ ->
        lam $ \s ->
        transition s >>= \s' ->
        emission s' >>= \o ->
        dirac $ pair (pair s' o) s'
        ))
        start >>= \x ->
    dirac (unzipV (fst x))

step 
    :: (ABT Term abt)
    => Expect (abt '[]) ('HInt ':-> 'HMeasure 'HInt)
    -> Expect (abt '[]) ('HInt ':-> 'HMeasure 'HInt)
    -> Expect (abt '[]) ('HInt ':-> 'HMeasure 'HInt)
step m1 m2 = lam $ \x -> reflectV (reifyV 5 (app m1 x >>= app m2))

-- P (s_20 = x | s_0 = y)
forwardBackward
    :: (ABT Term abt) => Expect (abt '[]) ('HInt ':-> 'HMeasure 'HInt)
forwardBackward =
    reduce step (lam dirac) . array (nat_ 20) $ \_ ->
        lam $ \s ->
        transition s >>= \s' ->
        emission s')

-- HDP-LDA

y  = 1
a0 = 1
nu = 0.01
w  = 10473

ldaVec = undefined

sampleV
    :: (ABT Term abt)
    => abt '[] ('HInt ':-> 'HArray 'HReal ':-> 'HMeasure ('HArray 'HInt))
sampleV =
    lam $ \n ->
    lam $ \x -> plate (vector n $ \i ->
        categorical (mapV unsafeProb x))

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

preferentialPrior :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
preferentialPrior = uniform zero one

numNodes          :: (ABT Term abt) => abt '[] ('HMeasure 'HInt)
numNodes          = poisson 5

edgesPerNode      :: (ABT Term abt) => abt '[] ('HMeasure 'HInt)
edgesPerNode      = poisson 3

-- Friends who Smoke
friendsWhoSmoke :: (ABT Term abt) => abt '[] ('HMeasure (Bool, Bool))
friendsWhoSmoke =
    bern (1/5) >>= \smokes1 ->
    bern (1/5) >>= \smokes2 ->
    bern (1/5) >>= \smokes3 ->
    (if_ (smokes1 == smokes2)
         (factor 3)
         (factor 1)) `bind_`
    dirac (pair smokes1 smokes3)

-- Seismic event monitoring

a1, b1, aN, bN, aS, bS :: (ABT Term abt) => abt '[] 'HProb

a1 = 20; b1 = 2
aN = 3;  bN = 2
aF = 20; bF = 1; aS = 2; bS = 1

uV, sigV, uB, sigB, uv, sigv :: (ABT Term abt) => abt '[] 'HProb
uV = 5; sigV = 1
uB = 2; sigB = 1
uv = 1; sigv = 1

uT = 0; lT = 1000; aT = 20; bT = 1
uA = 0; lA = 1;    aA = 2;  bA = 1
un = 0; ln = 1;    an = 2;  bn = 1

logistic
    :: (ABT Term abt)
    => abt '[] 'HReal -> abt '[] 'HReal -> abt '[] 'HProb -> abt '[] 'HProb
logistic x v sig = recip (one + exp (negate (x - v) / fromProb sig))

seismic :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
seismic = gamma a1 b1

-- Recursive reasoning
hiddenState :: (ABT Term abt) => abt '[] ('HMeasure 'HInt)
hiddenState = categorical (mapV (unsafeProb . fromInt) $ rangeV 3)

-- eTest :: (ABT Term abt) => Expect (abt '[]) 'HProb -> abt '[] 'HProb
-- eTest n = runExpect (dirac n)

-- Lifted inference
n :: Int
n = 10 -- [10,20,40,80,160,320,640,1280,2560,5120]

k :: (ABT Term abt) => abt '[] 'HInt
k = 2 -- [1,2,4,8,16,32,64]

liftedInference :: (ABT Term abt) => abt '[] ('HMeasure ('HInt, Bool))
liftedInference =
    bern 0.01 >>= \cause ->
    replicateH n (if_ cause (bern 0.6) (bern 0.05)) (\ effects ->
        dirac $
            foldl (\ sum_ e ->
                sum_ + (if_ e 1 0)) 0 effects
    ) >>= \sum_ ->
    dirac (pair sum_ cause)

testLiftedInference :: (ABT Term abt) => abt '[] ('HInt ':-> 'HMeasure Bool)
testLiftedInference =
    app (L.runDisintegrate (\u -> ununit u $ liftedInference) !! 0)
        unit
