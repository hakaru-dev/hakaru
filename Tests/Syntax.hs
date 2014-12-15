{-# LANGUAGE TypeFamilies, Rank2Types, FlexibleContexts #-}
{-# OPTIONS -W #-}

module Tests.Syntax(allTests) where

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Real, Prob, Measure,
       Order(..), Base(..), ununit, and_, fst_, snd_, min_,
       Mochastic(..), Lambda(..), bind_, beta, bern, lam,
       if_, true, false, Bool_)
import Language.Hakaru.Util.Pretty (Pretty (pretty), prettyPair)
import Language.Hakaru.Sample(Sample(unSample))
import Language.Hakaru.Disintegrate

import Control.Monad (zipWithM_, replicateM)
import Control.Applicative (Const(Const))
import Text.PrettyPrint (text, (<>), ($$), nest)

import qualified Data.Number.LogFloat as LF
import qualified System.Random.MWC as MWC

import Test.HUnit
import Tests.TestTools


allTests :: Test
allTests = test [
    "pair1fst" ~: testS pair1fst,
    "pair1snd" ~: testS pair1snd,
    "pair2fst" ~: testS pair2fst,
    "pair2snd" ~: testS pair2snd,
    -- "pair2'fst" ~: testS $ pair2'fst 10,
    -- "pair2'snd" ~: testS $ pair2'snd 10,
    -- "replicateH" ~: testS $ replicateH 10,
    "pair3fst" ~: testS $ pair3fst 1 [true,true,true],
    "pair3snd" ~: testS $ pair3snd 1 [true,true,true],
    "pair3trd" ~: testS $ pair3trd 1 [true,true,true],
    "pair4fst" ~: testS $ pair4fst,
    "pair4transition" ~: testS $ pair4transition $ pair true 1,
    "pair4'transition" ~: testS $ pair4'transition $ pair true 1,
    -- "transitionTest" ~: ignore $ transitionTest,
    "testDistWithSample" ~: do x <- testDistWithSample
                               mapM_ assertJust x,
    "testLinreg" ~: testS distLinreg,
    "prog1s" ~: map testS prog1s,
    "prog2s" ~: map testS prog2s,
    "prog3s" ~: map testS prog3s
    ]


-- pair1fst and pair1snd are equivalent
pair1fst :: (Mochastic repr) => repr (Measure (Bool_, Prob))
pair1fst =  beta 1 1 `bind` \bias ->
            bern bias `bind` \coin ->
            dirac (pair coin bias)
pair1snd :: (Mochastic repr) => repr (Measure (Bool_, Prob))
pair1snd =  bern (1/2) `bind` \coin ->
            if_ coin (beta 2 1) (beta 1 2) `bind` \bias ->
            dirac (pair coin bias)

-- pair2fst and pair2snd are equivalent
pair2fst :: (Mochastic repr) => repr (Measure ((Bool_, Bool_), Prob))
pair2fst =  beta 1 1 `bind` \bias ->
            bern bias `bind` \coin1 ->
            bern bias `bind` \coin2 ->
            dirac (pair (pair coin1 coin2) bias)

pair2snd :: (Mochastic repr) => repr (Measure ((Bool_, Bool_), Prob))
pair2snd =  bern (1/2) `bind` \coin1 ->
            bern (if_ coin1 (2/3) (1/3)) `bind` \coin2 ->
            beta (1 + f coin1 + f coin2)
                 (1 + g coin1 + g coin2) `bind` \bias ->
            dirac (pair (pair coin1 coin2) bias)
  where f b = if_ b 1 0
        g b = if_ b 0 1

{-
type Cont repr a = forall w. (a -> repr (Measure w)) -> repr (Measure w)
-- This Cont monad is useful for generalizing pair2fst and pair2snd to an
-- arbitrary number of coin flips. The generalization would look liks this:

pair2'fst :: (Mochastic repr) => Int -> Cont repr ([repr Bool_], repr Prob)
-- REQUIREMENT: pair2fst = pair2'fst 2 (\([coin1,coin2],bias) -> dirac (pair (pair coin1 coin2) bias))
pair2'fst n k = beta 1 1 `bind` \bias ->
                replicateH n (bern bias) (\ coins -> k (coins, bias))

pair2'snd :: (Mochastic repr) => Int -> Cont repr ([repr Bool_], repr Prob)
pair2'snd = go 1 1 where
  go a b 0 k = beta a b `bind` \bias -> k ([],bias)
  go a b n k = bern (a/(a+b)) `bind` \c ->
               go (if_ c (a+1) a) (if_ c b (b+1)) (n-1) (\(cs,bias) ->
               k (c:cs,bias))

replicateH :: (Mochastic repr) => Int -> repr (Measure a) -> Cont repr [repr a]
replicateH 0 _ k = k []
replicateH n m k = m `bind` \x -> replicateH (n-1) m (\xs -> k (x:xs))

twice :: (Mochastic repr) => repr (Measure a) -> Cont repr (repr a, repr a)
twice m k = m `bind` \x ->
            m `bind` \y ->
            k (x, y)
-}

-- pair3fst and pair3snd and pair3trd are equivalent
pair3fst, pair3snd, pair3trd :: (Mochastic repr) => repr Prob -> [repr Bool_] -> repr (Measure ())
pair3fst bias [b1,b2,b3] =
  factor (if_ b1 bias (1-bias)) `bind_`
  factor (if_ b2 bias (1-bias)) `bind_`
  factor (if_ b3 bias (1-bias))
pair3fst _ _ = error "pair3fst: only implemented for 3 coin flips"
pair3snd bias [b1,b2,b3] =
  factor (if_ b1 bias (1-bias)
        * if_ b2 bias (1-bias)
        * if_ b3 bias (1-bias))
pair3snd _ _ = error "pair3fst: only implemented for 3 coin flips"
pair3trd bias [b1,b2,b3] =
  factor (pow_ bias     (if_ b1 1 0 + if_ b2 1 0 + if_ b3 1 0)
        * pow_ (1-bias) (if_ b1 0 1 + if_ b2 0 1 + if_ b3 0 1))
pair3trd _ _ = error "pair3fst: only implemented for 3 coin flips"

pair4fst :: (Mochastic repr) => repr (Measure Real)
pair4fst = bern (1/2) `bind` \coin ->
           if_ coin (normal 0 1) (uniform 0 1)

normalLogDensity :: Mochastic repr => repr Real -> repr Prob -> repr Real -> repr Real
normalLogDensity mu sd x = (-(fromProb tau) * square (x - mu)
                            + log_ (tau / pi_ / 2)) / 2
 where square y = y * y
       tau = recip (square sd)

uniformLogDensity :: Mochastic repr => repr Real -> repr Real -> repr Real -> repr Real
uniformLogDensity lo hi x = if_ (and_ [less lo x, less x hi])
                            (log_ (recip (unsafeProb (hi - lo))))
                            (log_ 0)

bernLogDensity :: Mochastic repr => repr Prob -> repr Bool_ -> repr Real
bernLogDensity p x = log_ (if_ x p (1 - p))

pair4transition :: Mochastic repr => repr (Bool_, Real) -> repr (Measure (Bool_,Real))
pair4transition state = bern (1/2) `bind` \resampleCoin ->
                           if_ resampleCoin
                           (bern (1/2) `bind` \coin' ->
                            densityCheck (coin',x))
                           (if_ coin
                            (normal 3 2 `bind` \y -> densityCheck (coin, y))
                            (uniform (-1) 1 `bind` \y -> densityCheck (coin, y)))
    where densityCheck (coin', x') = if_ (less (bernLogDensity (1/2) coin' +
                                                 (if_ coin'
                                                  (normalLogDensity 0 1 x')
                                                  (uniformLogDensity 0 1 x')) -
                                                 bernLogDensity (1/2) coin -
                                                 (if_ coin
                                                  (normalLogDensity 0 1 x)
                                                  (uniformLogDensity 0 1 x))) 0)
                                       (dirac state)
                                       (dirac (pair coin' x'))
          coin = fst_ state
          x = snd_ state

pair4'transition :: (Mochastic repr) => repr (Bool_, Real) -> repr (Measure (Bool_, Real))
pair4'transition state = bern (1/2) `bind` \resampleCoin ->
                           if_ resampleCoin
                           (bern (1/2) `bind` \coin' ->
                            (if_ coin'
                             (updateState (pair coin' x) $
                              uniformLogDensity 0 1 x - normalLogDensity 0 1 x)
                             (updateState (pair coin' x) $
                              normalLogDensity 0 1 x - uniformLogDensity 0 1 x)))
                           (if_ coin
                            (normal 3 2 `bind` \x' ->
                                 updateState (pair coin x')
                                   (normalLogDensity 0 1 x' - normalLogDensity 0 1 x))
                            (uniform (-1) 1 `bind` \x' ->
                                 updateState (pair coin x')
                                   (uniformLogDensity 0 1 x' - uniformLogDensity 0 1 x)))
    where updateState state' ratio = bern (min_ 1 (exp_ ratio)) `bind` \u ->
                                       if_ u (dirac state') (dirac state)
          coin = fst_ state
          x = snd_ state

{-
transitionTest :: MWC.GenIO -> IO (Maybe ((Bool_, Double), LF.LogFloat))
transitionTest g = unSample (pair4transition (pair true 1)) 1 g
-}

testDistWithSample :: IO [Maybe (Double, LF.LogFloat)]
testDistWithSample = do
  g <- MWC.create
  let prog2 = (head prog 0) 1
  replicateM 10 (unSample prog2 1 g)
 where prog = runDisintegrate $ \env ->
                                normal env 1 `bind` \x ->
                                normal x 1 `bind` \y ->
                                dirac (pair y x)

type Real5 = (Real, (Real, (Real, (Real, Real))))
type Real6 = (Real, (Real, (Real, (Real, (Real, Real)))))

make5Pair :: (Base repr) => repr a -> repr a -> repr a -> repr a -> repr a -> repr (a,(a,(a,(a,a))))
make5Pair x1 x2 x3 x4 x5 = pair x1
                                (pair x2
                                 (pair x3
                                  (pair x4
                                         x5)))

make6Pair :: (Base repr) => repr a -> repr a -> repr a -> repr a -> repr a -> repr a-> repr (a,(a,(a,(a,(a,a)))))
make6Pair x1 x2 x3 x4 x5 x6 = pair x1
                                (pair x2
                                 (pair x3
                                  (pair x4
                                   (pair x5
                                         x6))))

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
         dirac (pair (make6Pair x1 x2 x3 x4 x5 y) (make5Pair w1 w2 w3 w4 w5))

distLinreg :: (Lambda repr, Mochastic repr) => repr (Real6 -> (Measure Real5))
distLinreg = lam $ \ x -> (runDisintegrate (const linreg) !! 0) unit x

disintegrateTestRunner :: IO ()
disintegrateTestRunner = do
  testDist ( Bind (Leaf x) stdRandom
           $ Bind (Leaf y) stdRandom
           $ Dirac (Pair (exp' (Var x)) (Op2 Add (Var y) (Var x)))
           , Fst Root )
  testDist ( Bind (Leaf x) stdRandom
           $ Bind (Leaf y) stdRandom
           $ Dirac (Pair (exp' (Var x)) (Op2 Add (Var y) (Var x)))
           , Snd Root )
  testDist ( Bind (Leaf x) stdRandom
           $ Bind (Leaf y) stdRandom
           $ Bind (Leaf z) (max_ (Var x) (Var y))
           $ Dirac (Pair (Var z) (Pair (Var x) (Var y)))
           , Fst Root )
  testDist ( Bind (Leaf x) stdRandom
           $ Dirac (Pair (exp' (Var x)) (Op1 Neg (Var x)))
           , Fst Root )
  testDist ( Bind (Leaf x) (Choice [stdRandom, stdRandom])
           $ Bind (Leaf y) (Choice [stdRandom, stdRandom])
           $ Bind (Leaf z) (Choice [stdRandom, stdRandom])
           $ Dirac (Var x + Var y + Var z)
           , Root)
  testDist ( Bind (Leaf x) stdRandom
           $ Bind (Leaf y) stdRandom
           $ Dirac (Pair (Var x + Var y) (Var x - Var y))
           , Fst Root )
  testDist ( Bind (Leaf y) stdRandom
           $ Bind (Leaf x) stdRandom
           $ Dirac (Pair (Var x + Var y) (Bind (Leaf x) stdRandom (Dirac (Var y))))
           , Fst Root )
  testDist ( Bind (Leaf m) (Dirac (Bind (Leaf x) stdRandom (Dirac (Op2 Add 1 (Var x)))))
           $ Bind (Leaf x) (Var m)
           $ Bind (Leaf y) (Var m)
           $ Dirac (Pair (Var x) (Var y))
           , Fst Root )
  testDist ( Bind (Leaf m) (Bind (Leaf x) stdRandom (Dirac (Dirac (Op2 Add 1 (Var x)))))
           $ Bind (Leaf x) (Var m)
           $ Bind (Leaf y) (Var m)
           $ Dirac (Pair (Var x) (Var y))
           , Fst Root )
  where x, y, z :: Name Real
        x = Const "x"
        y = Const "y"
        z = Const "z"
        m :: Name (Measure Real)
        m = Const "m"
        exp' :: Expr Name Name Real -> Expr Name Name Real
        exp' = Op1 Exp

testDist :: (Expr Name Name (Measure t), Selector to t) -> IO ()
testDist (e,s) = do
  print (prettyPair (pretty' 0 e) (pretty' 0 s))
  let es = run (disintegrate e emptyEnv s (Var (Const 0)))
  putStrLn (show (length es) ++ " result(s):")
  zipWithM_ (\n d -> print (pretty n <> text "." $$ nest 3 (pretty' 0 d)))
            [1::Int ..]
            es
  putStrLn ""

-- Jacques on 2014-11-18: "From an email of Oleg's, could someone please
-- translate the following 3 programs into new Hakaru?"  The 3 programs below
-- are equivalent.
prog1s, prog2s, prog3s :: (Mochastic repr, Lambda repr) => [repr (Real -> Measure Bool_)]
prog1s = map lam 
         [ d unit
         | d <- runDisintegrate $ \u ->
                ununit u $
                bern 0.5 `bind` \c ->
                if_ c (normal 0 1)
                      (uniform 10 20) `bind` \x ->
                dirac (pair x c) ]

prog2s = map lam
         [ d unit
         | d <- runDisintegrate $ \u ->
                ununit u $
                bern 0.5 `bind` \c ->
                if_ c (normal 0 1)
                      (dirac 10 `bind` \d ->
                       uniform d 20) `bind` \x ->
                dirac (pair x c) ]
prog3s = map lam
         [ d unit
         | d <- runDisintegrate $ \u ->
                ununit u $
                bern 0.5 `bind` \c ->
                if_ c (normal 0 1)
                      (dirac false `bind` \e ->
                       uniform (10 + if_ e 1 0) 20) `bind` \x ->
                dirac (pair x c) ]
