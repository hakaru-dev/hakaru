{-# LANGUAGE TypeFamilies, Rank2Types #-}
{-# OPTIONS -W #-}

-- module Tests.Syntax where

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Real, Prob, Measure,
       Order(..), Base(..), ununit, and_, fst_, snd_, min_,
       Mochastic(..), bind_, beta, bern,
       if_, true, Bool_,
       Lambda(..), Summate(..), Integrate(..))
import Language.Hakaru.Util.Pretty (Pretty (pretty), prettyPair)
import Language.Hakaru.Expect (Expect(unExpect), Expect')
import Language.Hakaru.Maple (Maple(Maple), runMaple)
import Language.Hakaru.Sample(Sample(unSample))
import Language.Hakaru.Disintegrate
import Language.Hakaru.PrettyPrint (runPrettyPrint)

import Control.Monad (zipWithM_, replicateM)
import Control.Applicative (Const(Const))
import Text.PrettyPrint (text, (<>), ($$), nest)

import qualified Data.Number.LogFloat as LF
import qualified System.Random.MWC as MWC

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
                            (normal 3 2 `bind` \x -> densityCheck (coin, x))
                            (uniform (-1) 1 `bind` \x -> densityCheck (coin, x)))
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

transitionTest :: MWC.GenIO -> IO (Maybe ((Bool_, Double), LF.LogFloat))
transitionTest g = unSample (pair4transition (pair true 1)) 1 g

mcmc :: (Mochastic repr, Summate repr, Integrate repr, Lambda repr,
         a ~ Expect' a) =>
        (forall repr'. (Mochastic repr') => repr' a -> repr' (Measure a)) ->
        (forall repr'. (Mochastic repr') => repr' (Measure a)) ->
        repr (a -> Measure a)
mcmc q p =
  let_ (lam (dp unit)) $ \density_p ->
  let_ (lam (\y -> lam (dq y))) $ \density_q ->
  lam $ \x ->
    q x `bind` \ x' ->
    let_ (min_ 1 (density_p `app` x' / density_q `app` x `app` x' *
                  density_q `app` x' `app` x / density_p `app` x)) $ \ratio ->
    bern ratio `bind` \accept ->
    dirac (if_ accept x' x)
  where dp:_ = density (\dummy -> ununit dummy p)
        dq:_ = density q

testMcmc :: IO ()
testMcmc = print (runPrettyPrint (mcmc (`normal` 1) (normal 0 5)))

testDistWithSample :: IO [Maybe (Double, LF.LogFloat)]
testDistWithSample = do
  g <- MWC.create
  let prog2 = (head prog 0) 1
  replicateM 10 (unSample prog2 1 g)
 where prog = runDisintegrate $ \env ->
                                normal env 1 `bind` \x ->
                                normal x 1 `bind` \y ->
                                dirac (pair y x)

-- In Maple, should 'evaluate' to "\c -> 1/2*c(Unit)"
t1 :: (Mochastic repr) => repr (Measure ())
t1 = uniform 0 1 `bind` \x -> factor (unsafeProb x)

t2 :: Mochastic repr => repr (Measure Prob)
t2 = beta 1 1

t3 :: Mochastic repr => repr (Measure Real)
t3 = normal 0 10

t4 :: Mochastic repr => repr (Measure (Prob, Bool_))
t4 = beta 1 1 `bind` \bias -> bern bias `bind` \coin -> dirac (pair bias coin)

-- t5 is "the same" as t1.
t5 :: Mochastic repr => repr (Measure ())
t5 = factor (1/2) `bind_` dirac unit

t6 :: Mochastic repr => repr (Measure Real)
t6 = dirac 5

t7 :: Mochastic repr => repr (Measure Real)
t7 = uniform 0 1 `bind` \x -> factor (unsafeProb (x+1)) `bind_` dirac (x*x)

-- For sampling efficiency (to keep importance weights at or close to 1),
-- t8 below should read back to uses of "normal", not uses of "lebesgue"
-- then "factor".  (For exact roundtripping, Maple "attributes" might help.)
t8 :: Mochastic repr => repr (Measure (Real, Real))
t8 = normal 0 10 `bind` \x -> normal x 20 `bind` \y -> dirac (pair x y)

t9 :: Mochastic repr => repr (Measure Real)
t9 = lebesgue `bind` \x -> factor (if_ (and_ [less 3 x, less x 7]) (1/2) 0) `bind_` dirac x

t10 :: Mochastic repr => repr (Measure ())
t10 = factor 0

t11 :: Mochastic repr => repr (Measure ())
t11 = factor 1

t12 :: Mochastic repr => repr (Measure ())
t12 = factor 2

t13 :: Mochastic repr => repr (Measure Real)
t13 = bern (3/5) `bind` \b -> dirac (if_ b 37 42)

t14 :: Mochastic repr => repr (Measure Real)
t14 = bern (3/5) `bind` \b ->
      if_ b t13 (bern (2/7) `bind` \b' ->
                 if_ b' (uniform 10 12) (uniform 14 16))

t20 :: (Lambda repr, Mochastic repr) => repr (Prob -> Measure ())
t20 = lam (\y -> uniform 0 1 `bind` \x -> factor (unsafeProb x * y))

t21 :: (Mochastic repr, Summate repr, Integrate repr, Lambda repr) =>
       repr (Real -> Measure Real)
t21 = mcmc (`normal` 1) (normal 0 5)

t22 :: Mochastic repr => repr (Measure ())
t22 = bern (1/2) `bind_` dirac unit

-- was called bayesNet in Nov.06 msg by Ken for exact inference
t23 :: Mochastic repr => repr (Measure (Bool_, Bool_))
t23 = bern (1/2) `bind` \a ->
               bern (if_ a (9/10) (1/10)) `bind` \b ->
               bern (if_ a (9/10) (1/10)) `bind` \c ->
               dirac (pair b c)

t24 :: (Mochastic repr, Lambda repr) => repr (Prob -> Measure ())
t24 = lam (\x ->
      uniform 0 1 `bind` \y ->
      uniform 0 1 `bind` \z ->
      factor (x * exp_ (cos y) * unsafeProb z))

t25 :: (Mochastic repr, Lambda repr) => repr (Prob -> Real -> Measure ())
t25 = lam (\x -> lam (\y -> 
    uniform 0 1 `bind` \z ->
    factor (x * exp_ (cos y) * unsafeProb z)))

t26 :: (Base repr, Lambda repr, Summate repr, Integrate repr) => repr Prob
t26 = unExpect t1 `app` lam (const 1)

t27 :: (Mochastic repr, Lambda repr) => [repr (Real -> Measure Real)]
t27 = map (\d -> lam (d unit)) $ runDisintegrate 
  (\env -> ununit env $ 
    normal 0 1 `bind` \x -> 
    normal x 1 `bind` \y -> 
    dirac (pair y x))

------- Tests

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


testMaple :: Expect Maple a -> String -> String
testMaple t pre = pre ++ " := " ++ res ++ ":"
  where res = runMaple (unExpect t) 0

-- this can sometimes be more convenient
testMaple2 :: (Expect' c ~ (b -> a)) => Maple b -> Expect Maple c -> String
testMaple2 c t = runMaple ((unExpect t) `app` c) 0

p1 :: String
p1 = testMaple2 (Maple (return "c")) t1

-- over time, this should be 'upgraded' to actually generate a proper
-- Maple test file
main :: IO ()
main = do
  putStrLn $ testMaple t1 "t1"
  putStrLn $ testMaple t2 "t2"
  putStrLn $ testMaple t3 "t3"
  putStrLn $ testMaple t4 "t4"
  putStrLn $ testMaple t5 "t5"
  putStrLn $ testMaple t6 "t6"
  putStrLn $ testMaple t7 "t7"
  putStrLn $ testMaple t8 "t8"
  putStrLn $ testMaple t9 "t9"
  putStrLn $ testMaple t10 "t10"
  putStrLn $ testMaple t11 "t11"
  putStrLn $ testMaple t12 "t12"
  putStrLn $ testMaple t13 "t13"
  putStrLn $ testMaple t14 "t14"
  putStrLn $ testMaple t20 "t20"
  putStrLn $ testMaple t21 "t21"
  putStrLn $ testMaple t22 "t22"
  putStrLn $ testMaple t23 "t23"
  putStrLn $ testMaple t24 "t24"
  putStrLn $ testMaple t25 "t25"
  putStrLn $ testMaple t26 "t26"
  putStrLn $ concat $ map (\x -> testMaple x "t27") t27
  putStrLn $ testMaple expr1 "expr1"
  putStrLn $ testMaple expr2 "expr2"
  putStrLn $ testMaple expr4 "expr4"
  putStrLn $ testMaple testKernel "testKernel"
  putStrLn $ testMaple testKernel2 "testKernel2"

-- this introduced too much noise in output, move it 
main2 :: IO ()
main2 = do
  disintegrateTestRunner

-- pull out some of the intermediate expressions for independent study
expr1 :: (Lambda repr, Mochastic repr) => repr (Real -> Prob)
expr1 =  (lam $ \x0 ->
          (lam $ \x1 ->
           lam $ \x2 ->
           lam $ \x3 ->
           (lam $ \x4 ->
            0
            + 1
              * (lam $ \x5 ->
                 (lam $ \x6 ->
                  0
                  + exp_ (-(x2 - 0) * (x2 - 0) / fromProb (2 * exp_ (log_ 5 * 2)))
                    / 5
                    / exp_ (log_ (2 * pi_) * (1 / 2))
                    * (lam $ \x7 -> x7 `app` unit) `app` x6)
                 `app` (lam $ \x6 ->
                        (lam $ \x7 ->
                         (lam $ \x8 -> x8 `app` x2)
                         `app` (lam $ \x8 ->
                                (lam $ \x9 ->
                                 (lam $ \x10 -> x10 `app` unit)
                                 `app` (lam $ \x10 ->
                                        (lam $ \x11 ->
                                         (lam $ \x12 -> x12 `app` x2)
                                         `app` (lam $ \x12 ->
                                                (lam $ \x13 -> x13 `app` pair x2 x10) `app` x11))
                                        `app` x9))
                                `app` x7))
                        `app` x5))
                `app` x4)
           `app` (lam $ \x4 ->
                  (lam $ \x5 -> x5 `app` (x4 `unpair` \x6 x7 -> x7)) `app` x3))
          `app` unit
          `app` x0
          `app` (lam $ \x1 -> 1))

expr2 :: (Mochastic repr, Lambda repr) => repr (Real -> Real -> Prob)
expr2 = (lam $ \x1 ->
          lam $ \x2 ->
          (lam $ \x3 ->
           lam $ \x4 ->
           lam $ \x5 ->
           (lam $ \x6 ->
            0
            + 1
              * (lam $ \x7 ->
                 (lam $ \x8 ->
                  0
                  + exp_ (-(x4 - x3) * (x4 - x3) / fromProb (2 * exp_ (log_ 1 * 2)))
                    / 1
                    / exp_ (log_ (2 * pi_) * (1 / 2))
                    * (lam $ \x9 -> x9 `app` unit) `app` x8)
                 `app` (lam $ \x8 ->
                        (lam $ \x9 ->
                         (lam $ \x10 -> x10 `app` x4)
                         `app` (lam $ \x10 ->
                                (lam $ \x11 ->
                                 (lam $ \x12 -> x12 `app` unit)
                                 `app` (lam $ \x12 ->
                                        (lam $ \x13 ->
                                         (lam $ \x14 -> x14 `app` x4)
                                         `app` (lam $ \x14 ->
                                                (lam $ \x15 -> x15 `app` pair x4 x12) `app` x13))
                                        `app` x11))
                                `app` x9))
                        `app` x7))
                `app` x6)
           `app` (lam $ \x6 ->
                  (lam $ \x7 -> x7 `app` (x6 `unpair` \x8 x9 -> x9)) `app` x5))
          `app` x1
          `app` x2
          `app` (lam $ \x3 -> 1))

-- the one we need in testKernel
expr3 :: (Mochastic repr, Lambda repr) => repr (d -> Prob) -> repr (d -> d -> Prob) -> repr d -> repr d -> repr Prob 
expr3 x0 x1 x2 x3 = (uneither (1
                    `less` x0 `app` x3 / x1 `app` x2 `app` x3 * x1 `app` x3 `app` x2
                           / x0 `app` x2)
                   (\x4 -> 1)
                   (\x4 ->
                    x0 `app` x3 / x1 `app` x2 `app` x3 * x1 `app` x3 `app` x2
                    / x0 `app` x2))

-- this is expr3 that we can send to Maple
expr4 :: (Lambda repr, Mochastic repr) => repr ((d -> Prob) -> (d -> d -> Prob) -> d -> d -> Prob)
expr4 = lam (\x0 -> lam (\x1 -> lam (\x2 -> lam (\x3 -> expr3 x0 x1 x2 x3))))

-- testKernel :: Sample IO (Real -> Measure Real)
testKernel :: (Lambda repr, Mochastic repr) => repr (Real -> Measure Real)
testKernel =
-- Below is the output of testMcmc as of 2014-11-05
    let_ expr1 $ \x0 ->
    let_ expr2 $ \x1 ->
    lam $ \x2 ->
    normal x2 1 `bind` \x3 ->
    let_ (expr3 x0 x1 x2 x3) $ \x4 ->
    categorical [(x4, inl unit), (1 - x4, inr unit)] `bind` \x5 ->
    dirac (uneither x5 (\x6 -> x3) (\x6 -> x2))

-- this should be equivalent to the above
testKernel2 :: (Lambda repr, Mochastic repr) => repr (Real -> Measure Real)
testKernel2 =
  lam $ \x2 ->
  normal x2 1 `bind` \x3 ->
  let_ (uneither (1 `less` exp_(-1/50*(x3-x2)*(x3+x2)))
                 (\x4 -> 1)
                 (\x4 -> exp_(-1/50*(x3-x2)*(x3+x2)))) $ \x4 ->
 categorical [(x4, x3), (1 - x4, x2)]
