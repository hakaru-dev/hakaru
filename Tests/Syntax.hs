{-# LANGUAGE MultiParamTypeClasses, TypeFamilies,
             FlexibleContexts, FlexibleInstances, DefaultSignatures,
             StandaloneDeriving, GeneralizedNewtypeDeriving,
             Rank2Types #-}
{-# OPTIONS -W #-}
import Prelude hiding (Real, repeat)
import Language.Hakaru.Syntax

pair1fst :: (Mochastic repr) => repr (Measure (Bool, Real))
pair1fst =  beta 1 1 `bind` \bias ->
            bern bias `bind` \coin ->
            dirac (pair coin bias)

pair1snd :: (Mochastic repr) => repr (Measure (Bool, Real))
pair1snd =  bern 0.5 `bind` \coin ->
            if_ coin (beta 2 1) (beta 1 2) `bind` \bias ->
            dirac (pair coin bias)

pair15fst :: (Mochastic repr) => repr (Measure ((Bool, Bool), Real))
pair15fst =  beta 1 1 `bind` \bias ->
             bern bias `bind` \coin1 ->
             bern bias `bind` \coin2 ->
             dirac (pair (pair coin1 coin2) bias)

pair15snd :: (Mochastic repr) => repr (Measure ((Bool, Bool), Real))
pair15snd =  bern 0.5 `bind` \coin1 ->
             bern (if_ coin1 (2/3) (1/3)) `bind` \coin2 ->
             beta (1 + f coin1 + f coin2)
                  (1 + g coin1 + g coin2) `bind` \bias ->
             dirac (pair (pair coin1 coin2) bias)
  where f b = if_ b 1 0
        g b = if_ b 0 1

type Cont repr a = forall w. (a -> repr (Measure w)) -> repr (Measure w)

pair18fst :: (Mochastic repr) => Int -> Cont repr ([repr Bool], repr Real)
-- REQUIREMENT: pair15fst = pair18fst 2 (\([coin1,coin2],bias) -> dirac (pair (pair coin1 coin2) bias))
pair18fst = undefined -- to be defined using replicateH

pair18snd :: (Mochastic repr) => Int -> Cont repr ([repr Bool], repr Real)
pair18snd = undefined -- to be defined using explicit recursion

replicateH :: (Mochastic repr) => Int -> repr (Measure a) -> Cont repr [repr a]
replicateH 0 _ k = k []
replicateH n m k = m `bind` \x -> replicateH (n-1) m (\xs -> k (x:xs))

twice :: (Mochastic repr) => repr (Measure a) -> Cont repr (repr a, repr a)
twice m k = m `bind` \x ->
            m `bind` \y ->
            k (x, y)

pair3fst, pair3snd, pair3trd :: (Mochastic repr) => repr Prob -> [repr Bool] -> repr (Measure ())
pair3fst bias [b1,b2,b3] =
  factor (if_ b1 bias (1-bias)) `bind_`
  factor (if_ b2 bias (1-bias)) `bind_`
  factor (if_ b3 bias (1-bias))
pair3snd bias [b1,b2,b3] =
  factor (if_ b1 bias (1-bias)
        * if_ b2 bias (1-bias)
        * if_ b3 bias (1-bias))
pair3trd bias [b1,b2,b3] =
  factor (pow_ bias     (if_ b1 1 0 + if_ b2 1 0 + if_ b3 1 0)
        * pow_ (1-bias) (if_ b1 0 1 + if_ b2 0 1 + if_ b3 0 1))

{- pair2fst,pair2snd doesn't work yet for lack of (1) repeat facility in Hakaru; (2) a generalization of said facility that makes non-iid choices -}

pair2fst :: (MochasticWithRepeat repr) => repr Real -> repr (Measure Real)
pair2fst flips =  beta 1 1 `bind` \bias ->
                  repeat flips (bern bias) `bind_`
                  dirac bias

pair2snd :: (MochasticWithRepeat repr) => repr Real -> repr (Measure Real)
pair2snd flips =  bern 0.5 `bind` \coin ->
                  if_ coin (beta (1+flips) 1) (beta 1 (1+flips)) `bind` \bias ->
                  dirac bias

-- In Maple, should 'evaluate' to "\c -> 1/2*c(Unit)"
t1 :: (Mochastic repr) => repr (Measure ())
t1 = uniform 0 1 `bind` \x -> factor (unsafeProb x)

t2 :: Mochastic repr => repr (Measure Real)
t2 = beta 1 1

t3 :: Mochastic repr => repr (Measure Real)
t3 = normal 0 10

t4 :: Mochastic repr => repr (Measure (Real, Bool))
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

tester :: Expect Maple a -> String
tester t = unMaple (unExpect t) 0

-- this can sometimes be more convenient
tester2 :: (Expect' c ~ (b -> a)) => Maple b -> Expect Maple c -> String
tester2 c t = unMaple ((unExpect t) `app` c) 0

p1 :: String
p1 = tester2 (Maple (\_ -> "c")) t1

-- over time, this should be 'upgraded' to actually generate a proper
-- Maple test file
main :: IO ()
main = do
  print $ tester t1
  print $ tester t2
  print $ tester t3
  print $ tester t4
  print $ tester t5
  print $ tester t6
  print $ tester t7
  print $ tester t8
  print $ tester t9
