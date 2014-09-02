{-# LANGUAGE MultiParamTypeClasses, TypeFamilies,
             FlexibleContexts, FlexibleInstances, DefaultSignatures,
             StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# OPTIONS -W #-}
import Prelude hiding (Real)
import Language.Hakaru.Syntax3

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

t8 :: Mochastic repr => repr (Measure (Real, Real))
t8 = normal 0 10 `bind` \x -> normal 5 20 `bind` \y -> dirac (pair x y)

t9 :: Mochastic repr => repr (Measure Real)
t9 = lebesgue `bind` \x -> factor (if_ (and_ [less 3 x, less x 7]) (1/2) 0) `bind_` dirac x

tester :: Expect Maple a -> String
tester t = unMaple (unExpect t) 0

-- this can sometimes be more convenient
tester2 :: (Expect' c ~ (b -> a)) => Maple b -> Expect Maple c -> String
tester2 c t = unMaple ((unExpect t) `app` c) 0

p1 :: String
p1 = tester2 (Maple (\_ -> "c")) t1

