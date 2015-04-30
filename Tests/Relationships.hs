{-# LANGUAGE TypeFamilies, Rank2Types, FlexibleContexts #-}
module Tests.Relationships (allTests) where

import Prelude hiding (Real)

import Language.Hakaru.Syntax

import Test.HUnit
import Tests.TestTools

testRelationships :: Test
testRelationships = test [
    "t1"   ~: testSS [t1] (lam (\_ -> (lam (\_ -> normal 0 1)))),
    "t2"   ~: testSS [t2] (lam (\b -> gamma b 2)),
    "t3"   ~: testSS [t3, t3'] (lam (\_ -> (lam (\b -> gamma 2 b)))),
    "t4"   ~: testSS [t4] (lam (\a -> lam (\b -> lam (\t -> beta a b)))),
    "t5"   ~: testSS [t5, t5'] (lam (\alpha -> gamma 1 alpha)),
    --"t6"   ~: testSS [t5] (lam (\mu -> poisson mu `bind` \x -> dirac (fromInt x))),
    "t7"   ~: testSS [t7] (normal 0 1 `bind` \x1 ->
                           normal 0 1 `bind` \x2 ->
                           dirac (x1 * recip x2)),
    "t8"   ~: testSS [t8] (lam (\a -> (lam (\alpha ->
                           (normal 0 1 `bind` \x1 ->
                           normal 0 1 `bind` \x2 ->
                           dirac (a + (fromProb alpha) * (x1 / x2))))))),
    "t9"   ~: testSS [t9] (lam (\p -> bern p `bind` \x -> dirac (if_ x 1 0))),
    "t10"  ~: testSS [t10] (uniform 0 1 `bind` \x -> dirac (unsafeProb x)),
    "t11"  ~: testSS [t11] (lam (\a1 -> (lam (\a2 ->
                            gamma 1 (unsafeProb a1) `bind` \x1 ->
                            gamma 1 a2 `bind` \x2 ->
                            dirac ((fromProb (x1-x2))))))),

    -- sum of n exponential(b) random variables is a gamma(n, b) random variable
    "t12"   ~: testSS [t12] (lam (\b -> gamma 2 b)),

    --  Weibull(1, b) random variable is an exponential random variable with mean b
    "t13"   ~: testSS [t13] (lam (\b -> exponential (recip b))),

    -- If X is a standard normal random variable and U is a chi-squared random variable with v degrees of freedom,
    -- then X/sqrt(U/v) is a Student's t(v) random variable
    "t14"   ~: testSS [t14] (lam (\v -> student 0 v)),

    "t15"   ~: testSS [t15] (lam (\k -> (lam (\t -> gamma k t)))),

    -- Linear combination property
    "t16"   ~: testSS [t16] (normal 0 (sqrt_ 2)),
    "t17"   ~: testSS [t17] (lam (\mu -> lam (\sigma ->
                             normal mu (sqrt_ (1 + sigma * sigma))))),
    "t18"   ~: testSS [t18] (lam (\a1 -> lam (\a2 ->
                             normal 0 (sqrt_ (a1 * a1 + a2 * a2))))),

    -- Convolution property
    "t19"   ~: testSS [t19] (lam (\n1 -> lam (\n2 -> lam (\p ->
                             binomial (n1 + n2) p)))),
    "t20"   ~: testSS [t20] (lam (\n -> lam (\p ->
                             binomial n p))),
    "t21"   ~: testSS [t21] (lam (\l1 -> lam (\l2 ->
                             poisson (l1 + l2)))),
    "t22"   ~: testSS [t22] (lam (\a1 -> lam (\a2 -> lam (\b ->
                             gamma (a1 + a2) b)))),
    "t23"   ~: testSS [t23] (lam (\n -> lam (\t ->
                             gamma n t))),

    -- Scaling property
    "t24"   ~: testSS [t24] (lam (\a -> lam (\b -> lam (\k ->
                             weibull (a*(pow_ k (fromProb b))) b)))),

    -- Product property
    "t25"   ~: testSS [t25] (lam (\mu1 -> lam (\mu2 ->
                             lam (\sigma1 -> lam (\sigma2 ->
                             normal (mu1+mu2) (sigma1+sigma2) `bind` \x ->
                             dirac (log x)))))),

    -- Inverse property
    "t26"   ~: testSS [t26] (lam (\l -> lam (\s ->
                             cauchy (l / (l*l + fromProb (s*s))) (s / (unsafeProb (l*l) + s*s))))),

    -- Multiple of a random variable
    "t27"   ~: testSS [t27] (lam (\r -> lam (\lambda -> lam (\a ->
                             gamma r (a*lambda))))),

    -- If X is a beta (a, b) random variable then (1 - X) is a beta (b, a) random variable.
    "t28"   ~: testSS [t28] (lam (\a -> lam (\b ->
                             beta b a))),

    -- If X is a binomial (n, p) random variable then (n - X) is a binomial (n, 1-p) random variable.
    "t29"   ~: testSS [t29] (lam (\n -> lam (\p ->
                             binomial n (1-p))))
    ]

allTests :: Test
allTests = test [
    testRelationships
    ]

t1 :: (Lambda repr, Mochastic repr) => repr (Real -> Prob -> Measure Real)
t1 = lam (\mu -> (lam (\sigma ->
    normal mu sigma `bind` \x ->
    dirac ((x - mu) / (fromProb sigma)))))

t2 :: (Lambda repr, Mochastic repr) => repr (Prob -> Measure Prob)
t2 = lam (\b -> chi2 (2*b))

t3 :: (Lambda repr, Mochastic repr) => repr (Prob -> Prob -> Measure Prob)
t3 = lam (\alpha -> (lam (\bet ->
    gamma alpha bet `bind` \x ->
    dirac (2 * x / alpha))))

t3' :: (Lambda repr, Mochastic repr) => repr (Prob -> Prob -> Measure Prob)
t3' = lam (\_ -> (lam (\bet -> chi2 (2*bet))))

t4 :: (Lambda repr, Mochastic repr) => repr (Prob -> Prob -> Prob -> Measure Prob)
t4 = lam (\a -> lam (\b -> lam (\t -> 
    gamma a t `bind` \x1 ->
    gamma b t `bind` \x2 ->
    dirac (x1/(x1+x2)))))

t5 :: (Lambda repr, Mochastic repr) => repr (Prob -> Measure Prob)
t5 = lam (\alpha ->
    uniform 0 1 `bind` \x ->
    dirac (-alpha * unsafeProb(log_ (unsafeProb x))))

t5' :: (Lambda repr, Mochastic repr) => repr (Prob -> Measure Prob)
t5' = lam (\alpha ->
    laplace (fromProb alpha) alpha `bind` \x ->
    dirac (abs (unsafeProb x)))

-- Untestable right now with mu -> infinity, maybe later?
--t6 :: (Lambda repr, Mochastic repr) => repr (Prob -> Measure Real)
--t6 = lam (\mu -> normal infinity mu)

t7 :: (Mochastic repr) => repr (Measure Real)
t7 = cauchy 0 1

t8 :: (Lambda repr, Mochastic repr) => repr (Real -> Prob -> Measure Real)
t8 = (lam (\a -> (lam (\alpha -> cauchy a alpha))))

t9 :: (Lambda repr, Mochastic repr) => repr (Prob -> Measure Int)
t9 = lam (\p -> binomial 1 p)

t10 :: (Mochastic repr) => repr (Measure Prob)
t10 = beta 1 1

t11 :: (Lambda repr, Mochastic repr) => repr (Real -> Prob -> Measure Real)
t11 = lam (\a1 -> (lam (\a2 -> laplace a1 a2)))

t12 :: (Lambda repr, Mochastic repr) => repr (Prob -> Measure Prob)
t12 = lam (\b ->
    exponential b `bind` \x1 ->
    exponential b `bind` \x2 ->
    dirac (x1+x2))

t13 :: (Lambda repr, Mochastic repr) => repr (Prob -> Measure Prob)
t13 = lam (\b -> weibull 1 b)

t14 :: (Lambda repr, Mochastic repr) => repr (Prob -> Measure Real)
t14 = lam (\v -> normal 0 1 `bind` \x ->
    chi2 v `bind` \u ->
    dirac (x/fromProb(sqrt_(u/v))))

t15 :: (Lambda repr, Mochastic repr) => repr (Prob -> Prob -> Measure Prob)
t15 = lam (\k -> (lam (\t ->
    invgamma k (recip t) `bind` \x ->
    dirac (recip x))))

t16 :: (Mochastic repr) => repr (Measure Real)
t16 = normal 0 1 `bind` \x1 ->
    normal 0 1 `bind` \x2 ->
    dirac (x1+x2)

t17 :: (Lambda repr, Mochastic repr) => repr (Real -> Prob -> Measure Real)
t17 = lam (\mu -> (lam (\sigma ->
    normal 0 1 `bind` \x1 ->
    normal mu sigma `bind` \x2 ->
    dirac (x1+x2))))

t18 :: (Lambda repr, Mochastic repr) => repr (Prob -> Prob -> Measure Real)
t18 = lam (\a1 -> (lam (\a2 ->
    normal 0 1 `bind` \x ->
    dirac ((fromProb a1) * x + (fromProb a2) * x))))

t19 :: (Lambda repr, Mochastic repr) => repr (Int -> Int -> Prob -> Measure Int)
t19 = lam (\n1 -> lam (\n2 -> lam (\p ->
    binomial n1 p `bind` \x1 ->
    binomial n2 p `bind` \x2 ->
    dirac (x1 + x2))))

t20 :: (Lambda repr, Mochastic repr) => repr (Int -> Prob -> Measure Int)
t20 = lam (\n -> lam (\p ->
    bern p `bind` \x ->
    dirac (n * (if_ x 1 0))))

t21 :: (Lambda repr, Mochastic repr) => repr (Prob -> Prob -> Measure Int)
t21 = lam (\l1 -> lam (\l2 ->
    poisson l1 `bind` \x1 ->
    poisson l2 `bind` \x2 ->
    dirac (x1 + x2)))

t22 :: (Lambda repr, Mochastic repr) => repr (Prob -> Prob -> Prob -> Measure Prob)
t22 = lam (\a1 -> lam (\a2 -> lam (\b ->
    gamma a1 b `bind` \x1 ->
    gamma a2 b `bind` \x2 ->
    dirac (x1 + x2))))

t23 :: (Lambda repr, Mochastic repr) => repr (Prob -> Prob -> Measure Prob)
t23 = lam (\n -> lam (\t ->
    exponential t `bind` \x ->
    dirac (n * x)))

t24 :: (Lambda repr, Mochastic repr) => repr (Prob -> Prob -> Prob -> Measure Prob)
t24 = lam (\a -> lam (\b -> lam (\k ->
    weibull a b `bind` \x ->
    dirac (k*x))))

t25 :: (Lambda repr, Mochastic repr) => repr (Real -> Real -> Prob -> Prob -> Measure Real)
t25 = lam (\mu1 -> lam (\mu2 ->
    lam (\sigma1 -> lam (\sigma2 ->
    normal mu1 sigma1 `bind` \x1 ->
    normal mu2 sigma2 `bind` \x2 ->
    dirac ((log x1) * (log x2))))))

t26 :: (Lambda repr, Mochastic repr) => repr (Real -> Prob -> Measure Real)
t26 = lam (\l -> lam (\s ->
    cauchy l s `bind` \x ->
    dirac (recip x)))

t27 :: (Lambda repr, Mochastic repr) => repr (Prob -> Prob -> Prob -> Measure Prob)
t27 = lam (\r -> lam (\lambda -> lam (\a ->
    gamma r lambda `bind` \x ->
    dirac (a * x))))

t28 :: (Lambda repr, Mochastic repr) => repr (Prob -> Prob -> Measure Prob)
t28 = lam (\a -> lam (\b ->
    beta a b `bind` \x ->
    dirac (1 - x)))

t29 :: (Lambda repr, Mochastic repr) => repr (Int -> Prob -> Measure Int)
t29 = lam (\n -> lam (\p ->
    binomial n p `bind` \x ->
    dirac (n - x)))
