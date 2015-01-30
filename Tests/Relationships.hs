{-# LANGUAGE TypeFamilies, Rank2Types, FlexibleContexts #-}
module Tests.Relationships (allTests) where

import Prelude hiding (Real)

import Language.Hakaru.Syntax

import Test.HUnit
import Tests.TestTools

testRelationships :: Test
testRelationships = test [
    "t1"   ~: testSS [t1] (lam (\mu -> (lam (\sigma -> normal 0 1)))),
    "t2"   ~: testSS [t2] (lam (\beta -> chi2 (2*beta))),
    "t3"   ~: testSS [t3] (lam (\alpha -> (lam (\beta -> chi2 (2*beta))))),
    "t4"   ~: testSS [t4] (lam (\a -> lam (\b -> lam (\t -> beta a b))))
    ]

allTests :: Test
allTests = test [
    testRelationships
    ]

t1 :: (Lambda repr, Mochastic repr) => repr (Real -> Prob -> Measure Real)
t1 = lam (\mu -> (lam (\sigma -> normal mu sigma `bind` \x -> dirac ((x - mu) / (fromProb sigma)))))

t2 :: (Lambda repr, Mochastic repr) => repr (Prob -> Measure Prob)
t2 = (lam (\beta -> gamma 2 beta))

t3 :: (Lambda repr, Mochastic repr) => repr (Prob -> Prob -> Measure Prob)
t3 = lam (\alpha -> (lam (\beta -> gamma alpha beta `bind` \x -> dirac (2 * x / alpha))))

t4 :: (Lambda repr, Mochastic repr) => repr (Prob -> Prob -> Prob -> Measure Prob)
t4 = lam (\a -> lam (\b -> lam (\t -> gamma a t `bind` \x1 -> gamma b t `bind` \x2 -> dirac (x1/(x1+x2)))))
