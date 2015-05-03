module Tests.Function(allTests) where

import Prelude hiding (Real)

import Language.Hakaru.Syntax
import Language.Hakaru.Expect (unExpect)

import Test.HUnit
import Tests.TestTools

testHigherOrder :: Test
testHigherOrder = test [
    "t41"            ~: testS t41,
    "pairFun"        ~: testSS [] (pair (lam exp_) pi_),
    "pairFunSimp"    ~: testSS [pair (lam exp_) (lam (log_.exp_))]
                               (pair (lam exp_) (lam id)),
    "unknownMeasure" ~: testSS [lam $ \m ->
                                normal 0 1 `bind_`
                                asTypeOf m (dirac (pair pi_ pi_))]
                               (lam id)
    ]

allTests :: Test
allTests = testHigherOrder

t41 :: (Lambda repr, Integrate repr, Mochastic repr) => repr (Measure ((Prob -> Prob) -> Prob))
t41 = dirac $ snd_ $ unExpect $ uniform 0 2 `bind` dirac . unsafeProb

