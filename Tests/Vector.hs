module Tests.Vector where

import Prelude hiding (Real)
import Language.Hakaru.Syntax
import Language.Hakaru.Disintegrate (Disintegrate, runDisintegrate)
import Language.Hakaru.Expect (Expect(Expect), normalize)
import Tests.TestTools
import Test.HUnit

allTests :: Test
allTests = test [ "testUnrolling" ~: testUnrolling
                , "testUnity"     ~: testUnity
                , "testInside"    ~: testInside
                , "testPull"      ~: testPull
                , "testConj"      ~: testConj
                , "testPlateDirac"~: testPlateDirac ]

-- Test unrolling short product measures
testUnrolling :: Assertion
testUnrolling = testSS [rolled] unrolled
rolled, unrolled :: (Mochastic repr, Integrate repr) => repr (Measure Prob)
rolled = liftM sumVec (plate (vector 3 (\i ->
         liftM unsafeProb (uniform 0 (fromInt i)))))
unrolled = uniform 0 2 `bind` \x2 ->
           uniform 0 3 `bind` \x3 ->
           uniform 0 4 `bind` \x4 ->
           uniform 0 5 `bind` \x5 ->
           dirac (unsafeProb (x2 + x3 + x4 + x5))

-- Test that normalizing a vector makes its sum 1
testNorm1, testNorm2 :: Assertion
testNorm1 = testSS [liftM (sumVec . normalizeVector) (plate (vector 3 (\i ->
                    liftM unsafeProb (uniform 0 (fromInt i)))))]
                   (dirac 1)
testNorm2 = testSS [liftM sumVec (dirichlet (vector 3 (\i ->
                    unsafeProb (fromInt i))))]
                   (dirac 1)

-- Test that the product of probability measures is a probability measure
testUnity :: Assertion
testUnity = testSS [unity] count
count, unity :: (Mochastic repr) => repr (Measure Int)
count = categorical' [(1, 20), (1, 30), (1, 40)]
unity = count `bind` \n ->
        plate (vector n (\i -> bern (recip (unsafeProb (fromInt i))))) `bind_`
        dirac n

-- Test simplification of measure inside vector and product
testInside :: Assertion
testInside = do testSS [      norm_nox_s]        norm_nox_s'
                testSS [plate norm_nox_s] (plate norm_nox_s')
norm_nox_s, norm_nox_s' :: (Mochastic repr) => repr (Vector (Measure Real))
norm_nox_s  = vector 20 (\i -> normal (fromInt i) 1 `bind` \x ->
                                  normal x 1 `bind` \y ->
                                  dirac y)
norm_nox_s' = vector 20 (\i -> normal (fromInt i) (sqrt_ 2))

-- Test pulling scalar factors out of product measure
testPull :: Assertion
testPull = testSS
  [plate (vector 20 (\i -> weight (exp_ (fromInt i))
                               $ normal (fromInt i) 1))]
  (plate (vector 20 (\i -> normal (fromInt i) 1)))

-- Test conjugacy of dirichlet and categorical
testConj :: Assertion
testConj = testSS
  [lam $ \as -> lam $ \coin -> normalize (d (Expect as) (Expect coin))]
  (lam $ \as -> lam $ \coin -> posterior as coin)
  where d:_ = runDisintegrate joint
instance Integrate Disintegrate -- UNDEFINED
instance Lambda Disintegrate -- UNDEFINED
joint :: (Mochastic repr, Integrate repr, Lambda repr) =>
         repr (Vector Prob) -> repr (Measure (Int, Vector Prob))
joint as = dirichlet as `bind` \bias ->
           categorical bias `bind` \coin ->
           dirac (pair coin bias)
posterior :: (Mochastic repr, Integrate repr, Lambda repr) =>
              repr (Vector Prob) -> repr Int -> repr (Measure (Vector Prob))
posterior as coin =
  dirichlet (mapWithIndex (\i a -> a + if_ (equal coin i) 1 0) as)

-- A plate full of diracs is a pure vector
testPlateDirac :: Assertion
testPlateDirac = testSS [plateDirac] plateDirac'
plateDirac, plateDirac' :: (Mochastic repr) => repr (Measure (Vector Real))
plateDirac = plate (vector 10 (dirac . fromInt))
plateDirac' = dirac (vector 10 fromInt)
