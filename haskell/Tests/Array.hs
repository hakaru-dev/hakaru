{-# LANGUAGE DataKinds, NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Tests.Array (allTests) where

import Prelude ((.), id, ($), asTypeOf)

import Language.Hakaru.Syntax.Prelude
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Syntax.AST   (Term)
import Language.Hakaru.Syntax.ABT   (ABT)
import Language.Hakaru.Disintegrate (determine, disintegrate)
import Language.Hakaru.Expect       (normalize)

import Tests.TestTools
import Test.HUnit

allTests :: Test
allTests = test
    [ "testReduce"    ~: testSS [unreduced] reduced
    , "testUnrolling" ~: testSS [rolled] unrolled
    , "testUnity"     ~: testSS [unity] count
    , "testInside"    ~: testInside
    , "testPull"      ~: testPull
    , "t75"           ~: testSS [] t75
    , "testConj"      ~: testConj
    , "testPlateDirac"~: testPlateDirac
    ]

-- Test partial evaluation of reduce
unreduced, reduced
    :: (ABT Term abt) => abt '[] ('HInt ':-> 'HMeasure 'HInt)
unreduced = lam $ \n -> dirac (sumV (vector (nat_ 4) $ \i -> n + nat2int i))
reduced   = lam $ \n -> dirac (n * int_ 4 + int_ 6)

-- Test unrolling short product measures
rolled, unrolled :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
rolled =
    summateV `liftM` plate (vector (nat_ 4) $ \i ->
        unsafeProb `liftM` uniform zero (prob_ 2 + nat2prob i))
unrolled =
    uniform zero (prob_ 2) >>= \x2 ->
    uniform zero (prob_ 3) >>= \x3 ->
    uniform zero (prob_ 4) >>= \x4 ->
    uniform zero (prob_ 5) >>= \x5 ->
    dirac (unsafeProb (x2 + x3 + x4 + x5))

-- Test that normalizing a vector makes its sum 1
testNorm1, testNorm2 :: Assertion
testNorm1 = testSS
    [ (summateV . normalizeV) `liftM` plate (vector (nat_ 4) $ \i ->
        unsafeProb `liftM` uniform zero (prob_ 2 + nat2prob i))
    ]
    (dirac one)
testNorm2 = testSS
    [ summateV `liftM` dirichlet (vector (nat_ 4) $ \i ->
        prob_ 2 + nat2prob i) ]
    (dirac one)

-- Test that the product of probability measures is a probability measure
count, unity :: (ABT Term abt) => abt '[] ('HMeasure 'HNat)
count =
    categorical (vector (nat_ 3) $ \_ -> one) >>= \i ->
    dirac (i * nat_ 10 + nat_ 20)
unity =
    count >>= \n ->
    plate (vector n $ \i -> bern (recip (one + nat2prob i))) >>
    dirac n

-- Test simplification of measure inside vector and product
testInside :: Assertion
testInside = do
    testSS [      norm_nox_s]        norm_nox_s'
    testSS [plate norm_nox_s] (plate norm_nox_s')

norm_nox_s, norm_nox_s'
    :: (ABT Term abt) => abt '[] ('HArray ('HMeasure 'HReal))
norm_nox_s =
    vector (nat_ 21) $ \i ->
        normal (real_ 10 + nat2real i) one >>= \x ->
        normal x one >>= \y ->
        dirac y
norm_nox_s' = vector (nat_ 21) $ \i -> normal (10 + nat2real i) (sqrt_ 2)

-- Test pulling scalar factors out of product measure
testPull :: Assertion
testPull = testSS
    [ plate (vector (nat_ 21) $ \i ->
        weight (exp_ (nat2real i - real_ 10)) $
        normal (nat2real i - real_ 10) one)
    ]
    (plate (vector (nat_ 21) $ \i -> normal (nat2real i - real_ 10) one))

-- Test conjugacy of dirichlet and categorical
testConj :: Assertion
testConj = testSS
    [   lam $ \as ->
        lam $ \coin ->
        normalize (app (app d as) coin)
    ]
    (lam $ \as ->
    lam $ \coin ->
    posterior as coin)
    where
    d = maybe (error "testConj") id . determine $ disintegrate joint

joint
    :: (ABT Term abt)
    => abt '[] ('HArray 'HProb)
    -> abt '[] ('HMeasure (HPair 'HInt ('HArray 'HProb)))
joint as =
    dirichlet as >>= \bias ->
    categorical bias >>= \coin ->
    dirac (pair coin bias)

posterior
    :: (ABT Term abt)
    => abt '[] ('HArray 'HProb)
    -> abt '[] 'HNat
    -> abt '[] ('HMeasure ('HArray 'HProb))
posterior as coin =
    dirichlet (mapWithIndex (\i a -> a + if_ (coin == i) one zero) as)

-- A plate full of diracs is a pure vector
testPlateDirac :: Assertion
testPlateDirac = testSS [plateDirac] plateDirac'
plateDirac, plateDirac'
    :: (ABT Term abt) => abt '[] ('HMeasure ('HArray 'HProb))
plateDirac  = plate (vector (nat_ 10) (dirac . (one +) . nat2prob))
plateDirac' = dirac (vector (nat_ 10) ((one +) . nat2prob))

t75 :: (ABT Term abt) => abt '[] ('HMeasure ('HArray 'HReal))
t75 =
    poisson (prob_ 8) >>= \n ->
    plate (vector n $ \ _ -> normal zero one)


