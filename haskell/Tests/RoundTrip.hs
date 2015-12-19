{-# LANGUAGE NoImplicitPrelude
           , DataKinds
           , TypeFamilies
           , ScopedTypeVariables
           , FlexibleContexts
           #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Tests.RoundTrip where

import Prelude ((.), id, ($), asTypeOf)

import Language.Hakaru.Syntax.Prelude
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Syntax.AST (Term)
import Language.Hakaru.Syntax.ABT (ABT)
import Language.Hakaru.Expect     (total)
import Language.Hakaru.Inference  (priorAsProposal, mcmc, mh)

import qualified Examples.Seismic as SE

import Test.HUnit
import Tests.TestTools
import Tests.Models
    (uniform_0_1, normal_0_1, gamma_1_1, beta_1_1, t4, t4', norm, unif2)

testMeasureUnit :: Test
testMeasureUnit = test [
    "t1,t5"   ~: testSS [t1,t5] (factor half),
    "t10"     ~: testSS [t10] (superpose []),
    "t11,t22" ~: testSS [t11,t22] (dirac unit),
    "t12"     ~: testSS [] t12,
    "t20"     ~: testSS [t20] (lam $ \y -> factor (y * half)),
    "t24"     ~: testSS [t24] t24',
    "t25"     ~: testSS [t25] t25',
    "t44Add"  ~: testSS [t44Add] t44Add',
    "t44Mul"  ~: testSS [t44Mul] t44Mul',
    "t53"     ~: testSS [t53,t53'] t53'',
    "t54"     ~: testS t54,
    "t55"     ~: testSS [t55] t55',
    "t56"     ~: testSS [t56,t56'] t56'',
    "t57"     ~: testSS [t57] t57',
    "t58"     ~: testSS [t58] t58',
    "t59"     ~: testS t59,
    "t60"     ~: testSS [t60,t60'] t60'',
    "t62"     ~: testSS [t62] t62',
    "t63"     ~: testSS [t63] t63',
    "t64"     ~: testSS [t64,t64'] t64'',
    "t65"     ~: testSS [t65] t65',
    "t77"     ~: testSS [] t77
    ]

testMeasureProb :: Test
testMeasureProb = test [
    "t2"  ~: testSS [t2] (unsafeProb <$> uniform_0_1),
    "t26" ~: testSS [t26] (dirac half),
    "t30" ~: testSS [] t30,
    "t33" ~: testSS [] t33,
    "t34" ~: testSS [t34] (dirac 3),
    "t35" ~: testSS [t35] (lam $ \x -> if_ (x < 4) (dirac 3) (dirac 5)),
    "t38" ~: testSS [] t38,
    "t42" ~: testSS [t42] (dirac one),
    "t49" ~: testSS [] t49,
    "t61" ~: testSS [t61] t61',
    "t66" ~: testSS [] t66,
    "t67" ~: testSS [] t67,
    "t69x" ~: testSS [t69x] (dirac (fromRational (3/2))),
    "t69y" ~: testSS [t69y] (dirac (fromRational (7/2)))
    ]

testMeasureReal :: Test
testMeasureReal = test
    [ "t3"  ~: testSS [] t3
    , "t6"  ~: testSS [t6'] t6
    , "t7"  ~: testSS [t7] t7'
    , "t7n" ~: testSS [t7n] t7n'
    , "t8'" ~: testSS [t8'] (lam $ \s1 -> lam $ \s2 -> normal zero (sqrt (s1 ^ 2 + s2 ^ 2)))
    , "t9"  ~: testSS [t9] (superpose [(2, uniform 3 7)])
    , "t13" ~: testSS [t13] t13'
    , "t14" ~: testSS [t14] t14'
    , "t21" ~: testS t21
    , "t28" ~: testSS [] t28
    , "t29" ~: testSS [] t29
    , "t31" ~: testSS [] t31
    , "t32" ~: testSS [] t32
    , "t36" ~: testSS [t36] t36'
    , "t37" ~: testSS [] t37
    , "t39" ~: testSS [t39] t39'
    , "t40" ~: testSS [] t40
    , "t43" ~: testSS [t43, t43'] t43''
    , "t45" ~: testSS [t46,t47] t45
    , "t50" ~: testS t50
    , "t51" ~: testS t51
    , "t68" ~: testS t68
    , "t68'" ~: testS t68'
    , "t70a" ~: testSS [t70a] (uniform one 3)
    , "t71a" ~: testSS [t71a] (uniform one 3)
    , "t72a" ~: testSS [t72a] (weight half $ uniform one 2)
    , "t73a" ~: testSS [t73a] (superpose [])
    , "t74a" ~: testSS [t74a] (superpose [])
    , "t70b" ~: testSS [t70b] (superpose [])
    , "t71b" ~: testSS [t71b] (superpose [])
    , "t72b" ~: testSS [t72b] (weight half $ uniform 2 3)
    , "t73b" ~: testSS [t73b] (uniform one 3)
    , "t74b" ~: testSS [t74b] (uniform one 3)
    , "t70c" ~: testSS [t70c] (uniform one 3)
    , "t71c" ~: testSS [t71c] (uniform one 3)
    , "t72c" ~: testSS [t72c] (weight half $ uniform one 2)
    , "t73c" ~: testSS [t73c] (superpose [])
    , "t74c" ~: testSS [t74c] (superpose [])
    , "t70d" ~: testSS [t70d] (superpose [])
    , "t71d" ~: testSS [t71d] (superpose [])
    , "t72d" ~: testSS [t72d] (weight half $ uniform 2 3)
    , "t73d" ~: testSS [t73d] (uniform one 3)
    , "t74d" ~: testSS [t74d] (uniform one 3)
    , "t76" ~: testS t76
    , "t78" ~: testSS [t78] t78'
    , "t79" ~: testSS [t79] (dirac one)
    , "t80" ~: testS t80
    , "t81" ~: testSS [] t81
    , "kalman" ~: testS kalman
    -- , "seismic" ~: testSS [] seismic
    , "lebesgue1" ~: testSS [] (lebesgue >>= \x -> if_ (42 < x) (dirac x) (superpose []))
    , "lebesgue2" ~: testSS [] (lebesgue >>= \x -> if_ (x < 42) (dirac x) (superpose []))
    , "lebesgue3" ~: testSS [lebesgue >>= \x -> if_ (x < 42 && 40 < x) (dirac x) (superpose [])] (weight 2 $ uniform 40 42)
    , "testexponential" ~: testS testexponential
    , "testcauchy" ~: testS testCauchy
    , "exceptionLebesgue" ~: testSS [lebesgue >>= \x -> dirac (if_ (x == 3) one x)] lebesgue
    , "exceptionUniform"  ~: testSS [uniform 2 4 >>= \x -> dirac (if_ (x == 3) one x)] (uniform 2 4)
    -- "two_coins" ~: testS two_coins -- needs support for lists
    ]

testMeasureInt :: Test
testMeasureInt = test
    [ "t75"  ~: testS t75
    , "t75'" ~: testS t75'
    , "exceptionCounting" ~: testSS [] (counting >>= \x -> dirac (if_ (x == 3) one x)) -- Jacques wrote: "bug: [simp_pw_equal] implicitly assumes the ambient measure is Lebesgue"
    , "exceptionSuperpose" ~: testSS [(superpose [(third, dirac 2), (third, dirac 3), (third, dirac 4)] `asTypeOf` counting) >>= \x -> dirac (if_ (x == 3) one x)] (superpose [(third, dirac one), (third, dirac 2), (third, dirac 4)])
    ]

testMeasurePair :: Test
testMeasurePair = test [
    "t4"            ~: testSS [t4] t4',
    "t8"            ~: testSS [] t8,
    "t23"           ~: testSS [t23] t23',
    "t48"           ~: testS t48,
    "t52"           ~: testSS [t52] t52',
    "dup"           ~: testSS [dup normal_0_1] (liftM2 pair normal_0_1 normal_0_1),
    "norm"          ~: testSS [] norm,
    "norm_nox"      ~: testSS [norm_nox] (normal zero (sqrt 2)),
    "norm_noy"      ~: testSS [norm_noy] normal_0_1,
    "flipped_norm"  ~: testSS [liftM swap_ norm] flipped_norm,
    "priorProp"     ~: testSS [lam (priorAsProposal norm)]
                              (lam $ \x -> superpose [(half, normal_0_1         >>= \y -> dirac (pair y (snd x))),
                                                      (half, normal zero (sqrt 2) >>= \y -> dirac (pair (fst x) y))]),
    "mhPriorProp"   ~: testSS [testMHPriorProp] testPriorProp',
    "unif2"         ~: testS unif2,
    "easyHMM"       ~: testS easyHMM
--    "testMCMCPriorProp" ~: testS testMCMCPriorProp
    ]

testOther :: Test
testOther = test [
    "testRoadmapProg1" ~: testS rmProg1,
    "testRoadmapProg4" ~: testS rmProg4,
    "testKernel" ~: testSS [testKernel] testKernel2,
    "testFalseDetection" ~: testS (lam seismicFalseDetection),
    -- this doesn't typecheck because Either isn't Simplifiable yet:
    -- "testTrueDetection" ~: testS (lam2 seismicTrueDetection)
    "testTrueDetectionL" ~: testS tdl,
    "testTrueDetectionR" ~: testS tdr
    ]

allTests :: Test
allTests = test
    [ testMeasureUnit
    , testMeasureProb
    , testMeasureReal
    , testMeasurePair
    , testMeasureInt
    , testOther
    ]


----------------------------------------------------------------
-- Some common subexpressions

-- TODO: move to Prelude.hs
-- HACK: will throw errors if the input is negative and the required output is 'HProb'
fromRational
    :: forall abt a
    . (ABT Term abt, HFractional_ a)
    -> Rational
    => abt '[] a
fromRational =
    case (hFractional :: HFractional a) of
    HFractional_Prob -> prob_ . unsafeNonNegativeRational
    HFractional_Real -> real_

half :: (ABT Term abt, HFractional_ a) => abt '[] a
half = fromRational (1/2)

third :: (ABT Term abt, HFractional_ a) => abt '[] a
third = fromRational (1/3)

----------------------------------------------------------------
-- In Maple, should 'evaluate' to "\c -> 1/2*c(Unit)"
t1 :: (ABT Term abt) => abt '[] ('HMeasure HUnit)
t1 = uniform_0_1 >>= \x -> factor (unsafeProb x)

t2 :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
t2 = beta_1_1

t3 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t3 = normal zero 10

-- t5 is "the same" as t1.
t5 :: (ABT Term abt) => abt '[] ('HMeasure HUnit)
t5 = factor half >> dirac unit

t6, t6' :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t6 = dirac 5
t6' = superpose [(one, dirac 5)]

t7,t7', t7n,t7n' :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t7   = uniform_0_1 >>= \x -> factor (unsafeProb (x+one)) >> dirac (x*x)
t7'  = uniform_0_1 >>= \x -> superpose [(unsafeProb (x+one), dirac (x*x))]
t7n  =
    uniform (negate one) zero >>= \x ->
    factor (unsafeProb (x+one)) >>
    dirac (x*x)
t7n' =
    uniform (negate one) zero >>= \x ->
    superpose [(unsafeProb (x + one), dirac (x*x))]

-- For sampling efficiency (to keep importance weights at or close to 1),
-- t8 below should read back to uses of "normal", not uses of "lebesgue"
-- then "factor".
t8 :: (ABT Term abt) => abt '[] ('HMeasure (HPair 'HReal 'HReal))
t8 = normal zero 10 >>= \x -> normal x 20 >>= \y -> dirac (pair x y)

-- Normal is conjugate to normal
t8' :: (ABT Term abt)
    => abt '[] ('HProb ':-> 'HProb ':-> 'HMeasure 'HReal)
t8' =
    lam $ \s1 ->
    lam $ \s2 ->
    normal zero s1 >>= \x ->
    normal x s2

t9 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t9 =
    lebesgue >>= \x -> 
    factor (if_ (3 < x && x < 7) half zero) >> 
    dirac x

t10 :: (ABT Term abt) => abt '[] ('HMeasure HUnit)
t10 = factor zero

t11 :: (ABT Term abt) => abt '[] ('HMeasure HUnit)
t11 = factor one

t12 :: (ABT Term abt) => abt '[] ('HMeasure HUnit)
t12 = factor 2

t13,t13' :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t13 = bern (3/5) >>= \b -> dirac (if_ b 37 42)
t13' = superpose
    [ (fromRational (3/5), dirac 37)
    , (fromRational (2/5), dirac 42)
    ]

t14,t14' :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t14 =
    bern (3/5) >>= \b ->
    if_ b t13 (bern (2/7) >>= \b' ->
        if_ b' (uniform 10 12) (uniform 14 16))
t14' = superpose 
    [ (fromRational (9/25), dirac 37)
    , (fromRational (6/25), dirac 42)
    , (fromRational (4/35), uniform 10 12)
    , (fromRational (2/7) , uniform 14 16)
    ]

t20 :: (ABT Term abt) => abt '[] ('HProb ':-> 'HMeasure HUnit)
t20 = lam $ \y -> uniform_0_1 >>= \x -> factor (unsafeProb x * y)

t21 :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure 'HReal)
t21 = mcmc (`normal` one) (normal zero 5)

t22 :: (ABT Term abt) => abt '[] ('HMeasure HUnit)
t22 = bern half >> dirac unit

-- was called bayesNet in Nov.06 msg by Ken for exact inference
t23, t23' :: (ABT Term abt) => abt '[] ('HMeasure (HPair HBool HBool))
t23 =
    bern half >>= \a ->
    bern (if_ a (9/10) (1/10)) >>= \b ->
    bern (if_ a (9/10) (1/10)) >>= \c ->
    dirac (pair b c)
t23' = superpose
    [ (fromRational (41/100), dirac (pair true true))
    , (fromRational ( 9/100), dirac (pair true false))
    , (fromRational ( 9/100), dirac (pair false true))
    , (fromRational (41/100), dirac (pair false false))
    ]

t24,t24' :: (ABT Term abt) => abt '[] ('HProb ':-> 'HMeasure HUnit)
t24 =
    lam $ \x ->
    uniform_0_1 >>= \y ->
    uniform_0_1 >>= \z ->
    factor (x * exp (cos y) * unsafeProb z)
t24' =
    lam $ \x ->
    uniform_0_1 >>= \y ->
    factor (x * exp (cos y) * half)

t25,t25' :: (ABT Term abt)
    => abt '[] ('HProb ':-> 'HReal ':-> 'HMeasure HUnit)
t25 =
    lam $ \x ->
    lam $ \y ->
    uniform_0_1 >>= \z ->
    factor (x * exp (cos y) * unsafeProb z)
t25' =
    lam $ \x ->
    lam $ \y ->
    factor (x * exp (cos y) * half)

t26 :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
t26 = dirac (total t1)

t28 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t28 = uniform_0_1

t29 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t29 = exp <$> uniform_0_1

t30 :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
t30 = exp <$> uniform_0_1

t31 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t31 = uniform (negate one) one

t32 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t32 = exp <$> t31

t33 :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
t33 = exp <$> t31

t34 :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
t34 = dirac (if_ ((2 `asTypeOf` log one) < 4) 3 5)

t35 :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure 'HProb)
t35 = lam $ \x -> dirac (if_ ((x `asTypeOf` log one) < 4) 3 5)

t36, t36' :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure 'HReal)
t36 = lam (dirac . sqrt)
t36' = lam $ \x -> if_ (x < zero) (dirac (-337)) (dirac (sqrt x))

t37 :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure 'HReal)
t37 = lam (dirac . recip)

t38 :: (ABT Term abt) => abt '[] ('HProb ':-> 'HMeasure 'HProb)
t38 = lam (dirac . recip)

t39, t39' :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure 'HReal)
t39 = lam (dirac . log)
t39' = lam $ \x -> if_ (x < zero) (dirac (-337)) (dirac (log x))

t40 :: (ABT Term abt) => abt '[] ('HProb ':-> 'HMeasure 'HReal)
t40 = lam (dirac . log)

t42 :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
t42 = dirac . total $ (unsafeProb <$> uniform zero 2)

t43, t43', t43'' :: (ABT Term abt) => abt '[] (HBool ':-> 'HMeasure 'HReal)
t43   = lam $ \b -> if_ b uniform_0_1 (fromProb <$> beta_1_1)
t43'  = lam $ \b -> if_ b uniform_0_1 uniform_0_1
t43'' = lam $ \_ -> uniform_0_1

t44Add, t44Add', t44Mul, t44Mul'
    :: (ABT Term abt) => abt '[] ('HReal ':-> 'HReal ':-> 'HMeasure HUnit)
t44Add  = lam $ \x -> lam $ \y -> factor (unsafeProb (x * x) + unsafeProb (y * y))
t44Add' = lam $ \x -> lam $ \y -> factor (unsafeProb (x ** 2 + y ** 2))
t44Mul  = lam $ \x -> lam $ \y -> factor (unsafeProb (x * x * y * y))
t44Mul' = lam $ \x -> lam $ \y -> factor (unsafeProb (x ** 2) * unsafeProb (y ** 2))

-- t45, t46, t47 are all equivalent.
-- But t47 is worse than t45 and t46 because the importance weight generated by
-- t47 as a sampler varies between 0 and 1 whereas the importance weight generated
-- by t45 and t46 is always 1.  In general it's good to reduce weight variance.
t45 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t45 = normal 4 5 >>= \x -> if_ (x < 3) (dirac (x*x)) (dirac (x-one))

t46 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t46 = normal 4 5 >>= \x -> dirac (if_ (x < 3) (x*x) (x-one))

t47 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t47 = superpose
    [ (one, normal 4 5 >>= \x -> if_ (x < 3) (dirac (x*x)) (superpose []))
    , (one, normal 4 5 >>= \x -> if_ (x < 3) (superpose []) (dirac (x-one)))
    ]

t48 :: (ABT Term abt) => abt '[] (HPair 'HReal 'HReal ':-> 'HMeasure 'HReal)
t48 = lam $ \x -> uniform (-5) 7 >>= \w -> dirac ((fst x + snd x) * w)

t49 :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
t49 = gamma 0.01 0.35

t50 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t50 = uniform one 3 >>= \x -> normal one (unsafeProb x)

t51 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t51 = t31 >>= \x -> normal x one

-- Example 1 from Chang & Pollard's Conditioning as Disintegration
t52, t52' :: (ABT Term abt) => abt '[] ('HMeasure (HPair 'HReal (HPair 'HReal 'HReal)))
t52 =
    uniform_0_1 >>= \x ->
    uniform_0_1 >>= \y ->
    dirac (pair (max_ x y) (pair x y))
t52' =
    uniform_0_1 >>= \x2 ->
    superpose
        [   ( unsafeProb (one + (x2 * negate one))
            , uniform x2 one >>= \x4 -> dirac (pair x4 (pair x2 x4))
            )
        ,   ( unsafeProb x2
            , uniform zero x2 >>= \x4 -> dirac (pair x2 (pair x2 x4))
            )
        ]

t53, t53', t53'' :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure HUnit)
t53 =
    lam $ \x ->
    superpose
        [ (one, superpose
            [ (one,
                if_ (zero < x)
                    (if_ (x < one) (dirac unit) (superpose []))
                    (superpose []))
            ])
        , (one, if_ false (dirac unit) (superpose []))
        ]
t53' =
    lam $ \x ->
    superpose
        [ (one,
            if_ (zero < x)
                (if_ (x < one) (dirac unit) (superpose []))
                (superpose []))
        , (one, if_ false (dirac unit) (superpose []))
        ]
t53'' =
    lam $ \x ->
    if_ (zero < x && x < one) (dirac unit) (superpose [])

t54 :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure HUnit)
t54 =
    lam $ \x0 ->
    (   dirac x0 >>= \x1 ->
        (negate <$> uniform_0_1) >>= \x2 ->
        dirac (x1 + x2)
    ) >>= \x1 ->
    (   (   (dirac zero >>= \x2 ->
            dirac x1 >>= \x3 ->
            dirac (x2 < x3)
            ) >>= \x2 ->
        if_ x2
            (recip <$> dirac x1)
            (dirac zero)
        ) >>= \x2 ->
        factor (unsafeProb x2)
    ) >>
    (log <$> dirac x1) >>= \x3 ->
    (negate <$> dirac x3) >>= \x4 ->
    (
        (dirac zero >>= \x5 ->
        dirac x4 >>= \x6 ->
        dirac (x5 < x6)
        ) >>= \x5 ->
        if_ x5
            (   (dirac x4 >>= \x6 ->
                dirac one >>= \x7 ->
                dirac (x6 < x7)
                ) >>= \x6 ->
            if_ x6 (dirac one) (dirac zero)
            )
         (dirac zero)
    ) >>= \x5 ->
    factor (unsafeProb x5)

t55, t55' :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure HUnit)
t55 =
    lam $ \t ->
    uniform_0_1 >>= \x ->
    if_ (x < t) (dirac unit) (superpose [])
t55' =
    lam $ \t ->
    if_ (t < zero) (superpose []) $
    if_ (t < one) (factor (unsafeProb t)) $
    dirac unit

t56, t56', t56'' :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure HUnit)
t56 =
    lam $ \x0 ->
    (   dirac x0 >>= \x1 ->
        (negate <$> uniform_0_1) >>= \x2 ->
        dirac (x1 + x2)
    ) >>= \x1 ->
    (   (dirac zero >>= \x2 ->
        dirac x1 >>= \x3 ->
        dirac (x2 < x3)
        ) >>= \x2 ->
    if_ x2
        (   (dirac x1 >>= \x3 ->
            dirac one >>= \x4 ->
            dirac (x3 < x4)
            ) >>= \x3 ->
        if_ x3 (dirac one) (dirac zero))
        (dirac zero)
    ) >>= \x2 ->
    weight (unsafeProb x2) (dirac unit)
t56' =
    lam $ \x0 ->
    uniform_0_1 >>= \x1 ->
    if_ (x0 - one < x1 && x1 < x0)
        (dirac unit)
        (superpose [])
t56'' =
    lam $ \t ->
    if_ (t <= zero) (superpose []) $
    if_ (t <= one) (factor (unsafeProb t)) $
    if_ (t <= 2) (factor (unsafeProb (2 + t * negate one))) $
    superpose []

t57, t57' :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure HUnit)
t57 = lam $ \t -> superpose
    [ (one, if_ (t < one)  (dirac unit) (superpose []))
    , (one, if_ (zero < t) (dirac unit) (superpose [])) ]
t57' = lam $ \t -> 
    if_ (t < one && zero < t) (factor 2) (dirac unit)

t58, t58' :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure HUnit)
t58 = lam $ \t -> superpose
    [ (one, if_ (zero < t && t < 2) (dirac unit) (superpose []))
    , (one, if_ (one  < t && t < 3) (dirac unit) (superpose [])) ]
t58' = lam $ \t ->
    if_ (if_ (zero < t) (t < 2) false)
        (if_ (if_ (one < t) (t < 3) false)
            (weight 2 (dirac unit))
            (dirac unit))
        (if_ (if_ (one < t) (t < 3) false)
            (dirac unit)
            (superpose []))

t59 :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure HUnit)
t59 =
    lam $ \x0 ->
    ((recip <$> uniform_0_1) >>= \x1 ->
     (((dirac zero >>= \x2 ->
        dirac x1 >>= \x3 ->
        dirac (x2 < x3)) >>= \x2 ->
       if_ x2
           (dirac x1)
           (negate <$> dirac x1)) >>= \x2 ->
      weight (unsafeProb x2) (dirac unit)) >>
     dirac x0 >>= \x3 ->
     dirac x1 >>= \x4 ->
     dirac (x3 * x4)) >>= \x1 ->
    (dirac x1 >>= \x2 ->
     (negate <$> uniform_0_1) >>= \x3 ->
     dirac (x2 + x3)) >>= \x2 ->
    ((dirac zero >>= \x3 ->
      dirac x2 >>= \x4 ->
      dirac (x3 < x4)) >>= \x3 ->
     if_ x3
         ((dirac x2 >>= \x4 ->
           dirac one >>= \x5 ->
           dirac (x4 < x5)) >>= \x4 ->
          if_ x4 (dirac one) (dirac zero))
         (dirac zero)) >>= \x3 ->
    weight (unsafeProb x3) (dirac unit)

t60,t60',t60'' :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure HUnit)
t60 =
    lam $ \x0 ->
    (((uniform_0_1 >>= \x1 ->
       uniform_0_1 >>= \x2 ->
       dirac (x1 + x2)) >>= \x1 ->
      dirac (recip x1)) >>= \x1 ->
     (((dirac zero >>= \x2 ->
        dirac x1 >>= \x3 ->
        dirac (x2 < x3)) >>= \x2 ->
       if_ x2
           (dirac x1)
           (negate <$> dirac x1)) >>= \x2 ->
      weight (unsafeProb x2) (dirac unit)) >>
     dirac x0 >>= \x3 ->
     dirac x1 >>= \x4 ->
     dirac (x3 * x4)) >>= \x1 ->
    ((dirac zero >>= \x2 ->
      dirac x1 >>= \x3 ->
      dirac (x2 < x3)) >>= \x2 ->
     if_ x2
         ((dirac x1 >>= \x3 ->
           dirac one >>= \x4 ->
           dirac (x3 < x4)) >>= \x3 ->
          if_ x3 (dirac one) (dirac zero))
         (dirac zero)) >>= \x2 ->
    weight (unsafeProb x2) (dirac unit)
t60' =
    lam $ \x0 ->
    uniform_0_1 >>= \x1 ->
    uniform_0_1 >>= \x2 ->
    if_ (if_ (zero < x0 / (x2 + x1))
             (x0 / (x2 + x1) < one)
             false)
        (weight (unsafeProb ((x2 + x1) ** negate one)) (dirac unit))
        (superpose [])
t60'' =
    lam $ \x0 ->
    uniform_0_1 >>= \x1 ->
    uniform_0_1 >>= \x2 ->
    if_ (if_ (zero < x0 / (x2 + x1))
             (x0 / (x2 + x1) < one)
             false)
        (weight (recip (unsafeProb (x2 + x1))) (dirac unit))
        (superpose [])

t61, t61' :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure 'HProb)
t61 = lam $ \x -> if_ (x < zero) (dirac zero) $ dirac $ unsafeProb $ recip x
t61'= lam $ \x -> if_ (x < zero) (dirac zero) $ dirac $ recip $ unsafeProb x

-- "Special case" of t56
t62, t62' :: (ABT Term abt) => abt '[] ('HReal ':-> 'HReal ':-> 'HMeasure HUnit)
t62 = lam $ \t ->
      lam $ \x ->
      uniform_0_1 >>= \y ->
      if_ (zero < t/x - y && t/x - y < one)
          (dirac unit)
          (superpose [])
t62'= lam $ \t ->
      lam $ \x ->
      if_ (t/x <= zero) (superpose []) $
      if_ (t/x <= one) (factor (unsafeProb (t/x))) $
      if_ (t/x <= 2) (factor (unsafeProb (2-t/x))) $
      superpose []

-- "Scalar multiple" of t62
t63, t63' :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure HUnit)
t63 = lam $ \t ->
      uniform_0_1 >>= \x ->
      uniform_0_1 >>= \y ->
      if_ (zero < t/x - y && t/x - y < one)
          (factor (recip (unsafeProb x)))
          (superpose [])
t63'= lam $ \t ->
      uniform_0_1 >>= \x ->
      if_ (t/x <= zero) (superpose []) $
      if_ (t/x <= one) (factor (unsafeProb (t/x) / unsafeProb x)) $
      if_ (t/x <= 2) (factor (unsafeProb (2-t/x) / unsafeProb x)) $
      superpose []

-- Density calculation for (Exp (Log StdRandom)) and StdRandom
t64, t64', t64'' :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure HUnit)
t64 = lam $ \x0 ->
      (((dirac zero >>= \x1 ->
         dirac x0 >>= \x2 ->
         dirac (x1 < x2)) >>= \x1 ->
        if_ x1
            (recip <$> dirac x0)
            (dirac zero)) >>= \x1 ->
       weight (unsafeProb x1) (dirac unit)) >>
      (log <$> dirac x0) >>= \x2 ->
      ((exp <$> dirac x2) >>= \x3 ->
       weight (unsafeProb x3) (dirac unit)) >>
      (exp <$> dirac x2) >>= \x4 ->
      ((dirac zero >>= \x5 ->
        dirac x4 >>= \x6 ->
        dirac (x5 < x6)) >>= \x5 ->
       if_ x5
           ((dirac x4 >>= \x6 ->
             dirac one >>= \x7 ->
             dirac (x6 < x7)) >>= \x6 ->
            if_ x6 (dirac one) (dirac zero))
           (dirac zero)) >>= \x5 ->
      weight (unsafeProb x5) (dirac unit)
t64' =lam $ \x0 ->
      ((dirac zero >>= \x1 ->
        dirac x0 >>= \x2 ->
        dirac (x1 < x2)) >>= \x1 ->
       if_ x1
           ((dirac x0 >>= \x2 ->
             dirac one >>= \x3 ->
             dirac (x2 < x3)) >>= \x2 ->
            if_ x2 (dirac one) (dirac zero))
           (dirac zero)) >>= \x1 ->
      weight (unsafeProb x1) (dirac unit)
t64''=lam $ \x0 ->
      if_ (zero < x0) 
          (if_ (x0 < one)
               (dirac unit)
               (superpose []))
          (superpose [])

-- Density calculation for (Add StdRandom (Exp (Neg StdRandom))).
-- Maple can integrate this but we don't simplify it for some reason.
t65, t65' :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure HUnit)
t65 =
    lam $ \t ->
    uniform_0_1 >>= \x ->
    if_ (zero < t-x)
        (let_ (unsafeProb (t-x)) $ \t_x ->
        weight (recip t_x) $
        (if_ (zero < negate (log t_x) && negate (log t_x) < one)
            (dirac unit)
            (superpose [])))
        (superpose [])
t65' = lam $ \t ->
       if_ (t < exp (negate one)) (superpose [])
     $ if_ (t < one) (factor (unsafeProb (log t + one)))
     $ if_ (t < one + exp (negate one)) (dirac unit)
     $ if_ (t < 2) (factor (unsafeProb (negate (log (t - one)))))
     $ superpose []

t66 :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
t66 = dirac (sqrt (3 + sqrt 3))

t67 :: (ABT Term abt) => abt '[] ('HProb ':-> 'HReal ':-> 'HMeasure 'HProb)
t67 = lam $ \p -> lam $ \r -> dirac (exp (r * fromProb p))

t68 :: (ABT Term abt)
    => abt '[] ('HProb ':-> 'HProb ':-> 'HReal ':-> 'HMeasure 'HReal)
t68 =
    lam $ \x4 ->
    lam $ \x5 ->
    lam $ \x1 ->
    lebesgue >>= \x2 ->
    lebesgue >>= \x3 ->
    weight (exp (-(x2 - x3) * (x2 - x3)
                     * recip (fromProb (2 * exp (log x4 * 2))))
              * recip x4
              * recip (exp (log (2 * pi_) * half)))
             (weight (exp (-(x1 - x3) * (x1 - x3)
                             * recip (fromProb (2 * exp (log x5 * 2))))
                      * recip x5
                      * recip (exp (log (2 * pi_) * half)))
                     (weight (exp (-x3 * x3
                                     * recip (fromProb (2 * exp (log x4 * 2))))
                              * recip x4
                              * recip (exp (log (2 * pi_) * half)))
                             (dirac x2)))

t68' :: (ABT Term abt) => abt '[] ('HProb ':-> 'HReal ':-> 'HMeasure 'HReal)
t68' = lam $ \noise -> app (app t68 noise) noise

t69x, t69y :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
t69x = dirac (integrate one 2 $ \x -> integrate 3 4 $ \_ -> unsafeProb x)
t69y = dirac (integrate one 2 $ \_ -> integrate 3 4 $ \y -> unsafeProb y)

t70a, t71a, t72a, t73a, t74a :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t70a = uniform one 3 >>= \x -> if_ (4 < x) (superpose []) (dirac x)
t71a = uniform one 3 >>= \x -> if_ (3 < x) (superpose []) (dirac x)
t72a = uniform one 3 >>= \x -> if_ (2 < x) (superpose []) (dirac x)
t73a = uniform one 3 >>= \x -> if_ (one < x) (superpose []) (dirac x)
t74a = uniform one 3 >>= \x -> if_ (zero < x) (superpose []) (dirac x)

t70b, t71b, t72b, t73b, t74b :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t70b = uniform one 3 >>= \x -> if_ (4 < x) (dirac x) (superpose [])
t71b = uniform one 3 >>= \x -> if_ (3 < x) (dirac x) (superpose [])
t72b = uniform one 3 >>= \x -> if_ (2 < x) (dirac x) (superpose [])
t73b = uniform one 3 >>= \x -> if_ (one < x) (dirac x) (superpose [])
t74b = uniform one 3 >>= \x -> if_ (zero < x) (dirac x) (superpose [])

t70c, t71c, t72c, t73c, t74c :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t70c = uniform one 3 >>= \x -> if_ (x < 4) (dirac x) (superpose [])
t71c = uniform one 3 >>= \x -> if_ (x < 3) (dirac x) (superpose [])
t72c = uniform one 3 >>= \x -> if_ (x < 2) (dirac x) (superpose [])
t73c = uniform one 3 >>= \x -> if_ (x < one) (dirac x) (superpose [])
t74c = uniform one 3 >>= \x -> if_ (x < zero) (dirac x) (superpose [])

t70d, t71d, t72d, t73d, t74d :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t70d = uniform one 3 >>= \x -> if_ (x < 4) (superpose []) (dirac x)
t71d = uniform one 3 >>= \x -> if_ (x < 3) (superpose []) (dirac x)
t72d = uniform one 3 >>= \x -> if_ (x < 2) (superpose []) (dirac x)
t73d = uniform one 3 >>= \x -> if_ (x < one) (superpose []) (dirac x)
t74d = uniform one 3 >>= \x -> if_ (x < zero) (superpose []) (dirac x)

t75 :: (ABT Term abt) => abt '[] ('HMeasure HInt)
t75 = gamma 6 one >>= poisson

t75' :: (ABT Term abt) => abt '[] ('HProb ':-> 'HMeasure HInt)
t75' = lam $ \x -> gamma x one >>= poisson

t76 :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure 'HReal)
t76 =
    lam $ \x ->
    lebesgue >>= \y ->
    weight (unsafeProb (abs y)) $
    if_ (y < one)
        (if_ (zero < y)
            (if_ (x * y < one)
                (if_ (zero < x * y)
                    (dirac (x * y))
                    (superpose []))
                (superpose []))
            (superpose []))
        (superpose [])

-- the (x * (-1)) below is an unfortunate artifact not worth fixing
t77 :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure HUnit)
t77 =
    lam $ \x ->
    if_ (x < zero)
        (factor (exp (negate x)))
        (factor (exp x))

t78, t78' :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t78 = uniform zero 2 >>= \x2 -> weight (unsafeProb x2) (dirac x2)
t78' = liftM (fromProb . (*2)) (beta 2 one)

-- what does this simplify to?
t79 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t79 = dirac 3 >>= \x -> dirac (if_ (x == 3) one x)

t80 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t80 = gamma_1_1 >>= \t -> normal zero t

t81 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t81 = uniform zero pi

-- Testing round-tripping of some other distributions
testexponential :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
testexponential = exponential third

testCauchy :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
testCauchy = cauchy 5 3

testMCMCPriorProp
    :: (ABT Term abt)
    => abt '[] (HPair 'HReal 'HReal ':-> 'HMeasure (HPair 'HReal 'HReal))
testMCMCPriorProp = mcmc (priorAsProposal norm) norm

testMHPriorProp
    :: (ABT Term abt)
    => abt '[]
        (HPair 'HReal 'HReal
        ':-> 'HMeasure (HPair (HPair 'HReal 'HReal) 'HProb))
testMHPriorProp = mh (priorAsProposal norm) norm

testPriorProp'
    :: (ABT Term abt)
    => abt '[]
        (HPair 'HReal 'HReal
        ':-> 'HMeasure (HPair (HPair 'HReal 'HReal) 'HProb))
testPriorProp' =
    lam $ \old ->
    superpose
        [(half,
            normal_0_1 >>= \x1 ->
            dirac (pair (pair x1 (snd old))
                (exp
                    ( (x1 * negate one + (old `unpair` \x2 x3 -> x2))
                    *   ( (old `unpair` \x2 x3 -> x2)
                        + (old `unpair` \x2 x3 -> x3) * (-2)
                        + x1)
                    * half))))
        , (half,
            normal zero (sqrt 2) >>= \x1 ->
            dirac (pair (pair (fst old) x1)
                (exp
                    ( (x1 + (old `unpair` \x2 x3 -> x3) * negate one)
                    *   ( (old `unpair` \x2 x3 -> x3)
                        + (old `unpair` \x2 x3 -> x2) * (-4)
                        + x1)
                    * fromRational (-1/4)))))
        ]

dup :: (ABT Term abt)
    => abt '[] ('HMeasure a)
    -> abt '[] ('HMeasure (HPair a a))
dup m = let_ m (\m' -> liftM2 pair m' m')

norm_nox :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
norm_nox =
    normal_0_1 >>= \x ->
    normal x one >>= \y ->
    dirac y

norm_noy :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
norm_noy =
    normal_0_1 >>= \x ->
    normal x one >>
    dirac x

flipped_norm :: (ABT Term abt) => abt '[] ('HMeasure (HPair 'HReal 'HReal))
flipped_norm =
    normal_0_1 >>= \x ->
    normal x one >>= \y ->
    dirac (pair y x)

-- pull out some of the intermediate expressions for independent study
expr1 :: (ABT Term abt) => abt '[] ('HReal ':-> 'HProb)
expr1 =
    lam $ \x0 ->
        (lam $ \_ ->
        lam $ \x2 ->
        lam $ \x3 ->
          (lam $ \x4 ->
            zero
            + one
              * (lam $ \x5 ->
                 (lam $ \x6 ->
                  zero
                  + exp (-(x2 - zero) * (x2 - zero) / fromProb (2 * exp (log 5 * 2)))
                    / 5
                    / exp (log (2 * pi_) * half)
                    * (lam $ \x7 -> x7 `app` unit) `app` x6)
                 `app` (lam $ \_ ->
                        (lam $ \x7 ->
                         (lam $ \x8 -> x8 `app` x2)
                         `app` (lam $ \_ ->
                                (lam $ \x9 ->
                                 (lam $ \x10 -> x10 `app` unit)
                                 `app` (lam $ \x10 ->
                                        (lam $ \x11 ->
                                         (lam $ \x12 -> x12 `app` x2)
                                         `app` (lam $ \_ ->
                                                (lam $ \x13 -> x13 `app` pair x2 x10) `app` x11))
                                        `app` x9))
                                `app` x7))
                        `app` x5))
                `app` x4)
           `app` (lam $ \x4 ->
                  (lam $ \x5 -> x5 `app` (x4 `unpair` \_ x7 -> x7)) `app` x3)
        )
        `app` unit
        `app` x0
        `app` (lam $ \_ -> one)

expr2 :: (ABT Term abt) => abt '[] ('HReal ':-> 'HReal ':-> 'HProb)
expr2 =
    lam $ \x1 ->
    lam $ \x2 ->
        (lam $ \x3 ->
        lam $ \x4 ->
        lam $ \x5 ->
           (lam $ \x6 ->
            zero
            + one
              * (lam $ \x7 ->
                 (lam $ \x8 ->
                  zero
                  + exp (-(x4 - x3) * (x4 - x3) / fromProb (2 * exp (log one * 2)))
                    / one
                    / exp (log (2 * pi_) * half)
                    * (lam $ \x9 -> x9 `app` unit) `app` x8)
                 `app` (lam $ \_ ->
                        (lam $ \x9 ->
                         (lam $ \x10 -> x10 `app` x4)
                         `app` (lam $ \_ ->
                                (lam $ \x11 ->
                                 (lam $ \x12 -> x12 `app` unit)
                                 `app` (lam $ \x12 ->
                                        (lam $ \x13 ->
                                         (lam $ \x14 -> x14 `app` x4)
                                         `app` (lam $ \_ ->
                                                (lam $ \x15 -> x15 `app` pair x4 x12) `app` x13))
                                        `app` x11))
                                `app` x9))
                        `app` x7))
                `app` x6)
           `app` (lam $ \x6 ->
                  (lam $ \x7 -> x7 `app` (x6 `unpair` \_ x9 -> x9)) `app` x5)
        )
        `app` x1
        `app` x2
        `app` (lam $ \_ -> one)

-- the one we need in testKernel
expr3 :: (ABT Term abt)
    => abt '[] (d ':-> 'HProb)
    -> abt '[] (d ':-> d ':-> 'HProb)
    -> abt '[] d -> abt '[] d -> abt '[] 'HProb
expr3 x0 x1 x2 x3 =
    let q = x0 `app` x3
            / x1 `app` x2 `app` x3
            * x1 `app` x3 `app` x2
            / x0 `app` x2
    in if_ (one < q) one q)

-- testKernel :: Sample IO ('HReal ':-> 'HMeasure 'HReal)
testKernel :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure 'HReal)
testKernel =
-- Below is the output of testMcmc as of 2014-11-05
    let_ expr1 $ \x0 ->
    let_ expr2 $ \x1 ->
    lam $ \x2 ->
    normal x2 one >>= \x3 ->
    let_ (expr3 x0 x1 x2 x3) $ \x4 ->
    bern x4 >>= \x5 ->
    dirac (if_ x5 x3 x2)

-- this should be equivalent to the above
testKernel2 :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure 'HReal)
testKernel2 =
    lam $ \x2 ->
    normal x2 one >>= \x3 ->
    let q = exp(-1/50*(x3-x2)*(x3+x2)) in
    let_ (if_ (one < q) one q) $ \x4 ->
    bern x4 >>= \x5 ->
    dirac $ if_ x5 x3 x2

-- this comes from {Tests.Lazy,Examples.EasierRoadmap}.easierRoadmapProg1.  It is the
-- program post-disintegrate, as passed to Maple to simplify
rmProg1 :: (ABT Term abt) => abt '[]
    (HUnit
    ':-> HPair 'HReal 'HReal
    ':-> 'HMeasure (HPair 'HProb 'HProb))
rmProg1 =
    lam $ \_ ->
    lam $ \x1 ->
    x1 `unpair` \x2 x3 ->
    weight one $
    weight one $
    superpose
        [(one,
            weight one $
            lebesgue >>= \x4 ->
            superpose
                [(one,
                    weight one $
                    lebesgue >>= \x5 ->
                    weight one $
                    lebesgue >>= \x6 ->
                    weight
                        ( exp (-(x3 - x6) * (x3 - x6)
                            / (fromProb (2 * exp (log (unsafeProb x5) * 2))))
                        / unsafeProb x5
                        / (exp (log (2 * pi_) * half))) $
                    weight one $
                    lebesgue >>= \x7 ->
                    weight
                        ( exp (-(x6 - x7) * (x6 - x7)
                            / (fromProb (2 * exp (log (unsafeProb x4) * 2))))
                        / (unsafeProb x4)
                        / (exp (log (2 * pi_) * half))) $
                    weight
                        ( exp (-(x2 - x7) * (x2 - x7)
                            / (fromProb (2 * exp (log (unsafeProb x5) * 2))))
                        / unsafeProb x5
                        / (exp (log (2 * pi_) * half))) $
                    weight
                        ( exp (-x7 * x7
                            / (fromProb (2 * exp (log (unsafeProb x4) * 2))))
                        / unsafeProb x4
                        / (exp (log (2 * pi_) * half))) $
                    weight (recip (unsafeProb 3)) $
                    superpose
                        [(one,
                            if_ (x5 < 4)
                                (if_ (one < x5)
                                    (weight (recip (unsafeProb 5)) $
                                    superpose
                                        [(one,
                                            if_ (x4 < 8)
                                                (if_ (3 < x4)
                                                    (dirac (pair (unsafeProb x4)
                                                        (unsafeProb x5)))
                                                    (superpose []))
                                                (superpose []))
                                        , (one, superpose [])])
                                    (superpose []))
                                (superpose []))
                , (one, superpose [])])
            , (one, superpose [])])
        , (one, superpose [])]

-- this comes from Examples.EasierRoadmap.easierRoadmapProg4'.
rmProg4
    :: (ABT Term abt)
    => abt '[]
        (HPair 'HReal 'HReal
        ':-> HPair 'HProb 'HProb
        ':-> 'HMeasure (HPair (HPair 'HProb 'HProb) 'HProb))
rmProg4 =
    lam $ \x0 ->
    let_ (lam $ \x1 ->
        (lam $ \x2 ->
         lam $ \x3 ->
         x3 `unpair` \x4 x5 ->
         let_ one $ \x6 ->
         let_ (let_ one $ \x7 ->
               let_ (let_ one $ \x8 ->
                     let_ (let_ one $ \x9 ->
                           let_ (let_ one $ \x10 ->
                                 let_ (let_ one $ \x11 ->
                                       let_ (x2 `unpair` \x12 _ ->
                                             x2 `unpair` \x14 _ ->
                                             x2 `unpair` \x16 _ ->
                                             x2 `unpair` \_ x19 ->
                                             x2 `unpair` \_ x21 ->
                                             x2 `unpair` \_ x23 ->
                                             x2 `unpair` \x24 _ ->
                                             x2 `unpair` \x26 _ ->
                                             x2 `unpair` \_ x29 ->
                                             x2 `unpair` \_ x31 ->
                                             let_ (recip pi_
                                                   * exp ((x12 * x14 * (fromProb x4 * fromProb x4)
                                                            * 2
                                                            + fromProb x4 * fromProb x4 * x16 * x19
                                                              * (-2)
                                                            + x21 * x23 * (fromProb x4 * fromProb x4)
                                                            + fromProb x5 * fromProb x5 * (x24 * x26)
                                                            + fromProb x5 * fromProb x5 * (x29 * x31))
                                                           * recip (fromProb x4 * fromProb x4
                                                                    * (fromProb x4 * fromProb x4)
                                                                    + fromProb x5 * fromProb x5
                                                                      * (fromProb x4 * fromProb x4)
                                                                      * 3
                                                                    + fromProb x5 * fromProb x5
                                                                      * (fromProb x5 * fromProb x5))
                                                           * (negate half))
                                                   * exp (log (unsafeProb (exp (log (fromProb x4)
                                                                                  * 4)
                                                                             + exp (log (fromProb x5)
                                                                                    * 2)
                                                                               * exp (log (fromProb x4)
                                                                                      * 2)
                                                                               * 3
                                                                             + exp (log (fromProb x5)
                                                                                    * 4)))
                                                           * (negate half))
                                                   * (1/10)) $ \x32 ->
                                             let_ (let_ (recip (unsafeProb 3)) $ \x33 ->
                                                   let_ (let_ one $ \x34 ->
                                                         let_ (if_ (fromProb x5 < 4)
                                                                   (if_ (one < fromProb x5)
                                                                        (let_ (recip (unsafeProb 5)) $ \x35 ->
                                                                         let_ (let_ one $ \x36 ->
                                                                               let_ (if_ (fromProb x4
                                                                                          < 8)
                                                                                         (if_ (3
                                                                                               < fromProb x4)
                                                                                              (let_ 5 $ \x37 ->
                                                                                               let_ (let_ (pair (unsafeProb (fromProb x4))
                                                                                                                (unsafeProb (fromProb x5))) $ \x38 ->
                                                                                                     pair (dirac x38)
                                                                                                          (lam $ \x39 ->
                                                                                                           x39
                                                                                                           `app` x38)) $ \x38 ->
                                                                                               pair (weight x37 $
                                                                                                     x38 `unpair` \x39 _ ->
                                                                                                     x39)
                                                                                                    (lam $ \x39 ->
                                                                                                     zero
                                                                                                     + x37
                                                                                                       * (x38 `unpair` \_ x41 ->
                                                                                                          x41)
                                                                                                         `app` x39))
                                                                                              (pair (superpose [])
                                                                                                    (lam $ \x37 ->
                                                                                                     zero)))
                                                                                         (pair (superpose [])
                                                                                               (lam $ \x37 ->
                                                                                                zero))) $ \x37 ->
                                                                               let_ one $ \x38 ->
                                                                               let_ (pair (superpose [])
                                                                                          (lam $ \x39 ->
                                                                                           zero)) $ \x39 ->
                                                                               pair (superpose [(x36,
                                                                                                 x37 `unpair` \x40 x41 ->
                                                                                                 x40),
                                                                                                (x38,
                                                                                                 x39 `unpair` \x40 x41 ->
                                                                                                 x40)])
                                                                                    (lam $ \x40 ->
                                                                                     zero
                                                                                     + x36
                                                                                       * (x37 `unpair` \x41 x42 ->
                                                                                          x42)
                                                                                         `app` x40
                                                                                     + x38
                                                                                       * (x39 `unpair` \x41 x42 ->
                                                                                          x42)
                                                                                         `app` x40)) $ \x36 ->
                                                                         pair (weight x35 $
                                                                               x36 `unpair` \x37 x38 ->
                                                                               x37)
                                                                              (lam $ \x37 ->
                                                                               zero
                                                                               + x35
                                                                                 * (x36 `unpair` \x38 x39 ->
                                                                                    x39)
                                                                                   `app` x37))
                                                                        (pair (superpose [])
                                                                              (lam $ \x35 -> zero)))
                                                                   (pair (superpose [])
                                                                         (lam $ \x35 -> zero))) $ \x35 ->
                                                         let_ one $ \x36 ->
                                                         let_ (pair (superpose [])
                                                                    (lam $ \x37 -> zero)) $ \x37 ->
                                                         pair (superpose [(x34,
                                                                           x35 `unpair` \x38 x39 ->
                                                                           x38),
                                                                          (x36,
                                                                           x37 `unpair` \x38 x39 ->
                                                                           x38)])
                                                              (lam $ \x38 ->
                                                               zero
                                                               + x34
                                                                 * (x35 `unpair` \x39 x40 -> x40)
                                                                   `app` x38
                                                               + x36
                                                                 * (x37 `unpair` \x39 x40 -> x40)
                                                                   `app` x38)) $ \x34 ->
                                                   pair (weight x33 $ x34 `unpair` \x35 x36 -> x35)
                                                        (lam $ \x35 ->
                                                         zero
                                                         + x33
                                                           * (x34 `unpair` \x36 x37 -> x37)
                                                             `app` x35)) $ \x33 ->
                                             pair (weight x32 $ x33 `unpair` \x34 x35 -> x34)
                                                  (lam $ \x34 ->
                                                   zero
                                                   + x32
                                                     * (x33 `unpair` \x35 x36 -> x36)
                                                       `app` x34)) $ \x12 ->
                                       pair (weight x11 $ x12 `unpair` \x13 x14 -> x13)
                                            (lam $ \x13 ->
                                             zero
                                             + x11
                                               * (x12 `unpair` \x14 x15 -> x15) `app` x13)) $ \x11 ->
                                 let_ one $ \x12 ->
                                 let_ (pair (superpose []) (lam $ \x13 -> zero)) $ \x13 ->
                                 pair (superpose [(x10, x11 `unpair` \x14 x15 -> x14),
                                                  (x12, x13 `unpair` \x14 x15 -> x14)])
                                      (lam $ \x14 ->
                                       zero + x10 * (x11 `unpair` \x15 x16 -> x16) `app` x14
                                       + x12 * (x13 `unpair` \x15 x16 -> x16) `app` x14)) $ \x10 ->
                           pair (weight x9 $ x10 `unpair` \x11 x12 -> x11)
                                (lam $ \x11 ->
                                 zero + x9 * (x10 `unpair` \x12 x13 -> x13) `app` x11)) $ \x9 ->
                     let_ one $ \x10 ->
                     let_ (pair (superpose []) (lam $ \x11 -> zero)) $ \x11 ->
                     pair (superpose [(x8, x9 `unpair` \x12 x13 -> x12),
                                      (x10, x11 `unpair` \x12 x13 -> x12)])
                          (lam $ \x12 ->
                           zero + x8 * (x9 `unpair` \x13 x14 -> x14) `app` x12
                           + x10 * (x11 `unpair` \x13 x14 -> x14) `app` x12)) $ \x8 ->
               pair (weight x7 $ x8 `unpair` \x9 x10 -> x9)
                    (lam $ \x9 ->
                     zero + x7 * (x8 `unpair` \x10 x11 -> x11) `app` x9)) $ \x7 ->
         pair (weight x6 $ x7 `unpair` \x8 x9 -> x8)
              (lam $ \x8 -> zero + x6 * (x7 `unpair` \x9 x10 -> x10) `app` x8))
        `app` x0
        `app` x1 `unpair` \x2 x3 ->
        x3 `app` (lam $ \x4 -> one)) $ \x1 ->
  lam $ \x2 ->
  (x2 `unpair` \x3 x4 ->
   superpose [(half,
               uniform 3 8 >>= \x5 -> dirac (pair (unsafeProb x5) x4)),
              (half,
               uniform one 4 >>= \x5 ->
               dirac (pair x3 (unsafeProb x5)))]) >>= \x3 ->
  dirac (pair x3 (x1 `app` x3 / x1 `app` x2))


-- this comes from Examples.Seismic.falseDetection
seismicFalseDetection
    :: (ABT Term abt)
    => abt '[] (HPair 'HReal (HPair 'HReal (HPair 'HReal (HPair 'HReal (HPair 'HReal (HPair 'HProb (HPair 'HProb (HPair 'HProb (HPair 'HReal (HPair 'HReal (HPair 'HReal (HPair 'HProb (HPair 'HProb (HPair 'HReal 'HProb))))))))))))))
    -> abt '[] ('HMeasure (HPair 'HReal (HPair 'HReal (HPair 'HReal 'HProb))))
seismicFalseDetection x0 =
    x0 `unpair` \x1 x2 ->
    x2 `unpair` \x3 x4 ->
    x4 `unpair` \x5 x6 ->
    x6 `unpair` \x7 x8 ->
    x8 `unpair` \x9 x10 ->
    x10 `unpair` \x11 x12 ->
    x12 `unpair` \x13 x14 ->
    x14 `unpair` \x15 x16 ->
    x16 `unpair` \x17 x18 ->
    x18 `unpair` \x19 x20 ->
    x20 `unpair` \x21 x22 ->
    x22 `unpair` \x23 x24 ->
    x24 `unpair` \x25 x26 ->
    x26 `unpair` \x27 x28 ->
    uniform zero 3600 >>= \x29 ->
    uniform zero 360 >>= \x30 ->
    uniform (-23/500 * 180 + 107/10) (-23/500 * zero + 107/10) >>= \x31 ->
    (
        normal_0_1 >>= \x32 ->
        normal_0_1 >>= \x33 ->
        dirac (x27 + fromProb x28 * (x32 / x33))
    ) >>= \x32 ->
    dirac (pair x29 (pair x30 (pair x31 (exp x32))))


-- this comes from Examples.Seismic.trueDetection
seismicTrueDetection
    :: (ABT Term abt)
    => abt '[] (HPair 'HReal (HPair 'HReal (HPair 'HReal (HPair 'HReal (HPair 'HReal (HPair 'HProb (HPair 'HProb (HPair 'HProb (HPair 'HReal (HPair 'HReal (HPair 'HReal (HPair 'HProb (HPair 'HProb (HPair 'HReal 'HProb))))))))))))))
    -> abt '[] (HPair 'HReal (HPair 'HReal (HPair 'HProb 'HReal)))
    -> abt '[] ('HMeasure (HEither HUnit (HPair 'HReal (HPair 'HReal (HPair 'HReal 'HProb)))))
seismicTrueDetection x0 x1 =
    let deg2rad x = x * pi / 180 in -- manual CSE
    x0 `unpair` \x2 x3 ->
    x3 `unpair` \x4 x5 ->
    x5 `unpair` \x6 x7 ->
    x7 `unpair` \x8 x9 ->
    x9 `unpair` \x10 x11 ->
    x11 `unpair` \x12 x13 ->
    x13 `unpair` \x14 x15 ->
    x15 `unpair` \x16 x17 ->
    x17 `unpair` \x18 x19 ->
    x19 `unpair` \x20 x21 ->
    x21 `unpair` \x22 x23 ->
    x23 `unpair` \x24 x25 ->
    x25 `unpair` \x26 x27 ->
    x27 `unpair` \x28 x29 ->
    x1 `unpair` \x30 x31 ->
    x31 `unpair` \x32 x33 ->
    x33 `unpair` \x34 x35 ->
    superpose
        [(recip (one + exp (negate
            ( x6
            + x8 * fromProb x34
            + x10 * (deg2rad
                (atan (sqrt
                    ( (cos (deg2rad x32) * sin (deg2rad (x30 - x2))) ** 2
                    +   ( cos (deg2rad x4) * sin (deg2rad x32)
                        - sin (deg2rad x4)
                            * cos (deg2rad x32)
                            * cos (deg2rad (x30 - x2))
                        ) ** 2
                    )
                    /   ( sin (deg2rad x4)
                            * sin (deg2rad x32)
                        + cos (deg2rad x4)
                            * cos (deg2rad x32)
                            * cos (deg2rad (x30 - x2))))
                + if_
                    ( sin (deg2rad x4)
                        * sin (deg2rad x32)
                    + cos (deg2rad x4)
                        * cos (deg2rad x32)
                        * cos (deg2rad (x30 - x2))
                    < zero)
                    pi
                    zero)))))
            , dirac true)
        , (one - recip (one + exp (negate
            ( x6
            + x8 * fromProb x34
            + x10 * (deg2rad
                (atan (sqrt
                    ( (cos (deg2rad x32) * sin (deg2rad (x30 - x2))) ** 2
                    +   ( cos (deg2rad x4)
                            * sin (deg2rad x32)
                        - sin (deg2rad x4)
                            * cos (deg2rad x32)
                            * cos (deg2rad (x30 - x2))) ** 2
                    )
                    /   ( sin (deg2rad x4)
                            * sin (deg2rad x32)
                        + cos (deg2rad x4)
                            * cos (deg2rad x32)
                            * cos (deg2rad (x30 - x2))))
                + if_
                    ( sin (deg2rad x4)
                        * sin (deg2rad x32)
                    + cos (deg2rad x4)
                        * cos (deg2rad x32)
                        * cos (deg2rad (x30 - x2))
                    < zero)
                    pi
                    zero)))))
            , dirac false)
        ] >>= \x36 ->
    if_ (if_ x36 false true)
      (dirac (inl unit))
      ((gamma_1_1 >>= \x37 ->
        normal_0_1 >>= \x38 ->
        dirac (x35
               + (-23/1000
                   * ((atan (sqrt ((cos (deg2rad x32) * sin (deg2rad (x30 - x2))) ** 2
                                   + (cos (deg2rad x4) * sin (deg2rad x32) - sin (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))) ** 2)
                             / (sin (deg2rad x4) * sin (deg2rad x32) + cos (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))))
                       + if_ (sin (deg2rad x4) * sin (deg2rad x32) + cos (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))
                              < zero)
                             pi
                             zero)
                      * 180
                      / pi)
                     ** 2
                  + 107/10
                    * ((atan (sqrt ((cos (deg2rad x32) * sin (deg2rad (x30 - x2))) ** 2
                                    + (cos (deg2rad x4) * sin (deg2rad x32) - sin (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))) ** 2)
                              / (sin (deg2rad x4) * sin (deg2rad x32) + cos (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))))
                        + if_ (sin (deg2rad x4) * sin (deg2rad x32) + cos (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))
                               < zero)
                              pi
                              zero)
                       * 180
                       / pi)
                  + 5)
               + x38 * fromProb (x12 * sqrt (2 * x37)))) >>= \x37 ->
       if_ (3600 < x37)
           (dirac (inl unit))
           ((gamma_1_1 >>= \x38 -> normal_0_1 >>= \x39 -> dirac (zero + x39 * fromProb (x14 * sqrt (2 * x38)))) >>= \x38 ->
            (counting >>= \x39 ->
             if_ (if_ (if_ ((atan (sin (deg2rad (x30 - x2))
                                   / (cos (deg2rad x4) * tan (deg2rad x32) - sin (deg2rad x4) * cos (deg2rad (x30 - x2))))
                             + if_ (cos (deg2rad x4) * tan (deg2rad x32) - sin (deg2rad x4) * cos (deg2rad (x30 - x2)) < zero)
                                   (if_ (sin (deg2rad (x30 - x2)) < zero) (-pi) pi)
                                   zero)
                            * 180
                            / pi
                            + x38
                            + 360 * fromInt x39
                            < zero)
                           false
                           true)
                      ((atan (sin (deg2rad (x30 - x2))
                              / (cos (deg2rad x4) * tan (deg2rad x32) - sin (deg2rad x4) * cos (deg2rad (x30 - x2))))
                        + if_ (cos (deg2rad x4) * tan (deg2rad x32) - sin (deg2rad x4) * cos (deg2rad (x30 - x2)) < zero)
                              (if_ (sin (deg2rad (x30 - x2)) < zero) (-pi) pi)
                              zero)
                       * 180
                       / pi
                       + x38
                       + 360 * fromInt x39
                       < 360)
                      false)
                 (dirac ((atan (sin (deg2rad (x30 - x2))
                                / (cos (deg2rad x4) * tan (deg2rad x32) - sin (deg2rad x4) * cos (deg2rad (x30 - x2))))
                          + if_ (cos (deg2rad x4) * tan (deg2rad x32) - sin (deg2rad x4) * cos (deg2rad (x30 - x2)) < zero)
                                (if_ (sin (deg2rad (x30 - x2)) < zero) (-pi) pi)
                                zero)
                         * 180
                         / pi
                         + x38
                         + 360 * fromInt x39))
                 (superpose [])) >>= \x39 ->
            (gamma_1_1 >>= \x40 ->
             normal_0_1 >>= \x41 ->
             dirac (-23/500
                     * ((atan (sqrt ((cos (deg2rad x32) * sin (deg2rad (x30 - x2))) ** 2
                                     + (cos (deg2rad x4) * sin (deg2rad x32) - sin (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))) ** 2)
                               / (sin (deg2rad x4) * sin (deg2rad x32) + cos (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))))
                         + if_ (sin (deg2rad x4) * sin (deg2rad x32) + cos (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))
                                < zero)
                               pi
                               zero)
                        * 180
                        / pi)
                    + 107/10
                    + x41 * fromProb (x16 * sqrt (2 * x40)))) >>= \x40 ->
            normal (x18 + x20 * fromProb x34
                    + x22
                      * ((atan (sqrt ((cos (deg2rad x32) * sin (deg2rad (x30 - x2))) ** 2
                                      + (cos (deg2rad x4) * sin (deg2rad x32) - sin (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))) ** 2)
                                / (sin (deg2rad x4) * sin (deg2rad x32) + cos (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))))
                          + if_ (sin (deg2rad x4) * sin (deg2rad x32) + cos (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))
                                 < zero)
                                pi
                                zero)
                         * 180
                         / pi))
                   x24 >>= \x41 ->
            dirac (inr (pair x37 (pair x39 (pair x40 (exp x41)))))))


tdl :: (ABT Term abt) => abt '[]
    (   (HPair 'HReal
        (HPair 'HReal
        (HPair 'HReal
        (HPair 'HReal
        (HPair 'HReal
        (HPair 'HProb
        (HPair 'HProb
        (HPair 'HProb
        (HPair 'HReal
        (HPair 'HReal
        (HPair 'HReal
        (HPair 'HProb
        (HPair 'HProb
        (HPair 'HReal
        'HProb))))))))))))))
    ':->
        (HPair 'HReal
        (HPair 'HReal
        (HPair 'HProb
        'HReal)))
    ':-> 'HMeasure HUnit)
tdl =
    lam $ \x0 ->
    lam $ \x1 -> 
    seismicTrueDetection x0 x1 >>= \z -> 
    uneither z dirac (\_ -> superpose [])
tdr :: (ABT Term abt) => abt '[]
    (   (HPair 'HReal
        (HPair 'HReal
        (HPair 'HReal
        (HPair 'HReal
        (HPair 'HReal
        (HPair 'HProb
        (HPair 'HProb
        (HPair 'HProb
        (HPair 'HReal
        (HPair 'HReal
        (HPair 'HReal
        (HPair 'HProb
        (HPair 'HProb
        (HPair 'HReal
        'HProb))))))))))))))
    ':->
        (HPair 'HReal
        (HPair 'HReal
        (HPair 'HProb
        'HReal)))
    ':-> 'HMeasure (HPair 'HReal (HPair 'HReal (HPair 'HReal 'HProb))))
tdr =
    lam $ \x0 ->
    lam $ \x1 -> 
    seismicTrueDetection x0 x1 >>= \z -> 
    uneither z (\_ -> superpose []) dirac

-- from Examples/HMMContinuous.hs
kalman :: (ABT Term abt) => abt '[]
    (   (HPair 'HProb
        (HPair 'HProb
        (HPair 'HReal
        (HPair 'HReal
        (HPair 'HReal
        'HProb)))))
    ':->
        (HPair 'HProb
        (HPair 'HProb
        (HPair 'HReal
        (HPair 'HReal
        (HPair 'HReal
        'HProb)))))
    ':-> 'HReal
    ':-> 'HMeasure 'HReal)
kalman =
    lam $ \m ->
    lam $ \n ->
    reflect m `bindo` reflect n
    where
    reflect m0 =
        unpair m0 $ \a m1 ->
        unpair m1 $ \b m2 ->
        unpair m2 $ \c m3 ->
        unpair m3 $ \d m4 ->
        unpair m4 $ \e f ->
        lam $ \s ->
        weight (a * exp (- fromProb b * (s - c) ** 2)) $
        normal (d * s + e) f

-- from a web question
-- these are mathematically equivalent, albeit at different types
chal1 :: (ABT Term abt) => abt '[]
    ('HProb ':-> 'HReal ':-> 'HReal ':-> 'HReal ':-> 'HMeasure HBool)
chal1 =
    lam $ \sigma ->
    lam $ \a     ->
    lam $ \b     ->
    lam $ \c     ->
    normal a sigma >>= \ya ->
    normal b sigma >>= \yb ->
    normal c sigma >>= \yc ->
    dirac (yb < ya && yc < ya)

chal2 :: (ABT Term abt) => abt '[]
    ('HProb ':-> 'HReal ':-> 'HReal ':-> 'HReal ':-> 'HMeasure 'HReal)
chal2 =
    lam $ \sigma ->
    lam $ \a     ->
    lam $ \b     ->
    lam $ \c     ->
    normal a sigma >>= \ya ->
    normal b sigma >>= \yb ->
    normal c sigma >>= \yc ->
    dirac (if_ (yb < ya && yc < ya) one zero)

chal3 :: (ABT Term abt) => abt '[] ('HProb ':-> 'HMeasure 'HReal)
chal3 = lam $ \sigma -> app3 (app chal2 sigma) zero zero zero

seismic :: (ABT Term abt) => abt '[]
    (SE.HStation
    ':-> HPair 'HReal (HPair 'HReal (HPair 'HProb 'HReal))
    ':-> HPair 'HReal (HPair 'HReal (HPair 'HReal 'HProb))
    ':-> 'HMeasure 'HProb)
seismic = lam3 (\s e d -> dirac $ SE.densT s e d)

easyHMM :: (ABT Term abt) => abt '[]
    ('HMeasure (HPair (HPair 'HReal 'HReal) (HPair 'HProb 'HProb)))
easyHMM =
    gamma 3 one >>= \noiseT ->
    gamma_1_1 >>= \noiseE ->
    normal zero noiseT >>= \x1 ->
    normal x1 noiseE >>= \m1 ->
    normal x1 noiseT >>= \x2 ->
    normal x2 noiseE >>= \m2 ->
    dirac (pair (pair m1 m2) (pair noiseT noiseE))
