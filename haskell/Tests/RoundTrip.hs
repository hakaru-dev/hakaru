{-# LANGUAGE NoImplicitPrelude
           , DataKinds
           , TypeOperators
           , TypeFamilies
           , ScopedTypeVariables
           , FlexibleContexts
           #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Tests.RoundTrip where

import Prelude ((.), ($), asTypeOf)


import Language.Hakaru.Syntax.Prelude
import Language.Hakaru.Types.DataKind
--import Language.Hakaru.Types.HClasses
import Language.Hakaru.Syntax.AST (Term)
import Language.Hakaru.Syntax.ABT (ABT)
import Language.Hakaru.Expect     (total)
import Language.Hakaru.Inference  (priorAsProposal, mcmc, mh)
import Language.Hakaru.Types.Sing

-- import qualified Examples.Seismic as SE

import Test.HUnit
import Tests.TestTools
import Tests.Models
    (uniform_0_1, normal_0_1, gamma_1_1,
     uniformC, normalC, beta_1_1, t4, t4', norm, unif2)

testMeasureUnit :: Test
testMeasureUnit = test [
    "t1,t5"   ~: testSStriv [t1,t5] (weight half),
    "t10"     ~: testSStriv [t10] (superpose []),
    "t11,t22" ~: testSStriv [t11,t22] (dirac unit),
    "t12"     ~: testSStriv [] t12,
    "t20"     ~: testSStriv [t20] (lam $ \y -> weight (y * half)),
    "t24"     ~: testSStriv [t24] t24',
    "t25"     ~: testSStriv [t25] t25',
    "t44Add"  ~: testSStriv [t44Add] t44Add',
    "t44Mul"  ~: testSStriv [t44Mul] t44Mul',
    "t53"     ~: testSStriv [t53,t53'] t53'',
    "t54"     ~: testStriv t54,
    "t55"     ~: testSStriv [t55] t55',
    "t56"     ~: testSStriv [t56,t56'] t56'',
    "t57"     ~: testSStriv [t57] t57',
    "t58"     ~: testSStriv [t58] t58',
    "t59"     ~: testStriv t59,
    "t60"     ~: testSStriv [t60,t60'] t60'',
    "t62"     ~: testSStriv [t62] t62',
    "t63"     ~: testSStriv [t63] t63',
    "t64"     ~: testSStriv [t64,t64'] t64'',
    "t65"     ~: testSStriv [t65] t65',
    "t77"     ~: testSStriv [] t77
    ]

testMeasureProb :: Test
testMeasureProb = test [
    "t2"  ~: testSStriv [t2] (unsafeProb <$> uniformC zero one),
    "t26" ~: testSStriv [t26] (dirac half),
    "t30" ~: testSStriv [] t30,
    "t33" ~: testSStriv [] t33,
    "t34" ~: testSStriv [t34] (dirac (nat2prob (nat_ 3))),
    "t35" ~: testSStriv [t35] (lam $ \x -> if_ (x < (fromRational 4)) (dirac (fromRational 3)) (dirac (fromRational 5))),
    "t38" ~: testSStriv [] t38,
    "t42" ~: testSStriv [t42] (dirac (nat2prob one)),
    "t49" ~: testSStriv [] t49,
    "t61" ~: testSStriv [t61] t61',
    "t66" ~: testSStriv [] t66,
    "t67" ~: testSStriv [] t67,
    "t69x" ~: testSStriv [t69x] (dirac $ (prob_ 3)/(prob_ 2)),
    "t69y" ~: testSStriv [t69y] (dirac $ (prob_ 7)/(prob_ 2))
    ]

testMeasureReal :: Test
testMeasureReal = test
    [ "t3"  ~: testSStriv [] t3
    , "t6"  ~: testSStriv [t6'] t6
    , "t7"  ~: testSStriv [t7] t7'
    , "t7n" ~: testSStriv [t7n] t7n'
    , "t8'" ~: testSStriv [t8'] (lam $ \s1 -> lam $ \s2 -> normal zero (sqrt (s1 ^ (nat_ 2) + s2 ^ (nat_ 2))))
    , "t9"  ~: testSStriv [t9] (superpose [((nat2prob . nat_ $ 2), uniformC (nat_ 3) (nat_ 7))])
    , "t13" ~: testSStriv [t13] t13'
    , "t14" ~: testSStriv [t14] t14'
    , "t21" ~: testStriv t21
    , "t28" ~: testSStriv [] t28
    , "t31" ~: testSStriv [] t31
    , "t36" ~: testSStriv [t36] t36'
    , "t37" ~: testSStriv [] t37
    , "t39" ~: testSStriv [t39] t39'
    , "t40" ~: testSStriv [] t40
    , "t43" ~: testSStriv [t43, t43'] t43''
    , "t45" ~: testSStriv [t46,t47] t45
    , "t50" ~: testStriv t50
    , "t51" ~: testStriv t51
    , "t68" ~: testStriv t68
    , "t68'" ~: testStriv t68'
    , "t70a" ~: testSStriv [t70a] (uniformC one (nat_ 3))
    , "t71a" ~: testSStriv [t71a] (uniformC one (nat_ 3))
    , "t72a" ~: testSStriv [t72a] (withWeight half $ uniformC one (nat_ 2))
    , "t73a" ~: testSStriv [t73a] (superpose [])
    , "t74a" ~: testSStriv [t74a] (superpose [])
    , "t70b" ~: testSStriv [t70b] (superpose [])
    , "t71b" ~: testSStriv [t71b] (superpose [])
    , "t72b" ~: testSStriv [t72b] (withWeight half $ uniformC (nat_ 2) (nat_ 3))
    , "t73b" ~: testSStriv [t73b] (uniformC one (nat_ 3))
    , "t74b" ~: testSStriv [t74b] (uniformC one (nat_ 3))
    , "t70c" ~: testSStriv [t70c] (uniformC one (nat_ 3))
    , "t71c" ~: testSStriv [t71c] (uniformC one (nat_ 3))
    , "t72c" ~: testSStriv [t72c] (withWeight half $ uniformC one (nat_ 2))
    , "t73c" ~: testSStriv [t73c] (superpose [])
    , "t74c" ~: testSStriv [t74c] (superpose [])
    , "t70d" ~: testSStriv [t70d] (superpose [])
    , "t71d" ~: testSStriv [t71d] (superpose [])
    , "t72d" ~: testSStriv [t72d] (withWeight half $ uniformC (nat_ 2) (nat_ 3))
    , "t73d" ~: testSStriv [t73d] (uniformC one (nat_ 3))
    , "t74d" ~: testSStriv [t74d] (uniformC one (nat_ 3))
    , "t76" ~: testStriv t76
    , "t78" ~: testSStriv [t78] t78'
    , "t79" ~: testSStriv [t79] (dirac (nat2real one))
    , "t80" ~: testStriv t80
    , "t81" ~: testSStriv [] t81
    -- TODO, "kalman" ~: testStriv kalman
    --, "seismic" ~: testSStriv [] seismic
    , "lebesgue1" ~: testSStriv [] (lebesgue >>= \x -> if_ ((real_ 42) < x) (dirac x) (superpose []))
    , "lebesgue2" ~: testSStriv [] (lebesgue >>= \x -> if_ (x < (real_ 42)) (dirac x) (superpose []))
    , "lebesgue3" ~: testSStriv [lebesgue >>= \x -> if_ (x < (real_ 42) && (real_ 40) < x) (dirac x) (superpose [])] (withWeight (prob_ 2) $ uniform (real_ 40) (real_ 42))
    , "testexponential" ~: testStriv testexponential
    , "testcauchy" ~: testStriv testCauchy
    , "exceptionLebesgue" ~: testSStriv [lebesgue >>= \x -> dirac (if_ (x == (real_ 3)) one x)] lebesgue
    , "exceptionUniform"  ~: testSStriv [uniform (real_ 2) (real_ 4) >>= \x -> dirac (if_ (x == (real_ 3)) one x)] (uniform (nat2real . nat_ $ 2) (nat2real . nat_ $ 4))
    -- TODO "two_coins" ~: testStriv two_coins -- needs support for lists
    ]

testMeasureInt :: Test
testMeasureInt = test
    [ "t75"  ~: testStriv t75
    , "t75'" ~: testStriv t75'
    , "exceptionCounting" ~: testSStriv [] (counting >>= \x -> dirac (if_ (x == (int_ 3)) one x)) -- Jacques wrote: "bug: [simp_pw_equal] implicitly assumes the ambient measure is Lebesgue"
    , "exceptionSuperpose" ~: testSStriv [(superpose [(third, dirac (int_ 2)), (third, dirac (int_ 3)), (third, dirac (int_ 4))] `asTypeOf` counting) >>= \x -> dirac (if_ (x == (int_ 3)) one x)] (superpose [(third, dirac one), (third, dirac (int_ 2)), (third, dirac (int_ 4))])
    ]

testMeasurePair :: Test
testMeasurePair = test [
    "t4"            ~: testSStriv [t4] t4',
    "t8"            ~: testSStriv [] t8,
    "t23"           ~: testSStriv [t23] t23',
    "t48"           ~: testStriv t48,
    "t52"           ~: testSStriv [t52] t52',
    "dup"           ~: testSStriv [dup normal_0_1] (liftM2 pair
                                                           (normalC zero one)
                                                           (normalC zero one)),
    "norm"          ~: testSStriv [] norm,
    "norm_nox"      ~: testSStriv [norm_nox] (normal (nat2real zero)
                                                     (nat2prob (nat_ 2) ** real_ 0.5)),
    "norm_noy"      ~: testSStriv [norm_noy] (normalC zero one),
    "flipped_norm"  ~: testSStriv [swap <$> norm] flipped_norm,
    "priorProp"     ~: testSStriv [lam (priorAsProposal norm)]
                              (lam $ \x -> superpose [(half, normal_0_1         >>= \y -> dirac (pair y (snd x))),
                                                      (half, normal zero (sqrt (prob_ 2)) >>= \y -> dirac (pair (fst x) y))]),
    "mhPriorProp"   ~: testSStriv [testMHPriorProp] testPriorProp',
    "unif2"         ~: testStriv unif2,
    "easyHMM"       ~: testStriv easyHMM,
    "testMCMCPriorProp" ~: testStriv testMCMCPriorProp
    ]

testOther :: Test
testOther = test [
    "testRoadmapProg1" ~: testStriv rmProg1,
    "testRoadmapProg4" ~: testStriv rmProg4,
    "testKernel" ~: testSStriv [testKernel] testKernel2,
    "testFalseDetection" ~: testStriv (lam seismicFalseDetection)
    --this doesn't typecheck because Either isn't Simplifiable yet:
    -- TODO "testTrueDetection" ~: testStriv (lam2 seismicTrueDetection)
    --"testTrueDetectionL" ~: testStriv tdl,
    --"testTrueDetectionR" ~: testStriv tdr
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
-- In Maple, should 'evaluate' to "\c -> 1/2*c(Unit)"
t1 :: (ABT Term abt) => abt '[] ('HMeasure HUnit)
t1 = uniform_0_1 >>= \x -> weight (unsafeProb x)

t2 :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
t2 = beta_1_1

t3 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t3 = normal (nat2real zero) (nat2prob . nat_ $ 10)

-- t5 is "the same" as t1.
t5 :: (ABT Term abt) => abt '[] ('HMeasure HUnit)
t5 = weight half >> dirac unit

t6, t6' :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t6 = dirac (nat2real (nat_ 5))
t6' = superpose [(one, dirac (real_ 5))]

t7,t7', t7n,t7n' :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t7   = uniform_0_1 >>= \x -> weight (unsafeProb (x+one)) >> dirac (x*x)
t7'  = uniform_0_1 >>= \x -> superpose [(unsafeProb (x+one), dirac (x*x))]
t7n  =
    uniform (negate one) zero >>= \x ->
    weight (unsafeProb (x+one)) >>
    dirac (x*x)
t7n' =
    uniform (negate one) zero >>= \x ->
    superpose [(unsafeProb (x + one), dirac (x*x))]

-- For sampling efficiency (to keep importance weights at or close to 1),
-- t8 below should read back to uses of "normal", not uses of "lebesgue"
-- then "weight".
t8 :: (ABT Term abt) => abt '[] ('HMeasure (HPair 'HReal 'HReal))
t8 = normal zero (prob_ 10) >>= \x -> normal x (prob_ 20) >>= \y -> dirac (pair x y)

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
    weight (if_ ((real_ 3) < x && x < (real_ 7)) half zero) >> 
    dirac x

t10 :: (ABT Term abt) => abt '[] ('HMeasure HUnit)
t10 = weight zero

t11 :: (ABT Term abt) => abt '[] ('HMeasure HUnit)
t11 = weight one

t12 :: (ABT Term abt) => abt '[] ('HMeasure HUnit)
t12 = weight (nat2prob . nat_ $ 2)

t13,t13' :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t13 = bern ((prob_ 3)/(prob_ 5)) >>= \b -> dirac (if_ b (real_ 37) (real_ 42))
t13' = superpose
    [ ((prob_ 3)/(prob_ 5), dirac (real_ 37))
    , ((prob_ 2)/(prob_ 5), dirac (real_ 42))
    ]

t14,t14' :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t14 =
    bern ((prob_ 3)/(prob_ 5)) >>= \b ->
    if_ b t13 (bern ((prob_ 2)/(prob_ 7)) >>= \b' ->
        if_ b' (uniform (real_ 10) (real_ 12)) (uniform (real_ 14) (real_ 16)))
t14' = superpose 
    [ ((prob_ 9)/(prob_ 25), dirac (real_ 37))
    , ((prob_ 6)/(prob_ 25), dirac (real_ 42))
    , ((prob_ 4)/(prob_ 35), uniform (real_ 10) (real_ 12))
    , ((prob_ 2)/(prob_ 7) , uniform (real_ 14) (real_ 16))
    ]

t20 :: (ABT Term abt) => abt '[] ('HProb ':-> 'HMeasure HUnit)
t20 = lam $ \y -> uniform_0_1 >>= \x -> weight (unsafeProb x * y)

t21 :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure 'HReal)
t21 = mcmc (`normal` one) (normal zero (prob_ 5))

t22 :: (ABT Term abt) => abt '[] ('HMeasure HUnit)
t22 = bern half >> dirac unit

-- was called bayesNet in Nov.06 msg by Ken for exact inference
t23, t23' :: (ABT Term abt) => abt '[] ('HMeasure (HPair HBool HBool))
t23 =
    bern half >>= \a ->
    bern (if_ a ((prob_ 9)/(prob_ 10)) ((prob_ 1)/(prob_ 10))) >>= \b ->
    bern (if_ a ((prob_ 9)/(prob_ 10)) ((prob_ 1)/(prob_ 10))) >>= \c ->
    dirac (pair b c)
t23' = superpose
    [ ((prob_ 41)/(prob_ 100), dirac (pair true true))
    , ((prob_ 9)/(prob_ 100), dirac (pair true false))
    , ((prob_ 9)/(prob_ 100), dirac (pair false true))
    , ((prob_ 41)/(prob_ 100), dirac (pair false false))
    ]

t24,t24' :: (ABT Term abt) => abt '[] ('HProb ':-> 'HMeasure HUnit)
t24 =
   lam $ \x ->
   uniform_0_1 >>= \y ->
   uniform_0_1 >>= \z ->
   weight (x * exp (cos y) * unsafeProb z)
t24' =
   lam $ \x ->
   uniform_0_1 >>= \y ->
   weight (x * exp (cos y) * half)

t25,t25' :: (ABT Term abt)
   => abt '[] ('HProb ':-> 'HReal ':-> 'HMeasure HUnit)
t25 =
   lam $ \x ->
   lam $ \y ->
   uniform_0_1 >>= \z ->
   weight (x * exp (cos y) * unsafeProb z)
t25' =
   lam $ \x ->
   lam $ \y ->
   weight (x * exp (cos y) * half)

t26 :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
t26 = dirac (total t1)

t28 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t28 = uniformC zero one

t30 :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
t30 = exp <$> uniformC zero one

t31 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t31 = uniform (fromInt . int_ $ -1) (nat2real one)

t33 :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
t33 = exp <$> t31

t34 :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
t34 = dirac (if_ ((real_ 2) < (real_ 4)) (prob_ 3) (prob_ 5))

t35 :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure 'HProb)
t35 = lam $ \x -> dirac (if_ ((x `asTypeOf` log one) < (real_ 4)) (prob_ 3) (prob_ 5))

t36, t36' :: (ABT Term abt) => abt '[] ('HProb ':-> 'HMeasure 'HProb)
t36 = lam (dirac . sqrt)
t36' = lam $ \x -> if_ (x < zero) (dirac (prob_ (-337))) (dirac (sqrt x))

t37 :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure 'HReal)
t37 = lam (dirac . recip)

t38 :: (ABT Term abt) => abt '[] ('HProb ':-> 'HMeasure 'HProb)
t38 = lam (dirac . recip)

t39, t39' :: (ABT Term abt) => abt '[] ('HProb ':-> 'HMeasure 'HReal)
t39 = lam (dirac . log)
t39' = lam $ \x -> if_ (x < zero) (dirac (real_ (-337))) (dirac (log x))

t40 :: (ABT Term abt) => abt '[] ('HProb ':-> 'HMeasure 'HReal)
t40 = lam (dirac . log)

t42 :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
t42 = dirac . total $ (unsafeProb <$> uniform zero (real_ 2))

t43, t43', t43'' :: (ABT Term abt) => abt '[] (HBool ':-> 'HMeasure 'HReal)
t43   = lam $ \b -> if_ b uniform_0_1 (fromProb <$> beta_1_1)
t43'  = lam $ \b -> if_ b uniform_0_1 uniform_0_1
t43'' = lam $ \_ -> uniform_0_1

t44Add, t44Add', t44Mul, t44Mul'
    :: (ABT Term abt) => abt '[] ('HReal ':-> 'HReal ':-> 'HMeasure HUnit)
t44Add  = lam $ \x -> lam $ \y -> weight (unsafeProb $ (x * x) + (y * y))
t44Add' = lam $ \x -> lam $ \y -> weight (unsafeProb $ (x ^ (nat_ 2) + y ^ (nat_ 2)))
t44Mul  = lam $ \x -> lam $ \y -> weight (unsafeProb $ (x * x * y * y))
t44Mul' = lam $ \x -> lam $ \y -> weight (unsafeProb $ (x ^ (nat_ 2)) * (y ^ (nat_ 2)))

-- t45, t46, t47 are all equivalent.
-- But t47 is worse than t45 and t46 because the importance weight generated by
-- t47 as a sampler varies between 0 and 1 whereas the importance weight generated
-- by t45 and t46 is always 1.  In general it's good to reduce weight variance.
t45 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t45 = normal (real_ 4) (prob_ 5) >>= \x -> if_ (x < (real_ 3)) (dirac (x*x)) (dirac (x-one))

t46 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t46 = normal (real_ 4) (prob_ 5) >>= \x -> dirac (if_ (x < (real_ 3)) (x*x) (x-one))

t47 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t47 = superpose
    [ (one, normal (real_ 4) (prob_ 5) >>= \x -> if_ (x < (real_ 3)) (dirac (x*x)) (superpose []))
    , (one, normal (real_ 4) (prob_ 5) >>= \x -> if_ (x < (real_ 3)) (superpose []) (dirac (x-one)))
    ]

t48 :: (ABT Term abt) => abt '[] (HPair 'HReal 'HReal ':-> 'HMeasure 'HReal)
t48 = lam $ \x -> uniform (real_ (-5)) (real_ 7) >>= \w -> dirac ((fst x + snd x) * w)

t49 :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
t49 = gamma (prob_ 0.01)  (prob_ 0.35)

t50 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t50 = uniform one (real_ 3) >>= \x -> normal one (unsafeProb x)

t51 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t51 = t31 >>= \x -> normal x one

-- Example 1 from Chang & Pollard's Conditioning as Disintegration
t52, t52' :: (ABT Term abt) => abt '[] ('HMeasure (HPair 'HReal (HPair 'HReal 'HReal)))
t52 =
    uniform_0_1 >>= \x ->
    uniform_0_1 >>= \y ->
    dirac (pair (max x y) (pair x y))
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
        weight (unsafeProb x2)
    ) >>
    (log <$> dirac (unsafeProb x1)) >>= \x3 ->
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
    weight (unsafeProb x5)

t55, t55' :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure HUnit)
t55 =
    lam $ \t ->
    uniform_0_1 >>= \x ->
    if_ (x < t) (dirac unit) (superpose [])
t55' =
    lam $ \t ->
    if_ (t < zero) (superpose []) $
    if_ (t < one) (weight (unsafeProb t)) $
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
    withWeight (unsafeProb x2) (dirac unit)
t56' =
    lam $ \x0 ->
    uniform_0_1 >>= \x1 ->
    if_ (x0 - one < x1 && x1 < x0)
        (dirac unit)
        (superpose [])
t56'' =
    lam $ \t ->
    if_ (t <= zero) (superpose []) $
    if_ (t <= one) (weight (unsafeProb t)) $
    if_ (t <= (real_ 2)) (weight (unsafeProb ((real_ 2) + t * negate one))) $
    superpose []

t57, t57' :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure HUnit)
t57 = lam $ \t -> superpose
    [ (one, if_ (t < one)  (dirac unit) (superpose []))
    , (one, if_ (zero < t) (dirac unit) (superpose [])) ]
t57' = lam $ \t -> 
    if_ (t < one && zero < t) (weight (prob_ 2)) (dirac unit)

t58, t58' :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure HUnit)
t58 = lam $ \t -> superpose
    [ (one, if_ (zero < t && t < (real_ 2)) (dirac unit) (superpose []))
    , (one, if_ (one  < t && t < (real_ 3)) (dirac unit) (superpose [])) ]
t58' = lam $ \t ->
    if_ (if_ (zero < t) (t < (real_ 2)) false)
        (if_ (if_ (one < t) (t < (real_ 3)) false)
            (weight (prob_ 2))
            (dirac unit))
        (if_ (if_ (one < t) (t < (real_ 3)) false)
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
      weight (unsafeProb x2) ) >>
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
    weight (unsafeProb x3) 

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
      weight (unsafeProb x2) ) >>
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
    weight (unsafeProb x2)
t60' =
    lam $ \x0 ->
    uniform_0_1 >>= \x1 ->
    uniform_0_1 >>= \x2 ->
    if_ (if_ (zero < x0 / (x2 + x1))
             (x0 / (x2 + x1) < one)
             false)
        (weight ((unsafeProb (x2 + x1)) ^^ negate one) )
        (superpose [])
t60'' =
    lam $ \x0 ->
    uniform_0_1 >>= \x1 ->
    uniform_0_1 >>= \x2 ->
    if_ (if_ (zero < x0 / (x2 + x1))
             (x0 / (x2 + x1) < one)
             false)
        (weight (recip (unsafeProb (x2 + x1))) )
        (superpose [])

t61, t61' :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure 'HProb)
t61 = lam $ \x -> if_ (x < zero) (dirac zero) $ dirac $ unsafeProb $ recip x
t61'= lam $ \x -> if_ (x < zero) (dirac zero) $ dirac $ recip $ unsafeProb x

---- "Special case" of t56
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
      if_ (t/x <= one) (weight (unsafeProb (t/x))) $
      if_ (t/x <= (real_ 2)) (weight (unsafeProb ((real_ 2)-t/x))) $
      superpose []

---- "Scalar multiple" of t62
t63, t63' :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure HUnit)
t63 = lam $ \t ->
      uniform_0_1 >>= \x ->
      uniform_0_1 >>= \y ->
      if_ (zero < t/x - y && t/x - y < one)
          (weight (recip (unsafeProb x)))
          (superpose [])
t63'= lam $ \t ->
      uniform_0_1 >>= \x ->
      if_ (t/x <= zero) (superpose []) $
      if_ (t/x <= one) (weight (unsafeProb (t/x) / unsafeProb x)) $
      if_ (t/x <= (real_ 2)) (weight (unsafeProb ((real_ 2)-t/x) / unsafeProb x)) $
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
       weight (unsafeProb x1)) >>
      (log <$> dirac (unsafeProb x0)) >>= \x2 ->
      ((exp <$> dirac x2) >>= \x3 ->
       weight x3) >>
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
      weight (unsafeProb x5) 
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
      weight (unsafeProb x1) 
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
        withWeight (recip t_x) $
        (if_ (zero < negate (log t_x) && negate (log t_x) < one)
            (dirac unit)
            (superpose [])))
        (superpose [])
t65' = lam $ \t ->
       if_ (t < (fromProb (exp (negate (real_ 1))))) (superpose [])
     $ if_ (t < one) (weight (unsafeProb (log (unsafeProb t) + one)))
     $ if_ (t < one + (fromProb (exp (negate (real_ 1))))) (dirac unit)
     $ if_ (t < (fromRational 2)) (weight (unsafeProb (negate (log (unsafeProb (t - one))))))
     $ superpose []

t66 :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
t66 = dirac (sqrt ((prob_ 3) + sqrt (prob_ 3)))

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
    withWeight (exp (negate (x2 - x3) * (x2 - x3)
                     * recip (fromProb ((fromRational 2) * exp (log x4 * (fromRational 2)))))
              * recip x4
              * recip (exp (log ((fromRational 2) * pi) * half)))
             (withWeight (exp (negate (x1 - x3) * (x1 - x3)
                             * recip (fromProb ((fromRational 2) * exp (log x5 * (fromRational 2)))))
                      * recip x5
                      * recip (exp (log ((fromRational 2) * pi) * half)))
                     (withWeight (exp (negate x3 * x3
                                     * recip (fromProb ((fromRational 2) * exp (log x4 * (fromRational 2)))))
                              * recip x4
                              * recip (exp (log ((fromRational 2) * pi) * half)))
                             (dirac x2)))

t68' :: (ABT Term abt) => abt '[] ('HProb ':-> 'HReal ':-> 'HMeasure 'HReal)
t68' = lam $ \noise -> app (app t68 noise) noise

t69x, t69y :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
t69x = dirac (integrate one (real_ 2) $ \x -> integrate (real_ 3) (real_ 4) $ \_ -> unsafeProb x)
t69y = dirac (integrate one (real_ 2) $ \_ -> integrate (real_ 3) (real_ 4) $ \y -> unsafeProb y)

t70a, t71a, t72a, t73a, t74a :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t70a = uniform one (real_ 3) >>= \x -> if_ ((real_ 4) < x) (superpose []) (dirac x)
t71a = uniform one (real_ 3) >>= \x -> if_ ((real_ 3) < x) (superpose []) (dirac x)
t72a = uniform one (real_ 3) >>= \x -> if_ ((real_ 2) < x) (superpose []) (dirac x)
t73a = uniform one (real_ 3) >>= \x -> if_ (one < x) (superpose []) (dirac x)
t74a = uniform one (real_ 3) >>= \x -> if_ (zero < x) (superpose []) (dirac x)

t70b, t71b, t72b, t73b, t74b :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t70b = uniform one (real_ 3) >>= \x -> if_ ((real_ 4) < x) (dirac x) (superpose [])
t71b = uniform one (real_ 3) >>= \x -> if_ ((real_ 3) < x) (dirac x) (superpose [])
t72b = uniform one (real_ 3) >>= \x -> if_ ((real_ 2) < x) (dirac x) (superpose [])
t73b = uniform one (real_ 3) >>= \x -> if_ (one < x) (dirac x) (superpose [])
t74b = uniform one (real_ 3) >>= \x -> if_ (zero < x) (dirac x) (superpose [])

t70c, t71c, t72c, t73c, t74c :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t70c = uniform one (real_ 3) >>= \x -> if_ (x < (real_ 4)) (dirac x) (superpose [])
t71c = uniform one (real_ 3) >>= \x -> if_ (x < (real_ 3)) (dirac x) (superpose [])
t72c = uniform one (real_ 3) >>= \x -> if_ (x < (real_ 2)) (dirac x) (superpose [])
t73c = uniform one (real_ 3) >>= \x -> if_ (x < one) (dirac x) (superpose [])
t74c = uniform one (real_ 3) >>= \x -> if_ (x < zero) (dirac x) (superpose [])

t70d, t71d, t72d, t73d, t74d :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t70d = uniform one (real_ 3) >>= \x -> if_ (x < (real_ 4)) (superpose []) (dirac x)
t71d = uniform one (real_ 3) >>= \x -> if_ (x < (real_ 3)) (superpose []) (dirac x)
t72d = uniform one (real_ 3) >>= \x -> if_ (x < (real_ 2)) (superpose []) (dirac x)
t73d = uniform one (real_ 3) >>= \x -> if_ (x < one) (superpose []) (dirac x)
t74d = uniform one (real_ 3) >>= \x -> if_ (x < zero) (superpose []) (dirac x)

t75 :: (ABT Term abt) => abt '[] ('HMeasure 'HNat)
t75 = gamma (prob_ 6) one >>= poisson

t75' :: (ABT Term abt) => abt '[] ('HProb ':-> 'HMeasure 'HNat)
t75' = lam $ \x -> gamma x one >>= poisson

t76 :: (ABT Term abt) => abt '[] ('HReal ':-> 'HMeasure 'HReal)
t76 =
    lam $ \x ->
    lebesgue >>= \y ->
    withWeight (unsafeProb (abs y)) $
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
        (weight (exp (negate x)))
        (weight (exp x))

t78, t78' :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t78 = uniform zero (real_ 2) >>= \x2 -> withWeight (unsafeProb x2) (dirac x2)
t78' = (fromProb . (*(prob_ 2))) <$> (beta (prob_ 2) one)

-- what does this simplify to?
t79 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t79 = dirac (real_ 3) >>= \x -> dirac (if_ (x == (real_ 3)) one x)

t80 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t80 = gamma_1_1 >>= \t -> normal zero t

t81 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t81 = uniform (nat2real zero) pi

-- Testing round-tripping of some other distributions
testexponential :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
testexponential = exponential third

testCauchy :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
testCauchy = cauchy (real_ 5) (prob_ 3)

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
                        + (old `unpair` \x2 x3 -> x3) * (negate (real_ 2))
                        + x1)
                    * half))))
        , (half,
            normal zero (sqrt (prob_ 2)) >>= \x1 ->
            dirac (pair (pair (fst old) x1)
                (exp
                    ( (x1 + (old `unpair` \x2 x3 -> x3) * negate one)
                    *   ( (old `unpair` \x2 x3 -> x3)
                        + (old `unpair` \x2 x3 -> x2) * (negate (real_ 4))
                        + x1)
                    * (negate (real_ 1))/(real_ 4)))))
        ]

dup :: (ABT Term abt, SingI a)
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
                  + exp (negate (x2 - zero) * (x2 - zero) / fromProb ((fromRational 2) * exp (log (fromRational 5) * (fromRational 2))))
                    / (fromRational 5)
                    / exp (log ((fromRational 2) * pi) * half)
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
                  + exp (((negate x4) - x3) * (x4 - x3) / fromProb ((fromRational 2) * exp (log one * (fromRational 2))))
                    / one
                    / exp (log ((fromRational 2) * pi) * half)
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
    in if_ (one < q) one q

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
    let q = exp(negate (real_ 1)/(real_ 50)*(x3-x2)*(x3+x2)) in
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
    withWeight one $
    withWeight one $
    superpose
        [(one,
            withWeight one $
            lebesgue >>= \x4 ->
            superpose
                [(one,
                    withWeight one $
                    lebesgue >>= \x5 ->
                    withWeight one $
                    lebesgue >>= \x6 ->
                    withWeight
                        ( exp (negate (x3 - x6) * (x3 - x6)
                            / (fromProb ((fromRational 2) * exp (log (unsafeProb x5) * (fromRational 2)))))
                        / unsafeProb x5
                        / (exp (log ((fromRational 2) * pi) * half))) $
                    withWeight one $
                    lebesgue >>= \x7 ->
                    withWeight
                        ( exp (negate (x6 - x7) * (x6 - x7)
                            / (fromProb ((fromRational 2) * exp (log (unsafeProb x4) * (fromRational 2)))))
                        / (unsafeProb x4)
                        / (exp (log ((fromRational 2) * pi) * half))) $
                    withWeight
                        ( exp (negate (x2 - x7) * (x2 - x7)
                            / (fromProb ((fromRational 2) * exp (log (unsafeProb x5) * (fromRational 2)))))
                        / unsafeProb x5
                        / (exp (log ((fromRational 2) * pi) * half))) $
                    withWeight
                        ( exp (negate x7 * x7
                            / (fromProb ((fromRational 2) * exp (log (unsafeProb x4) * (fromRational 2)))))
                        / unsafeProb x4
                        / (exp (log ((fromRational 2) * pi) * half))) $
                    withWeight (recip (fromRational 3)) $
                    superpose
                        [(one,
                            if_ (x5 < (real_ 4))
                                (if_ (one < x5)
                                    (withWeight (recip (prob_ 5)) $
                                    superpose
                                        [(one,
                                            if_ (x4 < (real_ 8))
                                                (if_ ((real_ 3) < x4)
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
                                             let_ (recip pi
                                                   * exp ((x12 * x14 * (fromProb x4 * fromProb x4)
                                                            * (fromRational 2)
                                                            + fromProb x4 * fromProb x4 * x16 * x19
                                                              * (negate (fromRational 2))
                                                            + x21 * x23 * (fromProb x4 * fromProb x4)
                                                            + fromProb x5 * fromProb x5 * (x24 * x26)
                                                            + fromProb x5 * fromProb x5 * (x29 * x31))
                                                           * recip (fromProb x4 * fromProb x4
                                                                    * (fromProb x4 * fromProb x4)
                                                                    + fromProb x5 * fromProb x5
                                                                      * (fromProb x4 * fromProb x4)
                                                                      * (fromRational 3)
                                                                    + fromProb x5 * fromProb x5
                                                                      * (fromProb x5 * fromProb x5))
                                                           * (negate half))
                                                   * exp (log (exp (log x4 * (fromRational 4))
                                                                             + exp (log x5 * (fromRational 2))
                                                                               * exp (log x4 * (fromRational 2))
                                                                               * (fromRational 3)
                                                                             + exp (log x5 * (fromRational 4)))
                                                           * (negate half))
                                                   * (fromRational 1)/(fromRational 10)) $ \x32 ->
                                             let_ (let_ (recip (fromRational 3)) $ \x33 ->
                                                   let_ (let_ one $ \x34 ->
                                                         let_ (if_ (fromProb x5 < (fromRational 4))
                                                                   (if_ (one < fromProb x5)
                                                                        (let_ (recip (fromRational 5)) $ \x35 ->
                                                                         let_ (let_ one $ \x36 ->
                                                                               let_ (if_ (fromProb x4
                                                                                          < (fromRational 8))
                                                                                         (if_ ((fromRational 3)
                                                                                               < fromProb x4)
                                                                                              (let_ (fromRational 5) $ \x37 ->
                                                                                               let_ (let_ (pair x4 x5) $ \x38 ->
                                                                                                     pair (dirac x38)
                                                                                                          (lam $ \x39 ->
                                                                                                           x39
                                                                                                           `app` x38)) $ \x38 ->
                                                                                               pair (withWeight x37 $
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
                                                                         pair (withWeight x35 $
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
                                                   pair (withWeight x33 $ x34 `unpair` \x35 x36 -> x35)
                                                        (lam $ \x35 ->
                                                         zero
                                                         + x33
                                                           * (x34 `unpair` \x36 x37 -> x37)
                                                             `app` x35)) $ \x33 ->
                                             pair (withWeight x32 $ x33 `unpair` \x34 x35 -> x34)
                                                  (lam $ \x34 ->
                                                   zero
                                                   + x32
                                                     * (x33 `unpair` \x35 x36 -> x36)
                                                       `app` x34)) $ \x12 ->
                                       pair (withWeight x11 $ x12 `unpair` \x13 x14 -> x13)
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
                           pair (withWeight x9 $ x10 `unpair` \x11 x12 -> x11)
                                (lam $ \x11 ->
                                 zero + x9 * (x10 `unpair` \x12 x13 -> x13) `app` x11)) $ \x9 ->
                     let_ one $ \x10 ->
                     let_ (pair (superpose []) (lam $ \x11 -> zero)) $ \x11 ->
                     pair (superpose [(x8, x9 `unpair` \x12 x13 -> x12),
                                      (x10, x11 `unpair` \x12 x13 -> x12)])
                          (lam $ \x12 ->
                           zero + x8 * (x9 `unpair` \x13 x14 -> x14) `app` x12
                           + x10 * (x11 `unpair` \x13 x14 -> x14) `app` x12)) $ \x8 ->
               pair (withWeight x7 $ x8 `unpair` \x9 x10 -> x9)
                    (lam $ \x9 ->
                     zero + x7 * (x8 `unpair` \x10 x11 -> x11) `app` x9)) $ \x7 ->
         pair (withWeight x6 $ x7 `unpair` \x8 x9 -> x8)
              (lam $ \x8 -> zero + x6 * (x7 `unpair` \x9 x10 -> x10) `app` x8))
        `app` x0
        `app` x1 `unpair` \x2 x3 ->
        x3 `app` (lam $ \x4 -> one)) $ \x1 ->
  lam $ \x2 ->
  (x2 `unpair` \x3 x4 ->
   superpose [(half,
               uniform (real_ 3) (real_ 8) >>= \x5 -> dirac (pair (unsafeProb x5) x4)),
              (half,
               uniform one (real_ 4) >>= \x5 ->
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
    uniform zero (real_ 3600) >>= \x29 ->
    uniform zero (real_ 360) >>= \x30 ->
    uniform (negate (real_ 23)/(real_ 500) * (real_ 180) + (real_ 107)/(real_ 10)) (negate (real_ 23)/(real_ 500) * zero + (real_ 107)/(real_ 10)) >>= \x31 ->
    (
        normal_0_1 >>= \x32 ->
        normal_0_1 >>= \x33 ->
        dirac (x27 + fromProb x28 * (x32 / x33))
    ) >>= \x32 ->
    dirac (pair x29 (pair x30 (pair x31 (exp x32))))


---- this comes from Examples.Seismic.trueDetection
--seismicTrueDetection
--    :: (ABT Term abt)
--    => abt '[] (HPair 'HReal (HPair 'HReal (HPair 'HReal (HPair 'HReal (HPair 'HReal (HPair 'HProb (HPair 'HProb (HPair 'HProb (HPair 'HReal (HPair 'HReal (HPair 'HReal (HPair 'HProb (HPair 'HProb (HPair 'HReal 'HProb))))))))))))))
--    -> abt '[] (HPair 'HReal (HPair 'HReal (HPair 'HProb 'HReal)))
--    -> abt '[] ('HMeasure (HEither HUnit (HPair 'HReal (HPair 'HReal (HPair 'HReal 'HProb)))))
--seismicTrueDetection x0 x1 =
--    let deg2rad x = x * pi / 180 in -- manual CSE
--    x0 `unpair` \x2 x3 ->
--    x3 `unpair` \x4 x5 ->
--    x5 `unpair` \x6 x7 ->
--    x7 `unpair` \x8 x9 ->
--    x9 `unpair` \x10 x11 ->
--    x11 `unpair` \x12 x13 ->
--    x13 `unpair` \x14 x15 ->
--    x15 `unpair` \x16 x17 ->
--    x17 `unpair` \x18 x19 ->
--    x19 `unpair` \x20 x21 ->
--    x21 `unpair` \x22 x23 ->
--    x23 `unpair` \x24 x25 ->
--    x25 `unpair` \x26 x27 ->
--    x27 `unpair` \x28 x29 ->
--    x1 `unpair` \x30 x31 ->
--    x31 `unpair` \x32 x33 ->
--    x33 `unpair` \x34 x35 ->
--    superpose
--        [(recip (one + exp (negate
--            ( x6
--            + x8 * fromProb x34
--            + x10 * (deg2rad
--                (atan (sqrt
--                    ( (cos (deg2rad x32) * sin (deg2rad (x30 - x2))) ** 2
--                    +   ( cos (deg2rad x4) * sin (deg2rad x32)
--                        - sin (deg2rad x4)
--                            * cos (deg2rad x32)
--                            * cos (deg2rad (x30 - x2))
--                        ) ** 2
--                    )
--                    /   ( sin (deg2rad x4)
--                            * sin (deg2rad x32)
--                        + cos (deg2rad x4)
--                            * cos (deg2rad x32)
--                            * cos (deg2rad (x30 - x2))))
--                + if_
--                    ( sin (deg2rad x4)
--                        * sin (deg2rad x32)
--                    + cos (deg2rad x4)
--                        * cos (deg2rad x32)
--                        * cos (deg2rad (x30 - x2))
--                    < zero)
--                    pi
--                    zero)))))
--            , dirac true)
--        , (one - recip (one + exp (negate
--            ( x6
--            + x8 * fromProb x34
--            + x10 * (deg2rad
--                (atan (sqrt
--                    ( (cos (deg2rad x32) * sin (deg2rad (x30 - x2))) ** 2
--                    +   ( cos (deg2rad x4)
--                            * sin (deg2rad x32)
--                        - sin (deg2rad x4)
--                            * cos (deg2rad x32)
--                            * cos (deg2rad (x30 - x2))) ** 2
--                    )
--                    /   ( sin (deg2rad x4)
--                            * sin (deg2rad x32)
--                        + cos (deg2rad x4)
--                            * cos (deg2rad x32)
--                            * cos (deg2rad (x30 - x2))))
--                + if_
--                    ( sin (deg2rad x4)
--                        * sin (deg2rad x32)
--                    + cos (deg2rad x4)
--                        * cos (deg2rad x32)
--                        * cos (deg2rad (x30 - x2))
--                    < zero)
--                    pi
--                    zero)))))
--            , dirac false)
--        ] >>= \x36 ->
--    if_ (if_ x36 false true)
--      (dirac (left unit))
--      ((gamma_1_1 >>= \x37 ->
--        normal_0_1 >>= \x38 ->
--        dirac (x35
--               + (-23/1000
--                   * ((atan (sqrt ((cos (deg2rad x32) * sin (deg2rad (x30 - x2))) ** 2
--                                   + (cos (deg2rad x4) * sin (deg2rad x32) - sin (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))) ** 2)
--                             / (sin (deg2rad x4) * sin (deg2rad x32) + cos (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))))
--                       + if_ (sin (deg2rad x4) * sin (deg2rad x32) + cos (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))
--                              < zero)
--                             pi
--                             zero)
--                      * 180
--                      / pi)
--                     ** 2
--                  + 107/10
--                    * ((atan (sqrt ((cos (deg2rad x32) * sin (deg2rad (x30 - x2))) ** 2
--                                    + (cos (deg2rad x4) * sin (deg2rad x32) - sin (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))) ** 2)
--                              / (sin (deg2rad x4) * sin (deg2rad x32) + cos (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))))
--                        + if_ (sin (deg2rad x4) * sin (deg2rad x32) + cos (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))
--                               < zero)
--                              pi
--                              zero)
--                       * 180
--                       / pi)
--                  + 5)
--               + x38 * fromProb (x12 * sqrt (2 * x37)))) >>= \x37 ->
--       if_ (3600 < x37)
--           (dirac (left unit))
--           ((gamma_1_1 >>= \x38 -> normal_0_1 >>= \x39 -> dirac (zero + x39 * fromProb (x14 * sqrt (2 * x38)))) >>= \x38 ->
--            (counting >>= \x39 ->
--             if_ (if_ (if_ ((atan (sin (deg2rad (x30 - x2))
--                                   / (cos (deg2rad x4) * tan (deg2rad x32) - sin (deg2rad x4) * cos (deg2rad (x30 - x2))))
--                             + if_ (cos (deg2rad x4) * tan (deg2rad x32) - sin (deg2rad x4) * cos (deg2rad (x30 - x2)) < zero)
--                                   (if_ (sin (deg2rad (x30 - x2)) < zero) (-pi) pi)
--                                   zero)
--                            * 180
--                            / pi
--                            + x38
--                            + 360 * fromInt x39
--                            < zero)
--                           false
--                           true)
--                      ((atan (sin (deg2rad (x30 - x2))
--                              / (cos (deg2rad x4) * tan (deg2rad x32) - sin (deg2rad x4) * cos (deg2rad (x30 - x2))))
--                        + if_ (cos (deg2rad x4) * tan (deg2rad x32) - sin (deg2rad x4) * cos (deg2rad (x30 - x2)) < zero)
--                              (if_ (sin (deg2rad (x30 - x2)) < zero) (-pi) pi)
--                              zero)
--                       * 180
--                       / pi
--                       + x38
--                       + 360 * fromInt x39
--                       < 360)
--                      false)
--                 (dirac ((atan (sin (deg2rad (x30 - x2))
--                                / (cos (deg2rad x4) * tan (deg2rad x32) - sin (deg2rad x4) * cos (deg2rad (x30 - x2))))
--                          + if_ (cos (deg2rad x4) * tan (deg2rad x32) - sin (deg2rad x4) * cos (deg2rad (x30 - x2)) < zero)
--                                (if_ (sin (deg2rad (x30 - x2)) < zero) (-pi) pi)
--                                zero)
--                         * 180
--                         / pi
--                         + x38
--                         + 360 * fromInt x39))
--                 (superpose [])) >>= \x39 ->
--            (gamma_1_1 >>= \x40 ->
--             normal_0_1 >>= \x41 ->
--             dirac (-23/500
--                     * ((atan (sqrt ((cos (deg2rad x32) * sin (deg2rad (x30 - x2))) ** 2
--                                     + (cos (deg2rad x4) * sin (deg2rad x32) - sin (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))) ** 2)
--                               / (sin (deg2rad x4) * sin (deg2rad x32) + cos (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))))
--                         + if_ (sin (deg2rad x4) * sin (deg2rad x32) + cos (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))
--                                < zero)
--                               pi
--                               zero)
--                        * 180
--                        / pi)
--                    + 107/10
--                    + x41 * fromProb (x16 * sqrt (2 * x40)))) >>= \x40 ->
--            normal (x18 + x20 * fromProb x34
--                    + x22
--                      * ((atan (sqrt ((cos (deg2rad x32) * sin (deg2rad (x30 - x2))) ** 2
--                                      + (cos (deg2rad x4) * sin (deg2rad x32) - sin (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))) ** 2)
--                                / (sin (deg2rad x4) * sin (deg2rad x32) + cos (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))))
--                          + if_ (sin (deg2rad x4) * sin (deg2rad x32) + cos (deg2rad x4) * cos (deg2rad x32) * cos (deg2rad (x30 - x2))
--                                 < zero)
--                                pi
--                                zero)
--                         * 180
--                         / pi))
--                   x24 >>= \x41 ->
--            dirac (right (pair x37 (pair x39 (pair x40 (exp x41)))))))


--tdl :: (ABT Term abt) => abt '[]
--    (   (HPair 'HReal
--        (HPair 'HReal
--        (HPair 'HReal
--        (HPair 'HReal
--        (HPair 'HReal
--        (HPair 'HProb
--        (HPair 'HProb
--        (HPair 'HProb
--        (HPair 'HReal
--        (HPair 'HReal
--        (HPair 'HReal
--        (HPair 'HProb
--        (HPair 'HProb
--        (HPair 'HReal
--        'HProb))))))))))))))
--    ':->
--        (HPair 'HReal
--        (HPair 'HReal
--        (HPair 'HProb
--        'HReal)))
--    ':-> 'HMeasure HUnit)
--tdl =
--    lam $ \x0 ->
--    lam $ \x1 -> 
--    seismicTrueDetection x0 x1 >>= \z -> 
--    uneither z dirac (\_ -> superpose [])
--tdr :: (ABT Term abt) => abt '[]
--    (   (HPair 'HReal
--        (HPair 'HReal
--        (HPair 'HReal
--        (HPair 'HReal
--        (HPair 'HReal
--        (HPair 'HProb
--        (HPair 'HProb
--        (HPair 'HProb
--        (HPair 'HReal
--        (HPair 'HReal
--        (HPair 'HReal
--        (HPair 'HProb
--        (HPair 'HProb
--        (HPair 'HReal
--        'HProb))))))))))))))
--    ':->
--        (HPair 'HReal
--        (HPair 'HReal
--        (HPair 'HProb
--        'HReal)))
--    ':-> 'HMeasure (HPair 'HReal (HPair 'HReal (HPair 'HReal 'HProb))))
--tdr =
--    lam $ \x0 ->
--    lam $ \x1 -> 
--    seismicTrueDetection x0 x1 >>= \z -> 
--    uneither z (\_ -> superpose []) dirac

---- from Examples/HMMContinuous.hs
--kalman :: (ABT Term abt) => abt '[]
--    (   (HPair 'HProb
--        (HPair 'HProb
--        (HPair 'HReal
--        (HPair 'HReal
--        (HPair 'HReal
--        'HProb)))))
--    ':->
--        (HPair 'HProb
--        (HPair 'HProb
--        (HPair 'HReal
--        (HPair 'HReal
--        (HPair 'HReal
--        'HProb)))))
--    ':-> 'HReal
--    ':-> 'HMeasure 'HReal)
--kalman =
--    lam $ \m ->
--    lam $ \n ->
--    reflect m `bindo` reflect n
--    where
--    reflect m0 =
--        unpair m0 $ \a m1 ->
--        unpair m1 $ \b m2 ->
--        unpair m2 $ \c m3 ->
--        unpair m3 $ \d m4 ->
--        unpair m4 $ \e f ->
--        lam $ \s ->
--        weight (a * exp (- fromProb b * (s - c) ** 2)) $
--        normal (d * s + e) f

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

--seismic :: (ABT Term abt) => abt '[]
--    (SE.HStation
--    ':-> HPair 'HReal (HPair 'HReal (HPair 'HProb 'HReal))
--    ':-> HPair 'HReal (HPair 'HReal (HPair 'HReal 'HProb))
--    ':-> 'HMeasure 'HProb)
--seismic = lam3 (\s e d -> dirac $ SE.densT s e d)

easyHMM :: (ABT Term abt) => abt '[]
    ('HMeasure (HPair (HPair 'HReal 'HReal) (HPair 'HProb 'HProb)))
easyHMM =
    gamma (prob_ 3)  one >>= \noiseT ->
    gamma_1_1 >>= \noiseE ->
    normal zero noiseT >>= \x1 ->
    normal x1 noiseE >>= \m1 ->
    normal x1 noiseT >>= \x2 ->
    normal x2 noiseE >>= \m2 ->
    dirac (pair (pair m1 m2) (pair noiseT noiseE))
