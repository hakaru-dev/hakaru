{-# LANGUAGE TypeFamilies, Rank2Types, FlexibleContexts, DataKinds #-}
module Tests.RoundTrip (allTests) where

import Language.Hakaru.Syntax
import Language.Hakaru.Expect (total)
import Language.Hakaru.Inference (priorAsProposal, mcmc, mh)

import qualified Examples.Seismic as SE

import Test.HUnit
import Tests.TestTools

import Tests.Models (t4, t4', norm, unif2)

testMeasureUnit :: Test
testMeasureUnit = test [
    "t1,t5"   ~: testSS [t1,t5] (factor $ fromRational (1/2)),
    "t10"     ~: testSS [t10] (superpose []),
    "t11,t22" ~: testSS [t11,t22] (dirac unit),
    "t12"     ~: testSS [] t12,
    "t20"     ~: testSS [t20] (lam (\y -> factor (y* fromRational (1/2)))),
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
    "t2"  ~: testSS [t2] (uniform 0 1 `bind` dirac . unsafeProb),
    "t26" ~: testSS [t26] (dirac $ fromRational (1/2)),
    "t30" ~: testSS [] t30,
    "t33" ~: testSS [] t33,
    "t34" ~: testSS [t34] (dirac 3),
    "t35" ~: testSS [t35] (lam (\x -> if_ (less x 4) (dirac 3) (dirac 5))),
    "t38" ~: testSS [] t38,
    "t42" ~: testSS [t42] (dirac 1),
    "t49" ~: testSS [] t49,
    "t61" ~: testSS [t61] t61',
    "t66" ~: testSS [] t66,
    "t67" ~: testSS [] t67,
    "t69x" ~: testSS [t69x] (dirac 1.5),
    "t69y" ~: testSS [t69y] (dirac 3.5)
    ]

testMeasureReal :: Test
testMeasureReal = test
  [ "t3"  ~: testSS [] t3
  , "t6"  ~: testSS [t6'] t6
  , "t7"  ~: testSS [t7] t7'
  , "t7n" ~: testSS [t7n] t7n'
  , "t8'" ~: testSS [t8'] (lam $ \s1 -> lam $ \s2 -> normal 0 (sqrt_ (s1 ^ 2 + s2 ^ 2)))
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
  , "t70a" ~: testSS [t70a] (uniform 1 3)
  , "t71a" ~: testSS [t71a] (uniform 1 3)
  , "t72a" ~: testSS [t72a] (weight 0.5 $ uniform 1 2)
  , "t73a" ~: testSS [t73a] (superpose [])
  , "t74a" ~: testSS [t74a] (superpose [])
  , "t70b" ~: testSS [t70b] (superpose [])
  , "t71b" ~: testSS [t71b] (superpose [])
  , "t72b" ~: testSS [t72b] (weight 0.5 $ uniform 2 3)
  , "t73b" ~: testSS [t73b] (uniform 1 3)
  , "t74b" ~: testSS [t74b] (uniform 1 3)
  , "t70c" ~: testSS [t70c] (uniform 1 3)
  , "t71c" ~: testSS [t71c] (uniform 1 3)
  , "t72c" ~: testSS [t72c] (weight 0.5 $ uniform 1 2)
  , "t73c" ~: testSS [t73c] (superpose [])
  , "t74c" ~: testSS [t74c] (superpose [])
  , "t70d" ~: testSS [t70d] (superpose [])
  , "t71d" ~: testSS [t71d] (superpose [])
  , "t72d" ~: testSS [t72d] (weight 0.5 $ uniform 2 3)
  , "t73d" ~: testSS [t73d] (uniform 1 3)
  , "t74d" ~: testSS [t74d] (uniform 1 3)
  , "t76" ~: testS t76
  , "t78" ~: testSS [t78] t78'
  , "t79" ~: testSS [t79] (dirac 1)
  , "t80" ~: testS t80
  , "t81" ~: testSS [] t81
  , "kalman" ~: testS kalman
  , "seismic" ~: testSS [] seismic
  , "lebesgue1" ~: testSS [] (lebesgue `bind` \x -> if_ (less 42 x) (dirac x) (superpose []))
  , "lebesgue2" ~: testSS [] (lebesgue `bind` \x -> if_ (less x 42) (dirac x) (superpose []))
  , "lebesgue3" ~: testSS [lebesgue `bind` \x -> if_ (and_ [less x 42, less 40 x]) (dirac x) (superpose [])] (weight 2 $ uniform 40 42)
  , "testexponential" ~: testS testexponential
  , "testcauchy" ~: testS testCauchy
  , "exceptionLebesgue" ~: testSS [lebesgue `bind` \x -> dirac (if_ (equal x 3) 1 x)] lebesgue
  , "exceptionUniform"  ~: testSS [uniform 2 4 `bind` \x -> dirac (if_ (equal x 3) 1 x)] (uniform 2 4)
    -- "two_coins" ~: testS two_coins -- needs support for lists
    ]

testMeasureInt :: Test
testMeasureInt = test
  [ "t75"  ~: testS t75
  , "t75'" ~: testS t75'
  , "exceptionCounting" ~: testSS [] (counting `bind` \x -> dirac (if_ (equal x 3) 1 x)) -- Jacques wrote: "bug: [simp_pw_equal] implicitly assumes the ambient measure is Lebesgue"
  , "exceptionSuperpose" ~: testSS [(superpose [(1/3, dirac 2), (1/3, dirac 3), (1/3, dirac 4)] `asTypeOf` counting) `bind` \x -> dirac (if_ (equal x 3) 1 x)] (let p = fromRational (1/3) in superpose [(p, dirac 1), (p, dirac 2), (p, dirac 4)])
    ]

testMeasurePair :: Test
testMeasurePair = test [
    "t4"            ~: testSS [t4] t4',
    "t8"            ~: testSS [] t8,
    "t23"           ~: testSS [t23] t23',
    "t48"           ~: testS t48,
    "t52"           ~: testSS [t52] t52',
    "dup"           ~: testSS [dup (normal 0 1)] (liftM2 pair (normal 0 1) (normal 0 1)),
    "norm"          ~: testSS [] norm,
    "norm_nox"      ~: testSS [norm_nox] (normal 0 (sqrt_ 2)),
    "norm_noy"      ~: testSS [norm_noy] (normal 0 1),
    "flipped_norm"  ~: testSS [liftM swap_ norm] flipped_norm,
    "priorProp"     ~: testSS [lam (priorAsProposal norm)]
                              (lam $ \x -> superpose [(fromRational (1/2), normal 0 1         `bind` \y -> dirac (pair y (snd_ x))),
                                                      (fromRational (1/2), normal 0 (sqrt_ 2) `bind` \y -> dirac (pair (fst_ x) y))]),
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

-- In Maple, should 'evaluate' to "\c -> 1/2*c(Unit)"
t1 :: (Mochastic repr) => repr (HMeasure HUnit)
t1 = uniform 0 1 `bind` \x -> factor (unsafeProb x)

t2 :: Mochastic repr => repr (HMeasure HProb)
t2 = beta 1 1

t3 :: Mochastic repr => repr (HMeasure HReal)
t3 = normal 0 10

-- t5 is "the same" as t1.
t5 :: Mochastic repr => repr (HMeasure HUnit)
t5 = factor (1/2) `bind_` dirac unit

t6, t6' :: Mochastic repr => repr (HMeasure HReal)
t6 = dirac 5
t6' = superpose [(1, dirac 5)]

t7,t7', t7n,t7n' :: Mochastic repr => repr (HMeasure HReal)
t7   = uniform 0 1 `bind` \x -> factor (unsafeProb (x+1)) `bind_` dirac (x*x)
t7'  = uniform 0 1 `bind` \x -> superpose [(unsafeProb (x+1), dirac (x*x))]
t7n  = uniform (-1) 0 `bind` \x -> factor (unsafeProb (x+1)) `bind_` dirac (x*x)
t7n' = uniform (-1) 0 `bind` \x -> superpose [(unsafeProb (x + 1), dirac (x*x))]

-- For sampling efficiency (to keep importance weights at or close to 1),
-- t8 below should read back to uses of "normal", not uses of "lebesgue"
-- then "factor".
t8 :: Mochastic repr => repr (HMeasure (HPair HReal HReal))
t8 = normal 0 10 `bind` \x -> normal x 20 `bind` \y -> dirac (pair x y)

-- Normal is conjugate to normal
t8' :: (Lambda repr, Mochastic repr)
    => repr (HFun HProb (HFun HProb (HMeasure HReal)))
t8' = lam $ \s1 ->
      lam $ \s2 ->
      normal 0 s1 `bind` \x -> normal x s2

t9 :: Mochastic repr => repr (HMeasure HReal)
t9 = lebesgue `bind` \x -> 
     factor (if_ (and_ [less 3 x, less x 7]) (fromRational (1/2)) 0) `bind_` 
     dirac x

t10 :: Mochastic repr => repr (HMeasure HUnit)
t10 = factor 0

t11 :: Mochastic repr => repr (HMeasure HUnit)
t11 = factor 1

t12 :: Mochastic repr => repr (HMeasure HUnit)
t12 = factor 2

t13,t13' :: Mochastic repr => repr (HMeasure HReal)
t13 = bern (3/5) `bind` \b -> dirac (if_ b 37 42)
t13' = superpose [(fromRational (3/5), dirac 37), 
                  (fromRational (2/5), dirac 42)]

t14,t14' :: Mochastic repr => repr (HMeasure HReal)
t14 = bern (3/5) `bind` \b ->
      if_ b t13 (bern (2/7) `bind` \b' ->
                 if_ b' (uniform 10 12) (uniform 14 16))
t14' = superpose 
  [ (fromRational (9/25), dirac 37)
  , (fromRational (6/25), dirac 42)
  , (fromRational (4/35), uniform 10 12)
  , (fromRational (2/7) , uniform 14 16)
  ]

t20 :: (Lambda repr, Mochastic repr) => repr (HFun HProb (HMeasure HUnit))
t20 = lam (\y -> uniform 0 1 `bind` \x -> factor (unsafeProb x * y))

t21 :: (Mochastic repr, Integrate repr, Lambda repr) =>
       repr (HFun HReal (HMeasure HReal))
t21 = mcmc (`normal` 1) (normal 0 5)

t22 :: Mochastic repr => repr (HMeasure HUnit)
t22 = bern (1/2) `bind_` dirac unit

-- was called bayesNet in Nov.06 msg by Ken for exact inference
t23, t23' :: Mochastic repr => repr (HMeasure (HPair HBool HBool))
t23 = bern (1/2) `bind` \a ->
               bern (if_ a (9/10) (1/10)) `bind` \b ->
               bern (if_ a (9/10) (1/10)) `bind` \c ->
               dirac (pair b c)
t23' = superpose [(fromRational (41/100), dirac (pair true true)),
                  (fromRational ( 9/100), dirac (pair true false)),
                  (fromRational ( 9/100), dirac (pair false true)),
                  (fromRational (41/100), dirac (pair false false))]

t24,t24' :: (Mochastic repr, Lambda repr) => repr (HFun HProb (HMeasure HUnit))
t24 = lam (\x ->
      uniform 0 1 `bind` \y ->
      uniform 0 1 `bind` \z ->
      factor (x * exp_ (cos y) * unsafeProb z))
t24' = lam (\x ->
      uniform 0 1 `bind` \y ->
      factor (x * exp_ (cos y) * fromRational (1/2)))

t25,t25' :: (Mochastic repr, Lambda repr) => repr (HFun HProb (HFun HReal (HMeasure HUnit)))
t25 = lam (\x -> lam (\y ->
    uniform 0 1 `bind` \z ->
    factor (x * exp_ (cos y) * unsafeProb z)))
t25' = lam (\x -> lam (\y ->
    factor (x * exp_ (cos y) * fromRational (1/2))))

t26 :: (Mochastic repr, Lambda repr, Integrate repr) => repr (HMeasure HProb)
t26 = dirac (total t1)

t28 :: Mochastic repr => repr (HMeasure HReal)
t28 = uniform 0 1

t29 :: Mochastic repr => repr (HMeasure HReal)
t29 = uniform 0 1 `bind` \x -> dirac (exp x)

t30 :: Mochastic repr => repr (HMeasure HProb)
t30 = uniform 0 1 `bind` \x -> dirac (exp_ x)

t31 :: Mochastic repr => repr (HMeasure HReal)
t31 = uniform (-1) 1

t32 :: Mochastic repr => repr (HMeasure HReal)
t32 = uniform (-1) 1 `bind` \x -> dirac (exp x)

t33 :: Mochastic repr => repr (HMeasure HProb)
t33 = uniform (-1) 1 `bind` \x -> dirac (exp_ x)

t34 :: Mochastic repr => repr (HMeasure HProb)
t34 = dirac (if_ (less (2 `asTypeOf` log_ 1) 4) 3 5)

t35 :: (Lambda repr, Mochastic repr) => repr (HFun HReal (HMeasure HProb))
t35 = lam (\x -> dirac (if_ (less (x `asTypeOf` log_ 1) 4) 3 5))

t36, t36' :: (Lambda repr, Mochastic repr) => repr (HFun HReal (HMeasure HReal))
t36 = lam (dirac . sqrt)
t36' = lam $ \x -> if_ (x `less` 0) (dirac (-337)) (dirac (sqrt x))

t37 :: (Lambda repr, Mochastic repr) => repr (HFun HReal (HMeasure HReal))
t37 = lam (dirac . recip)

t38 :: (Lambda repr, Mochastic repr) => repr (HFun HProb (HMeasure HProb))
t38 = lam (dirac . recip)

t39, t39' :: (Lambda repr, Mochastic repr) => repr (HFun HReal (HMeasure HReal))
t39 = lam (dirac . log)
t39' = lam $ \x -> if_ (x `less` 0) (dirac (-337)) (dirac (log x))

t40 :: (Lambda repr, Mochastic repr) => repr (HFun HProb (HMeasure HReal))
t40 = lam (dirac . log_)

t42 :: (Lambda repr, Integrate repr, Mochastic repr) => repr (HMeasure HProb)
t42 = dirac $ total $ uniform 0 2 `bind` dirac . unsafeProb

t43, t43', t43'' :: (Lambda repr, Mochastic repr) => repr (HFun HBool (HMeasure HReal))
t43   = lam $ \b -> if_ b (uniform 0 1) (beta 1 1 `bind` dirac . fromProb)
t43'  = lam $ \b -> if_ b (uniform 0 1) (uniform 0 1)
t43'' = lam $ \_ -> uniform 0 1

t44Add, t44Add', t44Mul, t44Mul' :: (Lambda repr, Mochastic repr) => repr (HFun HReal (HFun HReal (HMeasure HUnit)))
t44Add  = lam $ \x -> lam $ \y -> factor (unsafeProb (x * x) + unsafeProb (y * y))
t44Add' = lam $ \x -> lam $ \y -> factor (unsafeProb (x ** 2 + y ** 2))
t44Mul  = lam $ \x -> lam $ \y -> factor (unsafeProb (x * x * y * y))
t44Mul' = lam $ \x -> lam $ \y -> factor (unsafeProb (x ** 2) * unsafeProb (y ** 2))

-- t45, t46, t47 are all equivalent.
-- But t47 is worse than t45 and t46 because the importance weight generated by
-- t47 as a sampler varies between 0 and 1 whereas the importance weight generated
-- by t45 and t46 is always 1.  In general it's good to reduce weight variance.
t45 :: (Mochastic repr) => repr (HMeasure HReal)
t45 = normal 4 5 `bind` \x -> if_ (less x 3) (dirac (x*x)) (dirac (x-1))

t46 :: (Mochastic repr) => repr (HMeasure HReal)
t46 = normal 4 5 `bind` \x -> dirac (if_ (less x 3) (x*x) (x-1))

t47 :: (Mochastic repr) => repr (HMeasure HReal)
t47 =
  superpose [(1, (normal 4 5 `bind` \x -> if_ (less x 3) (dirac (x*x)) (superpose []))),
             (1, (normal 4 5 `bind` \x -> if_ (less x 3) (superpose []) (dirac (x-1))))]

t48 :: (Mochastic repr, Lambda repr) => repr (HFun (HPair HReal HReal) (HMeasure HReal))
t48 = lam (\x -> uniform (-5) 7 `bind` \w -> dirac ((fst_ x + snd_ x) * w))

t49 :: (Mochastic repr) => repr (HMeasure HProb)
t49 = gamma 0.01 0.35

t50 :: (Mochastic repr) => repr (HMeasure HReal)
t50 = uniform 1 3 `bind` \x ->
      normal 1 (unsafeProb x)

t51 :: (Mochastic repr) => repr (HMeasure HReal)
t51 = uniform (-1) 1 `bind` \x ->
      normal x 1

-- Example 1 from Chang & Pollard's Conditioning as Disintegration
t52, t52' :: (Mochastic repr) => repr (HMeasure (HPair HReal (HPair HReal HReal)))
t52 = uniform 0 1 `bind` \x ->
      uniform 0 1 `bind` \y ->
      dirac (pair (max_ x y)
                  (pair x y))
t52' = uniform 0 1 `bind` \x2 ->
       superpose [((unsafeProb (1 + (x2 * (-1)))),(uniform  x2 1) `bind` \x4 -> (dirac (pair x4 (pair x2 x4)))),
                  ((unsafeProb x2),(uniform  0 x2) `bind` \x4 -> (dirac (pair x2 (pair x2 x4))))]

t53, t53', t53'' :: (Mochastic repr, Lambda repr) => repr (HFun HReal (HMeasure HUnit))
t53 =
  lam $ \x ->
  superpose [(1, superpose [(1, if_ (0 `less` x)
                                    (if_ (x `less` 1) (dirac unit) (superpose []))
                                    (superpose []))]),
             (1, if_ false (dirac unit) (superpose []))]
t53' =
  lam $ \x ->
  superpose [(1, if_ (0 `less` x)
                     (if_ (x `less` 1) (dirac unit) (superpose []))
                     (superpose [])),
             (1, if_ false (dirac unit) (superpose []))]
t53'' =
  lam $ \x ->
  if_ (and_ [less 0 x, less x 1]) (dirac unit) (superpose [])

t54 :: (Mochastic repr, Lambda repr) => repr (HFun HReal (HMeasure HUnit))
t54 =
    lam $ \x0 ->
    (dirac x0 `bind` \x1 ->
     (uniform 0 1 `bind` \x2 -> dirac (-x2)) `bind` \x2 ->
     dirac (x1 + x2)) `bind` \x1 ->
    (((dirac 0 `bind` \x2 ->
       dirac x1 `bind` \x3 ->
       dirac (x2 `less` x3)) `bind` \x2 ->
      if_ x2
          (dirac x1 `bind` \x3 -> dirac (recip x3))
          (dirac 0)) `bind` \x2 ->
     factor (unsafeProb x2)) `bind_`
    (dirac x1 `bind` \x3 -> dirac (log x3)) `bind` \x3 ->
    (dirac x3 `bind` \x4 -> dirac (-x4)) `bind` \x4 ->
    ((dirac 0 `bind` \x5 ->
      dirac x4 `bind` \x6 ->
      dirac (x5 `less` x6)) `bind` \x5 ->
     if_ x5
         ((dirac x4 `bind` \x6 ->
           dirac 1 `bind` \x7 ->
           dirac (x6 `less` x7)) `bind` \x6 ->
          if_ x6 (dirac 1) (dirac 0))
         (dirac 0)) `bind` \x5 ->
    factor (unsafeProb x5)

t55, t55' :: (Mochastic repr, Lambda repr) => repr (HFun HReal (HMeasure HUnit))
t55  = lam $ \t -> uniform 0 1 `bind` \x ->
                   if_ (less x t) (dirac unit) $
                   superpose []
t55' = lam $ \t -> if_ (less t 0) (superpose []) $
                   if_ (less t 1) (factor (unsafeProb t)) $
                   dirac unit

t56, t56', t56'' :: (Mochastic repr, Lambda repr) => repr (HFun HReal (HMeasure HUnit))
t56 =
    lam $ \x0 ->
    (dirac x0 `bind` \x1 ->
     (uniform 0 1 `bind` \x2 -> dirac (-x2)) `bind` \x2 ->
     dirac (x1 + x2)) `bind` \x1 ->
    ((dirac 0 `bind` \x2 ->
      dirac x1 `bind` \x3 ->
      dirac (x2 `less` x3)) `bind` \x2 ->
     if_ x2
         ((dirac x1 `bind` \x3 ->
           dirac 1 `bind` \x4 ->
           dirac (x3 `less` x4)) `bind` \x3 ->
          if_ x3 (dirac 1) (dirac 0))
         (dirac 0)) `bind` \x2 ->
    weight (unsafeProb x2) (dirac unit)
t56' =
    lam $ \x0 ->
    uniform 0 1 `bind` \x1 ->
    if_ (and_ [x0 - 1 `less` x1, x1 `less` x0])
        (dirac unit)
        (superpose [])
t56'' =
    lam $ \t ->
    if_ (lesseq t 0) (superpose []) $
    if_ (lesseq t 1) (factor (unsafeProb t)) $
    if_ (lesseq t 2) (factor (unsafeProb (2 + t*(-1)))) $
    superpose []

t57, t57' :: (Mochastic repr, Lambda repr) => repr (HFun HReal (HMeasure HUnit))
t57 = lam $ \t -> superpose
  [(1, if_ (less t 1) (dirac unit) (superpose [])),
   (1, if_ (less 0 t) (dirac unit) (superpose []))]
t57' = lam $ \t -> 
  if_ (and_ [(t `less` 1), (0 `less` t)]) (factor 2) (dirac unit)

t58, t58' :: (Mochastic repr, Lambda repr) => repr (HFun HReal (HMeasure HUnit))
t58 = lam $ \t -> superpose
  [(1, if_ (and_ [less 0 t, less t 2]) (dirac unit) (superpose [])),
   (1, if_ (and_ [less 1 t, less t 3]) (dirac unit) (superpose []))]
t58' = lam $ \t ->
  if_ (if_ (0 `less` t) (t `less` 2) false)
      (if_ (if_ (1 `less` t) (t `less` 3) false)
           (weight 2 (dirac unit))
           (dirac unit))
      (if_ (if_ (1 `less` t) (t `less` 3) false)
           (dirac unit)
           (superpose []))

t59 :: (Mochastic repr, Lambda repr) => repr (HFun HReal (HMeasure HUnit))
t59 =
    lam $ \x0 ->
    ((uniform 0 1 `bind` \x1 -> dirac (recip x1)) `bind` \x1 ->
     (((dirac 0 `bind` \x2 ->
        dirac x1 `bind` \x3 ->
        dirac (x2 `less` x3)) `bind` \x2 ->
       if_ x2
           (dirac x1)
           (dirac x1 `bind` \x3 -> dirac (-x3))) `bind` \x2 ->
      weight (unsafeProb x2) (dirac unit)) `bind` \_ ->
     dirac x0 `bind` \x3 ->
     dirac x1 `bind` \x4 ->
     dirac (x3 * x4)) `bind` \x1 ->
    (dirac x1 `bind` \x2 ->
     (uniform 0 1 `bind` \x3 -> dirac (-x3)) `bind` \x3 ->
     dirac (x2 + x3)) `bind` \x2 ->
    ((dirac 0 `bind` \x3 ->
      dirac x2 `bind` \x4 ->
      dirac (x3 `less` x4)) `bind` \x3 ->
     if_ x3
         ((dirac x2 `bind` \x4 ->
           dirac 1 `bind` \x5 ->
           dirac (x4 `less` x5)) `bind` \x4 ->
          if_ x4 (dirac 1) (dirac 0))
         (dirac 0)) `bind` \x3 ->
    weight (unsafeProb x3) (dirac unit)

t60,t60',t60'' :: (Mochastic repr, Lambda repr) => repr (HFun HReal (HMeasure HUnit))
t60 =
    lam $ \x0 ->
    (((uniform 0 1 `bind` \x1 ->
       uniform 0 1 `bind` \x2 ->
       dirac (x1 + x2)) `bind` \x1 ->
      dirac (recip x1)) `bind` \x1 ->
     (((dirac 0 `bind` \x2 ->
        dirac x1 `bind` \x3 ->
        dirac (x2 `less` x3)) `bind` \x2 ->
       if_ x2
           (dirac x1)
           (dirac x1 `bind` \x3 -> dirac (-x3))) `bind` \x2 ->
      weight (unsafeProb x2) (dirac unit)) `bind` \_ ->
     dirac x0 `bind` \x3 ->
     dirac x1 `bind` \x4 ->
     dirac (x3 * x4)) `bind` \x1 ->
    ((dirac 0 `bind` \x2 ->
      dirac x1 `bind` \x3 ->
      dirac (x2 `less` x3)) `bind` \x2 ->
     if_ x2
         ((dirac x1 `bind` \x3 ->
           dirac 1 `bind` \x4 ->
           dirac (x3 `less` x4)) `bind` \x3 ->
          if_ x3 (dirac 1) (dirac 0))
         (dirac 0)) `bind` \x2 ->
    weight (unsafeProb x2) (dirac unit)
t60' =
    lam $ \x0 ->
    uniform 0 1 `bind` \x1 ->
    uniform 0 1 `bind` \x2 ->
    if_ (if_ (0 `less` x0 * recip (x2 + x1))
             (x0 * recip (x2 + x1) `less` 1)
             false)
        (weight (unsafeProb ((x2 + x1) ** (-1))) (dirac unit))
        (superpose [])
t60'' =
    lam $ \x0 ->
    uniform 0 1 `bind` \x1 ->
    uniform 0 1 `bind` \x2 ->
    if_ (if_ (0 `less` x0 * recip (x2 + x1))
             (x0 * recip (x2 + x1) `less` 1)
             false)
        (weight (recip (unsafeProb (x2 + x1))) (dirac unit))
        (superpose [])

t61, t61' :: (Mochastic repr, Lambda repr) => repr (HFun HReal (HMeasure HProb))
t61 = lam $ \x -> if_ (less x 0) (dirac 0) $ dirac $ unsafeProb $ recip x
t61'= lam $ \x -> if_ (less x 0) (dirac 0) $ dirac $ recip $ unsafeProb x

-- "Special case" of t56
t62, t62' :: (Mochastic repr, Lambda repr) => repr (HFun HReal (HFun HReal (HMeasure HUnit)))
t62 = lam $ \t ->
      lam $ \x ->
      uniform 0 1 `bind` \y ->
      if_ (and_ [0 `less` (t/x-y), (t/x-y) `less` 1])
          (dirac unit)
          (superpose [])
t62'= lam $ \t ->
      lam $ \x ->
      if_ (lesseq (t * recip x) 0) (superpose []) $
      if_ (lesseq (t * recip x) 1) (factor (unsafeProb (t/x))) $
      if_ (lesseq (t * recip x) 2) (factor (unsafeProb (2-t/x))) $
      superpose []

-- "Scalar multiple" of t62
t63, t63' :: (Mochastic repr, Lambda repr) => repr (HFun HReal (HMeasure HUnit))
t63 = lam $ \t ->
      uniform 0 1 `bind` \x ->
      uniform 0 1 `bind` \y ->
      if_ (and_ [0 `less` (t/x-y), (t/x-y) `less` 1])
          (factor (recip (unsafeProb x)))
          (superpose [])
t63'= lam $ \t ->
      uniform 0 1 `bind` \x ->
      if_ (lesseq (t * recip x) 0) (superpose []) $
      if_ (lesseq (t * recip x) 1) (factor (unsafeProb (t/x) / unsafeProb x)) $
      if_ (lesseq (t * recip x) 2) (factor (unsafeProb (2-t/x) / unsafeProb x)) $
      superpose []

-- Density calculation for (Exp (Log StdRandom)) and StdRandom
t64, t64', t64'' :: (Mochastic repr, Lambda repr) => repr (HFun HReal (HMeasure HUnit))
t64 = lam $ \x0 ->
      (((dirac 0 `bind` \x1 ->
         dirac x0 `bind` \x2 ->
         dirac (x1 `less` x2)) `bind` \x1 ->
        if_ x1
            (dirac x0 `bind` \x2 -> dirac (recip x2))
            (dirac 0)) `bind` \x1 ->
       weight (unsafeProb x1) (dirac unit)) `bind` \_ ->
      (dirac x0 `bind` \x2 -> dirac (log x2)) `bind` \x2 ->
      ((dirac x2 `bind` \x3 -> dirac (exp x3)) `bind` \x3 ->
       weight (unsafeProb x3) (dirac unit)) `bind` \_ ->
      (dirac x2 `bind` \x4 -> dirac (exp x4)) `bind` \x4 ->
      ((dirac 0 `bind` \x5 ->
        dirac x4 `bind` \x6 ->
        dirac (x5 `less` x6)) `bind` \x5 ->
       if_ x5
           ((dirac x4 `bind` \x6 ->
             dirac 1 `bind` \x7 ->
             dirac (x6 `less` x7)) `bind` \x6 ->
            if_ x6 (dirac 1) (dirac 0))
           (dirac 0)) `bind` \x5 ->
      weight (unsafeProb x5) (dirac unit)
t64' =lam $ \x0 ->
      ((dirac 0 `bind` \x1 ->
        dirac x0 `bind` \x2 ->
        dirac (x1 `less` x2)) `bind` \x1 ->
       if_ x1
           ((dirac x0 `bind` \x2 ->
             dirac 1 `bind` \x3 ->
             dirac (x2 `less` x3)) `bind` \x2 ->
            if_ x2 (dirac 1) (dirac 0))
           (dirac 0)) `bind` \x1 ->
      weight (unsafeProb x1) (dirac unit)
t64''=lam $ \x0 ->
      if_ (0 `less` x0) 
          (if_ (x0 `less` 1)
               (dirac unit)
               (superpose []))
          (superpose [])

-- Density calculation for (Add StdRandom (Exp (Neg StdRandom))).
-- Maple can integrate this but we don't simplify it for some reason.
t65, t65' :: (Mochastic repr, Lambda repr) => repr (HFun HReal (HMeasure HUnit))
t65 = lam $ \t -> uniform 0 1 `bind` \x ->
      if_ (0 `less` t-x)
          (let_ (unsafeProb (t-x)) $ \t_x ->
           weight (recip t_x)
                  (if_ (and_ [0 `less` -log_ t_x, -log_ t_x `less` 1])
                       (dirac unit)
                       (superpose [])))
          (superpose [])
t65' = lam $ \t ->
       if_ (t `less` exp (-1)) (superpose [])
     $ if_ (t `less` 1) (factor (unsafeProb (log t + 1)))
     $ if_ (t `less` 1 + exp (-1)) (dirac unit)
     $ if_ (t `less` 2) (factor (unsafeProb (log (t + (-1)) * (-1))))
     $ superpose []

t66 :: (Mochastic repr) => repr (HMeasure HProb)
t66 = dirac (sqrt_ (3 + sqrt_ 3))

t67 :: (Lambda repr, Mochastic repr) => repr (HFun HProb (HFun HReal (HMeasure HProb)))
t67 = lam $ \p -> lam $ \r -> dirac (exp_ (r * fromProb p))

t68 :: (Lambda repr, Mochastic repr) => repr (HFun HProb (HFun HProb (HFun HReal (HMeasure HReal))))
t68 = lam $ \x4 ->
      lam $ \x5 ->
      lam $ \x1 ->
      lebesgue `bind` \x2 ->
      lebesgue `bind` \x3 ->
      weight (exp_ (-(x2 - x3) * (x2 - x3)
                     * recip (fromProb (2 * exp_ (log_ x4 * 2))))
              * recip x4
              * recip (exp_ (log_ (2 * pi_) * (1 / 2))))
             (weight (exp_ (-(x1 - x3) * (x1 - x3)
                             * recip (fromProb (2 * exp_ (log_ x5 * 2))))
                      * recip x5
                      * recip (exp_ (log_ (2 * pi_) * (1 / 2))))
                     (weight (exp_ (-x3 * x3
                                     * recip (fromProb (2 * exp_ (log_ x4 * 2))))
                              * recip x4
                              * recip (exp_ (log_ (2 * pi_) * (1 / 2))))
                             (dirac x2)))

t68' :: (Lambda repr, Mochastic repr) => repr (HFun HProb (HFun HReal (HMeasure HReal)))
t68' = lam $ \noise -> app (app t68 noise) noise

t69x, t69y :: (Lambda repr, Mochastic repr, Integrate repr) => repr (HMeasure HProb)
t69x = dirac (integrate 1 2 (\x -> integrate 3 4 (\_ -> unsafeProb x)))
t69y = dirac (integrate 1 2 (\_ -> integrate 3 4 (\y -> unsafeProb y)))

t70a, t71a, t72a, t73a, t74a :: (Mochastic repr) => repr (HMeasure HReal)
t70a = uniform 1 3 `bind` \x -> if_ (less 4 x) (superpose []) (dirac x)
t71a = uniform 1 3 `bind` \x -> if_ (less 3 x) (superpose []) (dirac x)
t72a = uniform 1 3 `bind` \x -> if_ (less 2 x) (superpose []) (dirac x)
t73a = uniform 1 3 `bind` \x -> if_ (less 1 x) (superpose []) (dirac x)
t74a = uniform 1 3 `bind` \x -> if_ (less 0 x) (superpose []) (dirac x)

t70b, t71b, t72b, t73b, t74b :: (Mochastic repr) => repr (HMeasure HReal)
t70b = uniform 1 3 `bind` \x -> if_ (less 4 x) (dirac x) (superpose [])
t71b = uniform 1 3 `bind` \x -> if_ (less 3 x) (dirac x) (superpose [])
t72b = uniform 1 3 `bind` \x -> if_ (less 2 x) (dirac x) (superpose [])
t73b = uniform 1 3 `bind` \x -> if_ (less 1 x) (dirac x) (superpose [])
t74b = uniform 1 3 `bind` \x -> if_ (less 0 x) (dirac x) (superpose [])

t70c, t71c, t72c, t73c, t74c :: (Mochastic repr) => repr (HMeasure HReal)
t70c = uniform 1 3 `bind` \x -> if_ (less x 4) (dirac x) (superpose [])
t71c = uniform 1 3 `bind` \x -> if_ (less x 3) (dirac x) (superpose [])
t72c = uniform 1 3 `bind` \x -> if_ (less x 2) (dirac x) (superpose [])
t73c = uniform 1 3 `bind` \x -> if_ (less x 1) (dirac x) (superpose [])
t74c = uniform 1 3 `bind` \x -> if_ (less x 0) (dirac x) (superpose [])

t70d, t71d, t72d, t73d, t74d :: (Mochastic repr) => repr (HMeasure HReal)
t70d = uniform 1 3 `bind` \x -> if_ (less x 4) (superpose []) (dirac x)
t71d = uniform 1 3 `bind` \x -> if_ (less x 3) (superpose []) (dirac x)
t72d = uniform 1 3 `bind` \x -> if_ (less x 2) (superpose []) (dirac x)
t73d = uniform 1 3 `bind` \x -> if_ (less x 1) (superpose []) (dirac x)
t74d = uniform 1 3 `bind` \x -> if_ (less x 0) (superpose []) (dirac x)

t75 :: (Mochastic repr) => repr (HMeasure HInt)
t75 = gamma 6 1 `bind` poisson

t75' :: (Lambda repr, Mochastic repr) => repr (HFun HProb (HMeasure HInt))
t75' = lam $ \x -> gamma x 1 `bind` poisson

t76 :: (Lambda repr, Mochastic repr) => repr (HFun HReal (HMeasure HReal))
t76 = lam $ \x ->
      lebesgue `bind` \y ->
      weight (unsafeProb (abs y)) $
      if_ (y `less` 1)
          (if_ (0 `less` y)
               (if_ (x * y `less` 1)
                    (if_ (0 `less` x * y)
                         (dirac (x * y))
                         (superpose []))
                    (superpose []))
               (superpose []))
          (superpose [])

-- the (x * (-1)) below is an unfortunate artifact not worth fixing
t77 :: (Lambda repr, Mochastic repr) => repr (HFun HReal (HMeasure HUnit))
t77 = lam $ \x ->
      if_ (less_ x 0)
          (factor (exp_ (x * (-1))))
          (factor (exp_ x))

t78, t78' :: (Lambda repr, Mochastic repr) => repr (HMeasure HReal)
t78 = uniform 0 2 `bind` \x2 -> weight (unsafeProb x2) (dirac x2)
t78' = liftM (fromProb . (*2)) (beta 2 1)

-- what does this simplify to?
t79 :: (Mochastic repr) => repr (HMeasure HReal)
t79 = dirac 3 `bind` \x -> dirac (if_ (equal x 3) 1 x)

t80 :: (Mochastic repr) => repr (HMeasure HReal)
t80 = gamma 1 1 `bind` \t -> normal 0 t

t81 :: (Mochastic repr) => repr (HMeasure HReal)
t81 = uniform 0 pi

-- Testing round-tripping of some other distributions
testexponential :: Mochastic repr => repr (HMeasure HProb)
testexponential = exponential (1/3)

testCauchy :: Mochastic repr => repr (HMeasure HReal)
testCauchy = cauchy 5 3

testMCMCPriorProp
    :: (Integrate repr, Mochastic repr, Lambda repr)
    => repr (HFun (HPair HReal HReal) (HMeasure (HPair HReal HReal)))
testMCMCPriorProp = mcmc (priorAsProposal norm) norm

testMHPriorProp
    :: (Integrate repr, Mochastic repr, Lambda repr)
    => repr (HFun (HPair HReal HReal) (HMeasure (HPair (HPair HReal HReal) HProb)))
testMHPriorProp = mh (priorAsProposal norm) norm

testPriorProp'
    :: (Integrate repr, Mochastic repr, Lambda repr)
    => repr (HFun (HPair HReal HReal) (HMeasure (HPair (HPair HReal HReal) HProb)))
testPriorProp' =
      (lam $ \old ->
       superpose [(fromRational (1/2),
                   normal 0 1 `bind` \x1 ->
                   dirac (pair (pair x1 (snd_ old))
                        (exp_ ((x1 * (-1) + (old `unpair` \x2 x3 -> x2))
                               * ((old `unpair` \x2 x3 -> x2) + (old `unpair` \x2 x3 -> x3) * (-2)
                                  + x1)
                               * (1/2))))),

                  (fromRational (1/2),
                   normal 0 (sqrt_ 2) `bind` \x1 ->
                   dirac (pair (pair (fst_ old) x1)
                        (exp_ ((x1 + (old `unpair` \x2 x3 -> x3) * (-1))
                               * ((old `unpair` \x2 x3 -> x3) + (old `unpair` \x2 x3 -> x2) * (-4)
                                  + x1)
                               * (-1/4)))))])

dup :: (Lambda repr, Mochastic repr) => repr (HMeasure a) -> repr (HMeasure (HPair a a))
dup m = let_ m (\m' -> liftM2 pair m' m')

norm_nox :: Mochastic repr => repr (HMeasure HReal)
norm_nox = normal 0 1 `bind` \x ->
           normal x 1 `bind` \y ->
           dirac y

norm_noy :: Mochastic repr => repr (HMeasure HReal)
norm_noy = normal 0 1 `bind` \x ->
           normal x 1 `bind_`
           dirac x

flipped_norm :: Mochastic repr => repr (HMeasure (HPair HReal HReal))
flipped_norm = normal 0 1 `bind` \x ->
               normal x 1 `bind` \y ->
               dirac (pair y x)

-- pull out some of the intermediate expressions for independent study
expr1 :: (Lambda repr, Mochastic repr) => repr (HFun HReal HProb)
expr1 =  (lam $ \x0 ->
          (lam $ \_ ->
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
                  (lam $ \x5 -> x5 `app` (x4 `unpair` \_ x7 -> x7)) `app` x3))
          `app` unit
          `app` x0
          `app` (lam $ \_ -> 1))

expr2 :: (Mochastic repr, Lambda repr) => repr (HFun HReal (HFun HReal HProb))
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
                  (lam $ \x7 -> x7 `app` (x6 `unpair` \_ x9 -> x9)) `app` x5))
          `app` x1
          `app` x2
          `app` (lam $ \_ -> 1))

-- the one we need in testKernel
expr3 :: (Mochastic repr, Lambda repr)
    => repr (HFun d HProb)
    -> repr (HFun d (HFun d HProb))
    -> repr d -> repr d -> repr HProb
expr3 x0 x1 x2 x3 = (if_ (1
                    `less` x0 `app` x3 / x1 `app` x2 `app` x3 * x1 `app` x3 `app` x2
                           / x0 `app` x2)
                   1
                   (x0 `app` x3 / x1 `app` x2 `app` x3 * x1 `app` x3 `app` x2
                    / x0 `app` x2))

-- testKernel :: Sample IO (HFun HReal (HMeasure HReal)
testKernel :: (Lambda repr, Mochastic repr) => repr (HFun HReal (HMeasure HReal))
testKernel =
-- Below is the output of testMcmc as of 2014-11-05
    let_ expr1 $ \x0 ->
    let_ expr2 $ \x1 ->
    lam $ \x2 ->
    normal x2 1 `bind` \x3 ->
    let_ (expr3 x0 x1 x2 x3) $ \x4 ->
    bern x4 `bind` \x5 ->
    dirac (if_ x5 x3 x2)

-- this should be equivalent to the above
testKernel2 :: (Lambda repr, Mochastic repr) => repr (HFun HReal (HMeasure HReal))
testKernel2 =
  lam $ \x2 ->
  normal x2 1 `bind` \x3 ->
  let_ (if_ (1 `less` exp_(-1/50*(x3-x2)*(x3+x2)))
            1
            (exp_(-1/50*(x3-x2)*(x3+x2)))) $ \x4 ->
 bern x4 `bind` \x5 ->
 dirac $ if_ x5 x3 x2

-- this comes from {Tests.Lazy,Examples.EasierRoadmap}.easierRoadmapProg1.  It is the
-- program post-disintegrate, as passed to Maple to simplify
rmProg1 :: (Lambda repr, Mochastic repr) => repr
    (HFun HUnit
    (HFun (HPair HReal HReal)
        (HMeasure (HPair HProb HProb))))
rmProg1 =
  lam $ \_ ->
  lam $ \x1 ->
  x1 `unpair` \x2 x3 ->
  weight 1 $
  weight 1 $
  superpose [(1,
            weight 1 $
            lebesgue `bind` \x4 ->
            superpose [(1,
                        weight 1 $
                        lebesgue `bind` \x5 ->
                        weight 1 $
                        lebesgue `bind` \x6 ->
                        weight (exp_ (-(x3 - x6) * (x3 - x6)
                                       * recip (fromProb (2 * exp_ (log_ (unsafeProb x5) * 2))))
                                * recip (unsafeProb x5)
                                * recip (exp_ (log_ (2 * pi_) * (1 / 2)))) $
                        weight 1 $
                        lebesgue `bind` \x7 ->
                        weight (exp_ (-(x6 - x7) * (x6 - x7)
                                       * recip (fromProb (2 * exp_ (log_ (unsafeProb x4) * 2))))
                                * recip (unsafeProb x4)
                                * recip (exp_ (log_ (2 * pi_) * (1 / 2)))) $
                        weight (exp_ (-(x2 - x7) * (x2 - x7)
                                       * recip (fromProb (2 * exp_ (log_ (unsafeProb x5) * 2))))
                                * recip (unsafeProb x5)
                                * recip (exp_ (log_ (2 * pi_) * (1 / 2)))) $
                        weight (exp_ (-x7 * x7
                                       * recip (fromProb (2 * exp_ (log_ (unsafeProb x4) * 2))))
                                * recip (unsafeProb x4)
                                * recip (exp_ (log_ (2 * pi_) * (1 / 2)))) $
                        weight (recip (unsafeProb 3)) $
                        superpose [(1,
                                    if_ (x5 `less` 4)
                                        (if_ (1 `less` x5)
                                             (weight (recip (unsafeProb 5)) $
                                              superpose [(1,
                                                          if_ (x4 `less` 8)
                                                              (if_ (3 `less` x4)
                                                                   (dirac (pair (unsafeProb x4)
                                                                                (unsafeProb x5)))
                                                                   (superpose []))
                                                              (superpose [])),
                                                         (1, superpose [])])
                                             (superpose []))
                                        (superpose [])),
                                   (1, superpose [])]),
                       (1, superpose [])]),
           (1, superpose [])]

-- this comes from Examples.EasierRoadmap.easierRoadmapProg4'.
rmProg4
    :: (Lambda repr, Mochastic repr)
    => repr
        (HFun (HPair HReal HReal)
        (HFun (HPair HProb HProb)
        (HMeasure (HPair (HPair HProb HProb) HProb))))
rmProg4 =
  lam $ \x0 ->
  let_ (lam $ \x1 ->
        (lam $ \x2 ->
         lam $ \x3 ->
         x3 `unpair` \x4 x5 ->
         let_ 1 $ \x6 ->
         let_ (let_ 1 $ \x7 ->
               let_ (let_ 1 $ \x8 ->
                     let_ (let_ 1 $ \x9 ->
                           let_ (let_ 1 $ \x10 ->
                                 let_ (let_ 1 $ \x11 ->
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
                                                   * exp_ ((x12 * x14 * (fromProb x4 * fromProb x4)
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
                                                           * (-1/2))
                                                   * exp_ (log_ (unsafeProb (exp (log (fromProb x4)
                                                                                  * 4)
                                                                             + exp (log (fromProb x5)
                                                                                    * 2)
                                                                               * exp (log (fromProb x4)
                                                                                      * 2)
                                                                               * 3
                                                                             + exp (log (fromProb x5)
                                                                                    * 4)))
                                                           * (-1/2))
                                                   * (1/10)) $ \x32 ->
                                             let_ (let_ (recip (unsafeProb 3)) $ \x33 ->
                                                   let_ (let_ 1 $ \x34 ->
                                                         let_ (if_ (fromProb x5 `less` 4)
                                                                   (if_ (1 `less` fromProb x5)
                                                                        (let_ (recip (unsafeProb 5)) $ \x35 ->
                                                                         let_ (let_ 1 $ \x36 ->
                                                                               let_ (if_ (fromProb x4
                                                                                          `less` 8)
                                                                                         (if_ (3
                                                                                               `less` fromProb x4)
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
                                                                                                     0
                                                                                                     + x37
                                                                                                       * (x38 `unpair` \_ x41 ->
                                                                                                          x41)
                                                                                                         `app` x39))
                                                                                              (pair (superpose [])
                                                                                                    (lam $ \x37 ->
                                                                                                     0)))
                                                                                         (pair (superpose [])
                                                                                               (lam $ \x37 ->
                                                                                                0))) $ \x37 ->
                                                                               let_ 1 $ \x38 ->
                                                                               let_ (pair (superpose [])
                                                                                          (lam $ \x39 ->
                                                                                           0)) $ \x39 ->
                                                                               pair (superpose [(x36,
                                                                                                 x37 `unpair` \x40 x41 ->
                                                                                                 x40),
                                                                                                (x38,
                                                                                                 x39 `unpair` \x40 x41 ->
                                                                                                 x40)])
                                                                                    (lam $ \x40 ->
                                                                                     0
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
                                                                               0
                                                                               + x35
                                                                                 * (x36 `unpair` \x38 x39 ->
                                                                                    x39)
                                                                                   `app` x37))
                                                                        (pair (superpose [])
                                                                              (lam $ \x35 -> 0)))
                                                                   (pair (superpose [])
                                                                         (lam $ \x35 -> 0))) $ \x35 ->
                                                         let_ 1 $ \x36 ->
                                                         let_ (pair (superpose [])
                                                                    (lam $ \x37 -> 0)) $ \x37 ->
                                                         pair (superpose [(x34,
                                                                           x35 `unpair` \x38 x39 ->
                                                                           x38),
                                                                          (x36,
                                                                           x37 `unpair` \x38 x39 ->
                                                                           x38)])
                                                              (lam $ \x38 ->
                                                               0
                                                               + x34
                                                                 * (x35 `unpair` \x39 x40 -> x40)
                                                                   `app` x38
                                                               + x36
                                                                 * (x37 `unpair` \x39 x40 -> x40)
                                                                   `app` x38)) $ \x34 ->
                                                   pair (weight x33 $ x34 `unpair` \x35 x36 -> x35)
                                                        (lam $ \x35 ->
                                                         0
                                                         + x33
                                                           * (x34 `unpair` \x36 x37 -> x37)
                                                             `app` x35)) $ \x33 ->
                                             pair (weight x32 $ x33 `unpair` \x34 x35 -> x34)
                                                  (lam $ \x34 ->
                                                   0
                                                   + x32
                                                     * (x33 `unpair` \x35 x36 -> x36)
                                                       `app` x34)) $ \x12 ->
                                       pair (weight x11 $ x12 `unpair` \x13 x14 -> x13)
                                            (lam $ \x13 ->
                                             0
                                             + x11
                                               * (x12 `unpair` \x14 x15 -> x15) `app` x13)) $ \x11 ->
                                 let_ 1 $ \x12 ->
                                 let_ (pair (superpose []) (lam $ \x13 -> 0)) $ \x13 ->
                                 pair (superpose [(x10, x11 `unpair` \x14 x15 -> x14),
                                                  (x12, x13 `unpair` \x14 x15 -> x14)])
                                      (lam $ \x14 ->
                                       0 + x10 * (x11 `unpair` \x15 x16 -> x16) `app` x14
                                       + x12 * (x13 `unpair` \x15 x16 -> x16) `app` x14)) $ \x10 ->
                           pair (weight x9 $ x10 `unpair` \x11 x12 -> x11)
                                (lam $ \x11 ->
                                 0 + x9 * (x10 `unpair` \x12 x13 -> x13) `app` x11)) $ \x9 ->
                     let_ 1 $ \x10 ->
                     let_ (pair (superpose []) (lam $ \x11 -> 0)) $ \x11 ->
                     pair (superpose [(x8, x9 `unpair` \x12 x13 -> x12),
                                      (x10, x11 `unpair` \x12 x13 -> x12)])
                          (lam $ \x12 ->
                           0 + x8 * (x9 `unpair` \x13 x14 -> x14) `app` x12
                           + x10 * (x11 `unpair` \x13 x14 -> x14) `app` x12)) $ \x8 ->
               pair (weight x7 $ x8 `unpair` \x9 x10 -> x9)
                    (lam $ \x9 ->
                     0 + x7 * (x8 `unpair` \x10 x11 -> x11) `app` x9)) $ \x7 ->
         pair (weight x6 $ x7 `unpair` \x8 x9 -> x8)
              (lam $ \x8 -> 0 + x6 * (x7 `unpair` \x9 x10 -> x10) `app` x8))
        `app` x0
        `app` x1 `unpair` \x2 x3 ->
        x3 `app` (lam $ \x4 -> 1)) $ \x1 ->
  lam $ \x2 ->
  (x2 `unpair` \x3 x4 ->
   superpose [(1 / 2,
               uniform 3 8 `bind` \x5 -> dirac (pair (unsafeProb x5) x4)),
              (1 / 2,
               uniform 1 4 `bind` \x5 ->
               dirac (pair x3 (unsafeProb x5)))]) `bind` \x3 ->
  dirac (pair x3 (x1 `app` x3 / x1 `app` x2))

-- this comes from Examples.Seismic.falseDetection
seismicFalseDetection
    :: (Mochastic repr)
    => repr (HPair HReal (HPair HReal (HPair HReal (HPair HReal (HPair HReal (HPair HProb (HPair HProb (HPair HProb (HPair HReal (HPair HReal (HPair HReal (HPair HProb (HPair HProb (HPair HReal HProb))))))))))))))
    -> repr (HMeasure (HPair HReal (HPair HReal (HPair HReal HProb))))
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
  uniform 0 3600 `bind` \x29 ->
  uniform 0 360 `bind` \x30 ->
  uniform (-23/500 * 180 + 107/10) (-23/500 * 0 + 107/10) `bind` \x31 ->
  (normal 0 1 `bind` \x32 -> normal 0 1 `bind` \x33 -> dirac (x27 + fromProb x28 * (x32 / x33))) `bind` \x32 ->
  dirac (pair x29 (pair x30 (pair x31 (exp_ x32))))

-- this comes from Examples.Seismic.trueDetection
seismicTrueDetection :: (Mochastic repr) =>
  repr (HPair HReal (HPair HReal (HPair HReal (HPair HReal (HPair HReal (HPair HProb (HPair HProb (HPair HProb (HPair HReal (HPair HReal (HPair HReal (HPair HProb (HPair HProb (HPair HReal HProb))))))))))))))
  -> repr (HPair HReal (HPair HReal (HPair HProb HReal)))
  -> repr (HMeasure (HEither HUnit (HPair HReal (HPair HReal (HPair HReal HProb)))))
seismicTrueDetection x0 x1 =
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
  superpose [(recip (1
                     + exp_ (-(x6 + x8 * fromProb x34
                               + x10
                                 * ((atan (sqrt ((cos (x32 * pi / 180) * sin ((x30 - x2) * pi / 180)) ** 2
                                                 + (cos (x4 * pi / 180) * sin (x32 * pi / 180) - sin (x4 * pi / 180) * cos (x32 * pi / 180) * cos ((x30 - x2) * pi / 180)) ** 2)
                                           / (sin (x4 * pi / 180) * sin (x32 * pi / 180) + cos (x4 * pi / 180) * cos (x32 * pi / 180) * cos ((x30 - x2) * pi / 180)))
                                     + if_ (sin (x4 * pi / 180) * sin (x32 * pi / 180) + cos (x4 * pi / 180) * cos (x32 * pi / 180) * cos ((x30 - x2) * pi / 180)
                                            `less` 0)
                                           pi
                                           0)
                                    * 180
                                    / pi)))),
              dirac true),
             (1
              - recip (1
                       + exp_ (-(x6 + x8 * fromProb x34
                                 + x10
                                   * ((atan (sqrt ((cos (x32 * pi / 180) * sin ((x30 - x2) * pi / 180)) ** 2
                                                   + (cos (x4 * pi / 180) * sin (x32 * pi / 180) - sin (x4 * pi / 180) * cos (x32 * pi / 180) * cos ((x30 - x2) * pi / 180)) ** 2)
                                             / (sin (x4 * pi / 180) * sin (x32 * pi / 180) + cos (x4 * pi / 180) * cos (x32 * pi / 180) * cos ((x30 - x2) * pi / 180)))
                                       + if_ (sin (x4 * pi / 180) * sin (x32 * pi / 180) + cos (x4 * pi / 180) * cos (x32 * pi / 180) * cos ((x30 - x2) * pi / 180)
                                              `less` 0)
                                             pi
                                             0)
                                      * 180
                                      / pi)))),
              dirac false)] `bind` \x36 ->
  if_ (if_ x36 false true)
      (dirac (inl unit))
      ((gamma 1 1 `bind` \x37 ->
        normal 0 1 `bind` \x38 ->
        dirac (x35
               + (-23/1000
                   * ((atan (sqrt ((cos (x32 * pi / 180) * sin ((x30 - x2) * pi / 180)) ** 2
                                   + (cos (x4 * pi / 180) * sin (x32 * pi / 180) - sin (x4 * pi / 180) * cos (x32 * pi / 180) * cos ((x30 - x2) * pi / 180)) ** 2)
                             / (sin (x4 * pi / 180) * sin (x32 * pi / 180) + cos (x4 * pi / 180) * cos (x32 * pi / 180) * cos ((x30 - x2) * pi / 180)))
                       + if_ (sin (x4 * pi / 180) * sin (x32 * pi / 180) + cos (x4 * pi / 180) * cos (x32 * pi / 180) * cos ((x30 - x2) * pi / 180)
                              `less` 0)
                             pi
                             0)
                      * 180
                      / pi)
                     ** 2
                  + 107/10
                    * ((atan (sqrt ((cos (x32 * pi / 180) * sin ((x30 - x2) * pi / 180)) ** 2
                                    + (cos (x4 * pi / 180) * sin (x32 * pi / 180) - sin (x4 * pi / 180) * cos (x32 * pi / 180) * cos ((x30 - x2) * pi / 180)) ** 2)
                              / (sin (x4 * pi / 180) * sin (x32 * pi / 180) + cos (x4 * pi / 180) * cos (x32 * pi / 180) * cos ((x30 - x2) * pi / 180)))
                        + if_ (sin (x4 * pi / 180) * sin (x32 * pi / 180) + cos (x4 * pi / 180) * cos (x32 * pi / 180) * cos ((x30 - x2) * pi / 180)
                               `less` 0)
                              pi
                              0)
                       * 180
                       / pi)
                  + 5)
               + x38 * fromProb (x12 * sqrt_ (2 * x37)))) `bind` \x37 ->
       if_ (3600 `less` x37)
           (dirac (inl unit))
           ((gamma 1 1 `bind` \x38 -> normal 0 1 `bind` \x39 -> dirac (0 + x39 * fromProb (x14 * sqrt_ (2 * x38)))) `bind` \x38 ->
            (counting `bind` \x39 ->
             if_ (if_ (if_ ((atan (sin ((x30 - x2) * pi / 180)
                                   / (cos (x4 * pi / 180) * tan (x32 * pi / 180) - sin (x4 * pi / 180) * cos ((x30 - x2) * pi / 180)))
                             + if_ (cos (x4 * pi / 180) * tan (x32 * pi / 180) - sin (x4 * pi / 180) * cos ((x30 - x2) * pi / 180) `less` 0)
                                   (if_ (sin ((x30 - x2) * pi / 180) `less` 0) (-pi) pi)
                                   0)
                            * 180
                            / pi
                            + x38
                            + 360 * fromInt x39
                            `less` 0)
                           false
                           true)
                      ((atan (sin ((x30 - x2) * pi / 180)
                              / (cos (x4 * pi / 180) * tan (x32 * pi / 180) - sin (x4 * pi / 180) * cos ((x30 - x2) * pi / 180)))
                        + if_ (cos (x4 * pi / 180) * tan (x32 * pi / 180) - sin (x4 * pi / 180) * cos ((x30 - x2) * pi / 180) `less` 0)
                              (if_ (sin ((x30 - x2) * pi / 180) `less` 0) (-pi) pi)
                              0)
                       * 180
                       / pi
                       + x38
                       + 360 * fromInt x39
                       `less` 360)
                      false)
                 (dirac ((atan (sin ((x30 - x2) * pi / 180)
                                / (cos (x4 * pi / 180) * tan (x32 * pi / 180) - sin (x4 * pi / 180) * cos ((x30 - x2) * pi / 180)))
                          + if_ (cos (x4 * pi / 180) * tan (x32 * pi / 180) - sin (x4 * pi / 180) * cos ((x30 - x2) * pi / 180) `less` 0)
                                (if_ (sin ((x30 - x2) * pi / 180) `less` 0) (-pi) pi)
                                0)
                         * 180
                         / pi
                         + x38
                         + 360 * fromInt x39))
                 (superpose [])) `bind` \x39 ->
            (gamma 1 1 `bind` \x40 ->
             normal 0 1 `bind` \x41 ->
             dirac (-23/500
                     * ((atan (sqrt ((cos (x32 * pi / 180) * sin ((x30 - x2) * pi / 180)) ** 2
                                     + (cos (x4 * pi / 180) * sin (x32 * pi / 180) - sin (x4 * pi / 180) * cos (x32 * pi / 180) * cos ((x30 - x2) * pi / 180)) ** 2)
                               / (sin (x4 * pi / 180) * sin (x32 * pi / 180) + cos (x4 * pi / 180) * cos (x32 * pi / 180) * cos ((x30 - x2) * pi / 180)))
                         + if_ (sin (x4 * pi / 180) * sin (x32 * pi / 180) + cos (x4 * pi / 180) * cos (x32 * pi / 180) * cos ((x30 - x2) * pi / 180)
                                `less` 0)
                               pi
                               0)
                        * 180
                        / pi)
                    + 107/10
                    + x41 * fromProb (x16 * sqrt_ (2 * x40)))) `bind` \x40 ->
            normal (x18 + x20 * fromProb x34
                    + x22
                      * ((atan (sqrt ((cos (x32 * pi / 180) * sin ((x30 - x2) * pi / 180)) ** 2
                                      + (cos (x4 * pi / 180) * sin (x32 * pi / 180) - sin (x4 * pi / 180) * cos (x32 * pi / 180) * cos ((x30 - x2) * pi / 180)) ** 2)
                                / (sin (x4 * pi / 180) * sin (x32 * pi / 180) + cos (x4 * pi / 180) * cos (x32 * pi / 180) * cos ((x30 - x2) * pi / 180)))
                          + if_ (sin (x4 * pi / 180) * sin (x32 * pi / 180) + cos (x4 * pi / 180) * cos (x32 * pi / 180) * cos ((x30 - x2) * pi / 180)
                                 `less` 0)
                                pi
                                0)
                         * 180
                         / pi))
                   x24 `bind` \x41 ->
            dirac (inr (pair x37 (pair x39 (pair x40 (exp_ x41)))))))


tdl :: (Lambda repr, Mochastic repr) => repr
    (HFun
        (HPair HReal
        (HPair HReal
        (HPair HReal
        (HPair HReal
        (HPair HReal
        (HPair HProb
        (HPair HProb
        (HPair HProb
        (HPair HReal
        (HPair HReal
        (HPair HReal
        (HPair HProb
        (HPair HProb
        (HPair HReal
        HProb))))))))))))))
    (HFun
        (HPair HReal
        (HPair HReal
        (HPair HProb
        HReal)))
    (HMeasure HUnit)))
tdl = lam $ \x0 -> lam $ \x1 -> 
  seismicTrueDetection x0 x1 `bind` \z -> 
  uneither z dirac (\_ -> superpose [])
tdr :: (Lambda repr, Mochastic repr) => repr
    (HFun
        (HPair HReal
        (HPair HReal
        (HPair HReal
        (HPair HReal
        (HPair HReal
        (HPair HProb
        (HPair HProb
        (HPair HProb
        (HPair HReal
        (HPair HReal
        (HPair HReal
        (HPair HProb
        (HPair HProb
        (HPair HReal
        HProb))))))))))))))
    (HFun
        (HPair HReal
        (HPair HReal
        (HPair HProb
        HReal)))
    (HMeasure (HPair HReal (HPair HReal (HPair HReal HProb))))))
tdr = lam $ \x0 -> lam $ \x1 -> 
  seismicTrueDetection x0 x1 `bind` \z -> 
  uneither z (\_ -> superpose []) dirac

-- from Examples/HMMContinuous.hs
kalman :: (Mochastic repr, Lambda repr) => repr
    (HFun
        (HPair HProb
        (HPair HProb
        (HPair HReal
        (HPair HReal
        (HPair HReal
        HProb)))))
    (HFun
        (HPair HProb
        (HPair HProb
        (HPair HReal
        (HPair HReal
        (HPair HReal
        HProb)))))
    (HFun HReal
    (HMeasure HReal))))
kalman = lam $ \m -> lam $ \n -> reflect m `bindo` reflect n
  where reflect m0 =
          unpair m0 $ \a m1 ->
          unpair m1 $ \b m2 ->
          unpair m2 $ \c m3 ->
          unpair m3 $ \d m4 ->
          unpair m4 $ \e f ->
          lam $ \s ->
          weight (a * exp_ (- fromProb b * (s - c) ** 2)) $
          normal (d * s + e) f

-- from a web question
-- these are mathematically equivalent, albeit at different types
chal1 :: (Mochastic repr, Lambda repr) => repr (HFun HProb (HFun HReal (HFun HReal (HFun HReal (HMeasure HBool)))))
chal1 = lam $ \sigma ->
        lam $ \a     ->
        lam $ \b     ->
        lam $ \c     ->
        normal a sigma `bind` \ya ->
        normal b sigma `bind` \yb ->
        normal c sigma `bind` \yc ->
        dirac (and_ [less_ yb ya, less_ yc ya])

chal2 :: (Mochastic repr, Lambda repr) => repr (HFun HProb (HFun HReal (HFun HReal (HFun HReal (HMeasure HReal)))))
chal2 = lam $ \sigma ->
        lam $ \a     ->
        lam $ \b     ->
        lam $ \c     ->
        normal a sigma `bind` \ya ->
        normal b sigma `bind` \yb ->
        normal c sigma `bind` \yc ->
        dirac (if_ (and_ [less_ yb ya, less_ yc ya]) 1 0)

chal3 :: (Lambda repr, Mochastic repr) => repr (HFun HProb (HMeasure HReal))
chal3 = lam $ \sigma -> app3 (app chal2 sigma) 0 0 0

seismic :: (Lambda repr, Mochastic repr, Integrate repr) => repr
    (HFun SE.HStation
    (HFun (HPair HReal (HPair HReal (HPair HProb HReal)))
    (HFun (HPair HReal (HPair HReal (HPair HReal HProb)))
    (HMeasure HProb))))
seismic = lam3 (\s e d -> dirac $ SE.densT s e d)

easyHMM
    :: (Mochastic repr)
    => repr (HMeasure (HPair (HPair HReal HReal) (HPair HProb HProb)))
easyHMM =
  gamma 3 1 `bind` \noiseT ->
  gamma 1 1 `bind` \noiseE ->
  normal  0 noiseT `bind` \x1 ->
  normal x1 noiseE `bind` \m1 ->
  normal x1 noiseT `bind` \x2 ->
  normal x2 noiseE `bind` \m2 ->
  dirac (pair (pair m1 m2) (pair noiseT noiseE))
