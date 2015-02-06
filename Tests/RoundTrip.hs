{-# LANGUAGE TypeFamilies, Rank2Types, FlexibleContexts #-}
module Tests.RoundTrip (allTests) where

import Prelude hiding (Real)

import Language.Hakaru.Syntax
import Language.Hakaru.Disintegrate hiding (max_)
import Language.Hakaru.Expect (Expect(..), Expect', total, normalize)
-- import Language.Hakaru.Maple (Maple, runMaple)
-- import Language.Hakaru.Simplify (simplify)
-- import Language.Hakaru.PrettyPrint (runPrettyPrint)
-- import Text.PrettyPrint (text, (<>), ($$), nest, render)

import Test.HUnit
import Tests.TestTools

testMeasureUnit :: Test
testMeasureUnit = test [
    "t1,t5"   ~: testSS [t1,t5] (factor (1/2)),
    "t10"     ~: testSS [t10] (superpose []),
    "t11,t22" ~: testSS [t11,t22] (dirac unit),
    "t12"     ~: testSS [] t12,
    "t20"     ~: testSS [t20] (lam (\y -> factor (y*(1/2)))),
    "t24"     ~: testSS [t24] t24',
    "t25"     ~: testSS [t25] t25',
    "t44Add"  ~: testSS [t44Add] t44Add',
    "t44Mul"  ~: testSS [t44Mul] t44Mul',
    "t53"     ~: testSS [t53,t53'] t53'',
    "t54"     ~: testS t54,
    "t55"     ~: testSS [t55] t55',
    "t56"     ~: testSS [t56,t56'] t56'',
    "t57"     ~: testSS [t57] t57',
    "t58"     ~: testSS [t58] t58'
    ]

testMeasureProb :: Test
testMeasureProb = test [
    "t2"  ~: testSS [t2] (uniform 0 1 `bind` dirac . unsafeProb),
    "t26" ~: testSS [t26] (dirac (1/2)),
    "t30" ~: testSS [] t30,
    "t33" ~: testSS [] t33,
    "t34" ~: testSS [t34] (dirac 3),
    "t35" ~: testSS [t35] (lam (\x -> if_ (less x 4) (dirac 3) (dirac 5))),
    "t38" ~: testSS [] t38,
    "t42" ~: testSS [t42] (dirac 1),
    "t49" ~: testSS [] t49
    ]

testMeasureReal :: Test
testMeasureReal = test
  [ "t3"  ~: testSS [] t3
  , "t6"  ~: testSS [] t6
  , "t7"  ~: testSS [t7] t7'
  , "t7n" ~: testSS [t7n] t7n'
  , "t9"  ~: testSS [t9] (superpose [(2, uniform 3 7)])
  , "t13" ~: testSS [t13] t13'
  , "t14" ~: testSS [t14] t14'
  , "t21" ~: testS t21
  , "t27" ~: testSS t27 t27'
  , "t28" ~: testSS [] t28
  , "t29" ~: testSS [] t29
  , "t31" ~: testSS [] t31
  , "t32" ~: testSS [] t32
  , "t36" ~: testSS [] t36
  , "t37" ~: testSS [] t37
  , "t39" ~: testSS [] t39
  , "t40" ~: testSS [] t40
  , "t43" ~: testSS [t43, t43'] t43''
  , "t45" ~: testSS [t46,t47] t45
  , "t50" ~: testS t50
  , "t51" ~: testS t51
  , "testexponential" ~: testS testexponential
    -- "two_coins" ~: testS two_coins -- needs support for lists
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
                              (lam $ \x -> superpose [(1/2, normal 0 1         `bind` \y -> dirac (pair y (snd_ x))),
                                                      (1/2, normal 0 (sqrt_ 2) `bind` \y -> dirac (pair (fst_ x) y))]),
    "mhPriorProp"   ~: testSS [testMHPriorProp] testPriorProp',
    "unif2"         ~: testS unif2,
    "testGibbsPropUnif" ~: testS testGibbsPropUnif
--    "testMCMCPriorProp" ~: testS testMCMCPriorProp
    ]

testOther :: Test
testOther = test [
    "beta1"      ~: testSS [testBetaConj] (superpose [(1/2, beta 2 1)]),
    "beta2"      ~: testSS [testBetaConj'] (beta 2 1),
    "testGibbs0" ~: testSS [testGibbsProp0] (lam $ \x -> normal (x * (1/2))
                                                                (sqrt_ 2 * (1/2))),
    "testGibbs1" ~: testSS [testGibbsProp1] (lam $ \x -> normal (fst_ x) 1
                                             `bind` \y -> dirac (pair (fst_ x) y)),
    "testGibbs2" ~: testSS [testGibbsProp2] (lam $ \x -> normal ((snd_ x) * (1/2))
                                                                (sqrt_ 2 * (1/2))
                                             `bind` \y -> dirac (pair y (snd_ x))),
    "testKernel" ~: testSS [testKernel] testKernel2
    ]

allTests :: Test
allTests = test
  [ testMeasureUnit
  , testMeasureProb
  , testMeasureReal
  , testMeasurePair
  , testOther
  ]

-- In Maple, should 'evaluate' to "\c -> 1/2*c(Unit)"
t1 :: (Mochastic repr) => repr (Measure ())
t1 = uniform 0 1 `bind` \x -> factor (unsafeProb x)

t2 :: Mochastic repr => repr (Measure Prob)
t2 = beta 1 1

t3 :: Mochastic repr => repr (Measure Real)
t3 = normal 0 10

t4 :: Mochastic repr => repr (Measure (Prob, Bool))
t4 = beta 1 1 `bind` \bias -> bern bias `bind` \coin -> dirac (pair bias coin)

t4' :: Mochastic repr => repr (Measure (Prob, Bool))
t4' = (uniform  0 1) `bind` \x3 ->
      superpose [((unsafeProb x3)               ,(dirac (pair (unsafeProb x3) true))),
                 ((unsafeProb (1 + (x3 * (-1)))),(dirac (pair (unsafeProb x3) false)))]

-- testBetaConj is like t4, but we condition on the coin coming up true,
-- so a different sampling procedure for the bias is called for.
testBetaConj :: (Mochastic repr) => repr (Measure Prob)
testBetaConj = d unit true
  where d:_ = runDisintegrate (\env -> ununit env $ liftM swap_ t4)

testBetaConj' :: (Mochastic repr, Integrate repr, Lambda repr) => repr (Measure Prob)
testBetaConj' = normalize (d unit true)
  where d:_ = runDisintegrate (const $ liftM swap_ t4)

-- t5 is "the same" as t1.
t5 :: Mochastic repr => repr (Measure ())
t5 = factor (1/2) `bind_` dirac unit

t6 :: Mochastic repr => repr (Measure Real)
t6 = dirac 5

t7,t7', t7n,t7n' :: Mochastic repr => repr (Measure Real)
t7   = uniform 0 1 `bind` \x -> factor (unsafeProb (x+1)) `bind_` dirac (x*x)
t7'  = uniform 0 1 `bind` \x -> superpose [(unsafeProb (x+1), dirac (x*x))]
t7n  = uniform (-1) 0 `bind` \x -> factor (unsafeProb (x+1)) `bind_` dirac (x*x)
t7n' = uniform (-1) 0 `bind` \x -> superpose [(unsafeProb (x + 1), dirac (x*x))]

-- For sampling efficiency (to keep importance weights at or close to 1),
-- t8 below should read back to uses of "normal", not uses of "lebesgue"
-- then "factor".
t8 :: Mochastic repr => repr (Measure (Real, Real))
t8 = normal 0 10 `bind` \x -> normal x 20 `bind` \y -> dirac (pair x y)

t9 :: Mochastic repr => repr (Measure Real)
t9 = lebesgue `bind` \x -> factor (if_ (and_ [less 3 x, less x 7]) (1/2) 0) `bind_` dirac x

t10 :: Mochastic repr => repr (Measure ())
t10 = factor 0

t11 :: Mochastic repr => repr (Measure ())
t11 = factor 1

t12 :: Mochastic repr => repr (Measure ())
t12 = factor 2

t13,t13' :: Mochastic repr => repr (Measure Real)
t13 = bern (3/5) `bind` \b -> dirac (if_ b 37 42)
t13' = superpose [(3/5, dirac 37), (2/5, dirac 42)]

t14,t14' :: Mochastic repr => repr (Measure Real)
t14 = bern (3/5) `bind` \b ->
      if_ b t13 (bern (2/7) `bind` \b' ->
                 if_ b' (uniform 10 12) (uniform 14 16))
t14' = superpose [
                  (9/25, dirac 37),
                  (6/25, dirac 42),
                  (4/35, uniform 10 12),
                  (2/7, uniform 14 16)
                 ]

t20 :: (Lambda repr, Mochastic repr) => repr (Prob -> Measure ())
t20 = lam (\y -> uniform 0 1 `bind` \x -> factor (unsafeProb x * y))

t21 :: (Mochastic repr, Integrate repr, Lambda repr) =>
       repr (Real -> Measure Real)
t21 = mcmc (`normal` 1) (normal 0 5)

t22 :: Mochastic repr => repr (Measure ())
t22 = bern (1/2) `bind_` dirac unit

-- was called bayesNet in Nov.06 msg by Ken for exact inference
t23, t23' :: Mochastic repr => repr (Measure (Bool, Bool))
t23 = bern (1/2) `bind` \a ->
               bern (if_ a (9/10) (1/10)) `bind` \b ->
               bern (if_ a (9/10) (1/10)) `bind` \c ->
               dirac (pair b c)
t23' = superpose [(41/100, dirac (pair true true)),
                  ( 9/100, dirac (pair true false)),
                  ( 9/100, dirac (pair false true)),
                  (41/100, dirac (pair false false))]

t24,t24' :: (Mochastic repr, Lambda repr) => repr (Prob -> Measure ())
t24 = lam (\x ->
      uniform 0 1 `bind` \y ->
      uniform 0 1 `bind` \z ->
      factor (x * exp_ (cos y) * unsafeProb z))
t24' = lam (\x ->
      uniform 0 1 `bind` \y ->
      factor (x * exp_ (cos y) * (1/2)))

t25,t25' :: (Mochastic repr, Lambda repr) => repr (Prob -> Real -> Measure ())
t25 = lam (\x -> lam (\y ->
    uniform 0 1 `bind` \z ->
    factor (x * exp_ (cos y) * unsafeProb z)))
t25' = lam (\x -> lam (\y ->
    factor (x * exp_ (cos y) * (1/2))))

t26 :: (Mochastic repr, Lambda repr, Integrate repr) => repr (Measure Prob)
t26 = dirac (total t1)

t27 :: (Mochastic repr, Lambda repr) => [repr (Real -> Measure Real)]
t27 = map (\d -> lam (d unit)) $ runDisintegrate
  (\env -> ununit env $
    normal 0 1 `bind` \x ->
    normal x 1 `bind` \y ->
    dirac (pair y x))
t27' :: (Mochastic repr, Lambda repr) => repr (Real -> Measure Real)
t27' = lam (\y ->
  superpose [( recip (sqrt_ pi_) * exp_ (y * y * ((-1)/4)) * (1/2)
             , normal (y * (1/2)) ((sqrt_ 2) * (1/2)) )])

t28 :: Mochastic repr => repr (Measure Real)
t28 = uniform 0 1

t29 :: Mochastic repr => repr (Measure Real)
t29 = uniform 0 1 `bind` \x -> dirac (exp x)

t30 :: Mochastic repr => repr (Measure Prob)
t30 = uniform 0 1 `bind` \x -> dirac (exp_ x)

t31 :: Mochastic repr => repr (Measure Real)
t31 = uniform (-1) 1

t32 :: Mochastic repr => repr (Measure Real)
t32 = uniform (-1) 1 `bind` \x -> dirac (exp x)

t33 :: Mochastic repr => repr (Measure Prob)
t33 = uniform (-1) 1 `bind` \x -> dirac (exp_ x)

t34 :: Mochastic repr => repr (Measure Prob)
t34 = dirac (if_ (less (2 `asTypeOf` log_ 1) 4) 3 5)

t35 :: (Lambda repr, Mochastic repr) => repr (Real -> Measure Prob)
t35 = lam (\x -> dirac (if_ (less (x `asTypeOf` log_ 1) 4) 3 5))

t36 :: (Lambda repr, Mochastic repr) => repr (Real -> Measure Real)
t36 = lam (dirac . sqrt)

t37 :: (Lambda repr, Mochastic repr) => repr (Real -> Measure Real)
t37 = lam (dirac . recip)

t38 :: (Lambda repr, Mochastic repr) => repr (Prob -> Measure Prob)
t38 = lam (dirac . recip)

t39 :: (Lambda repr, Mochastic repr) => repr (Real -> Measure Real)
t39 = lam (dirac . log)

t40 :: (Lambda repr, Mochastic repr) => repr (Prob -> Measure Real)
t40 = lam (dirac . log_)

-- this is not plugged in as it requires dealing with first-class functions,
-- which is not implemented
t41 :: (Lambda repr, Integrate repr, Mochastic repr) => repr (Measure ((Prob -> Prob) -> Prob))
t41 = dirac $ snd_ $ unExpect $ uniform 0 2 `bind` dirac . unsafeProb

t42 :: (Lambda repr, Integrate repr, Mochastic repr) => repr (Measure Prob)
t42 = dirac $ total $ uniform 0 2 `bind` dirac . unsafeProb

t43, t43', t43'' :: (Lambda repr, Mochastic repr) => repr (Bool -> Measure Real)
t43   = lam $ \b -> if_ b (uniform 0 1) (beta 1 1 `bind` dirac . fromProb)
t43'  = lam $ \b -> if_ b (uniform 0 1) (uniform 0 1)
t43'' = lam $ \_ -> uniform 0 1

t44Add, t44Add', t44Mul, t44Mul' :: (Lambda repr, Mochastic repr) => repr (Real -> Real -> Measure ())
t44Add  = lam $ \x -> lam $ \y -> factor (unsafeProb (x * x) + unsafeProb (y * y))
t44Add' = lam $ \x -> lam $ \y -> factor (unsafeProb (x ** 2 + y ** 2))
t44Mul  = lam $ \x -> lam $ \y -> factor (unsafeProb (x * x * y * y))
t44Mul' = lam $ \x -> lam $ \y -> factor (unsafeProb (x ** 2) * unsafeProb (y ** 2))

-- t45, t46, t47 are all equivalent. Which one is best?
t45 :: (Mochastic repr) => repr (Measure Real)
t45 = normal 4 5 `bind` \x -> if_ (less x 3) (dirac (x*x)) (dirac (x-1))

t46 :: (Mochastic repr) => repr (Measure Real)
t46 = normal 4 5 `bind` \x -> dirac (if_ (less x 3) (x*x) (x-1))

t47 :: (Mochastic repr) => repr (Measure Real)
t47 =
  superpose [(1, (normal 4 5 `bind` \x -> if_ (less x 3) (dirac (x*x)) (dirac 0))),
             (1, (normal 4 5 `bind` \x -> if_ (less x 3) (dirac 0) (dirac (x-1))))]

t48 :: (Mochastic repr, Lambda repr) => repr ((Real, Real) -> (Measure Real))
t48 = lam (\x -> uniform (-5) 7 `bind` \w -> dirac ((fst_ x + snd_ x) * w))

t49 :: (Mochastic repr) => repr (Measure Prob)
t49 = gamma 0.01 0.35

t50 :: (Mochastic repr) => repr (Measure Real)
t50 = uniform 1 3 `bind` \x ->
      normal 1 (unsafeProb x)

t51 :: (Mochastic repr) => repr (Measure Real)
t51 = uniform (-1) 1 `bind` \x ->
      normal x 1

-- Example 1 from Chang & Pollard's Conditioning as Disintegration
t52, t52' :: (Mochastic repr) => repr (Measure (Real, (Real, Real)))
t52 = uniform 0 1 `bind` \x ->
      uniform 0 1 `bind` \y ->
      dirac (pair (max_ x y)
                  (pair x y))
t52' = uniform 0 1 `bind` \x2 ->
       superpose [((unsafeProb (1 + (x2 * (-1)))),(uniform  x2 1) `bind` \x4 -> (dirac (pair x4 (pair x2 x4)))),
                  ((unsafeProb x2),(uniform  0 x2) `bind` \x4 -> (dirac (pair x2 (pair x2 x4))))]

t53, t53', t53'' :: (Mochastic repr, Lambda repr) => repr (Real -> Measure ())
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

t54 :: (Mochastic repr, Lambda repr) => repr (Real -> Measure ())
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
     factor (unsafeProb x2)) `bind` \x2 ->
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

t55, t55' :: (Mochastic repr, Lambda repr) => repr (Real -> Measure ())
t55  = lam $ \t -> uniform 0 1 `bind` \x ->
                   if_ (less x t) (dirac unit) $
                   superpose []
t55' = lam $ \t -> if_ (less 1 t) (dirac unit) $
                   if_ (less 0 t) (factor (unsafeProb t)) $
                   superpose []

t56, t56', t56'' :: (Mochastic repr, Lambda repr) => repr (Real -> Measure ())
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
    if_ (less t 0) (superpose []) $
    if_ (less t 1) (factor (unsafeProb t)) $
    if_ (less t 2) (factor (unsafeProb (2+t*(-1)))) $
    superpose []

t57, t57' :: (Mochastic repr, Lambda repr) => repr (Real -> Measure ())
t57 = lam $ \t -> superpose
  [(1, if_ (less t 1) (dirac unit) (superpose [])),
   (1, if_ (less 0 t) (dirac unit) (superpose []))]
t57' = lam $ \t -> if_ (t `less` 1)
                       (if_ (0 `less` t) (weight 2 (dirac unit)) (dirac unit))
                       (dirac unit)

t58, t58' :: (Mochastic repr, Lambda repr) => repr (Real -> Measure ())
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

-- Testing round-tripping of some other distributions
testexponential :: Mochastic repr => repr (Measure Prob)
testexponential = exponential (1/3)

testCauchy :: Mochastic repr => repr (Measure Real)
testCauchy = cauchy 5 3

-- And now some actual ML-related tests
priorAsProposal :: Mochastic repr => repr (Measure (a,b)) -> repr (a,b) -> repr (Measure (a,b))
priorAsProposal p x = bern (1/2) `bind` \c ->
                      p `bind` \x' ->
                      dirac (if_ c
                             (pair (fst_ x ) (snd_ x'))
                             (pair (fst_ x') (snd_ x )))

gibbsProposal :: (Order_ a, Expect' a ~ a, Expect' b ~ b,
                  Mochastic repr, Integrate repr, Lambda repr) =>
                 Disintegrate (Measure (a,b)) ->
                 repr (a, b) -> repr (Measure (a, b))
gibbsProposal p x = q (fst_ x) `bind` \x' -> dirac (pair (fst_ x) x')
  where d:_ = runDisintegrate (const p)
        q x = normalize (d unit (Expect x))

testGibbsProp0 :: (Lambda repr, Mochastic repr, Integrate repr) =>
                  repr (Real -> Measure Real)
testGibbsProp0 = lam $ \x -> normalize (d unit (Expect x))
  where d:_ = runDisintegrate (const flipped_norm)

onFst :: (Lambda repr) => (t -> repr a -> repr b) -> t -> repr (a -> b)
onFst tr f = lam (tr f)

onSnd :: (Mochastic repr, Mochastic repr1, Lambda repr) =>
               (repr1 (Measure (b1, a1))
                -> repr (b2, a2) -> repr (Measure (a, b)))
               -> repr1 (Measure (a1, b1)) -> repr ((a2, b2) -> Measure (b, a))
onSnd tr f = lam (liftM swap_ . tr (liftM swap_ f) . swap_)

testGibbsProp1 :: (Lambda repr, Mochastic repr, Integrate repr) =>
                  repr ((Real, Real) -> Measure (Real, Real))
-- testGibbsProp1 = lam (gibbsProposal norm)
testGibbsProp1 = onFst gibbsProposal norm

testGibbsProp2 :: (Lambda repr, Mochastic repr, Integrate repr) =>
                  repr ((Real, Real) -> Measure (Real, Real))
-- testGibbsProp2 = lam (liftM swap_ . gibbsProposal (liftM swap_ norm) . swap_)
testGibbsProp2 = onSnd gibbsProposal norm

testGibbsPropUnif :: (Lambda repr, Mochastic repr, Integrate repr) =>
                  repr (Real -> Measure Real)
testGibbsPropUnif = lam $ \x -> normalize (d unit (Expect x))
  where d:_ = runDisintegrate (const (liftM swap_ unif2))

mh :: (Mochastic repr, Integrate repr, Lambda repr,
       a ~ Expect' a, Order_ a) =>
      (forall repr'. (Mochastic repr') => repr' a -> repr' (Measure a)) ->
      (forall repr'. (Mochastic repr') => repr' (Measure a)) ->
      repr (a -> Measure (a, Prob))
mh proposal target =
  let_ (lam (d unit)) $ \mu ->
  lam $ \old ->
    proposal old `bind` \new ->
    dirac (pair new (mu `app` pair new old / mu `app` pair old new))
  where d:_ = density (\dummy -> ununit dummy $ bindx target proposal)

mcmc :: (Mochastic repr, Integrate repr, Lambda repr,
         a ~ Expect' a, Order_ a) =>
        (forall repr'. (Mochastic repr') => repr' a -> repr' (Measure a)) ->
        (forall repr'. (Mochastic repr') => repr' (Measure a)) ->
        repr (a -> Measure a)
mcmc proposal target =
  let_ (mh proposal target) $ \f ->
  lam $ \old ->
    app f old `bind` \new_ratio ->
    unpair new_ratio $ \new ratio ->
    bern (min_ 1 ratio) `bind` \accept ->
    dirac (if_ accept new old)

testMCMCPriorProp :: (Integrate repr, Mochastic repr, Lambda repr) =>
                 repr ((Real, Real) -> Measure (Real, Real))
testMCMCPriorProp = mcmc (priorAsProposal norm) norm

testMHPriorProp :: (Integrate repr, Mochastic repr, Lambda repr) =>
                 repr ((Real, Real) -> Measure ((Real, Real), Prob))
testMHPriorProp = mh (priorAsProposal norm) norm

testPriorProp' :: (Integrate repr, Mochastic repr, Lambda repr) =>
                 repr ((Real, Real) -> Measure ((Real, Real), Prob))
testPriorProp' =
      (lam $ \old ->
       superpose [(1 / 2,
                   normal 0 1 `bind` \x1 ->
                   dirac (pair (pair x1 (snd_ old))
                               (exp_ ((x1 * (-1) + fst_ old)
                                      * (fst_ old + snd_ old * (-2) + x1)
                                      * (1 / 2))))),
                  (1 / 2,
                   normal 0 (sqrt_ 2) `bind` \x1 ->
                   dirac (pair (pair (fst_ old) x1)
                               (exp_ ((x1 * (-1) + snd_ old)
                                      * (snd_ old * (-1) + fst_ old * 4 + x1 * (-1))
                                      * ((-1) / 4)))))])

dup :: (Lambda repr, Mochastic repr) => repr (Measure a) -> repr (Measure (a,a))
dup m = let_ m (\m' -> liftM2 pair m' m')

norm :: Mochastic repr => repr (Measure (Real, Real))
norm = normal 0 1 `bind` \x ->
       normal x 1 `bind` \y ->
       dirac (pair x y)

norm_nox :: Mochastic repr => repr (Measure Real)
norm_nox = normal 0 1 `bind` \x ->
           normal x 1 `bind` \y ->
           dirac y

norm_noy :: Mochastic repr => repr (Measure Real)
norm_noy = normal 0 1 `bind` \x ->
           normal x 1 `bind` \y ->
           dirac x

flipped_norm :: Mochastic repr => repr (Measure (Real, Real))
flipped_norm = normal 0 1 `bind` \x ->
               normal x 1 `bind` \y ->
               dirac (pair y x)

unif2 :: Mochastic repr => repr (Measure (Real, Real))
unif2 = uniform (-1) 1 `bind` \x ->
        uniform (x-1) (x+1) `bind` \y ->
        dirac (pair x y)

two_coins :: (Mochastic repr, Lambda repr) => repr (Measure [Real])
two_coins = bern (1/2) `bind` \x ->
            dirac $ (if_ x
                     (cons 1 nil)
                     (cons 1 (cons 2 nil)))

-- pull out some of the intermediate expressions for independent study
expr1 :: (Lambda repr, Mochastic repr) => repr (Real -> Prob)
expr1 =  (lam $ \x0 ->
          (lam $ \x1 ->
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
                 `app` (lam $ \x6 ->
                        (lam $ \x7 ->
                         (lam $ \x8 -> x8 `app` x2)
                         `app` (lam $ \x8 ->
                                (lam $ \x9 ->
                                 (lam $ \x10 -> x10 `app` unit)
                                 `app` (lam $ \x10 ->
                                        (lam $ \x11 ->
                                         (lam $ \x12 -> x12 `app` x2)
                                         `app` (lam $ \x12 ->
                                                (lam $ \x13 -> x13 `app` pair x2 x10) `app` x11))
                                        `app` x9))
                                `app` x7))
                        `app` x5))
                `app` x4)
           `app` (lam $ \x4 ->
                  (lam $ \x5 -> x5 `app` (x4 `unpair` \x6 x7 -> x7)) `app` x3))
          `app` unit
          `app` x0
          `app` (lam $ \x1 -> 1))

expr2 :: (Mochastic repr, Lambda repr) => repr (Real -> Real -> Prob)
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
                 `app` (lam $ \x8 ->
                        (lam $ \x9 ->
                         (lam $ \x10 -> x10 `app` x4)
                         `app` (lam $ \x10 ->
                                (lam $ \x11 ->
                                 (lam $ \x12 -> x12 `app` unit)
                                 `app` (lam $ \x12 ->
                                        (lam $ \x13 ->
                                         (lam $ \x14 -> x14 `app` x4)
                                         `app` (lam $ \x14 ->
                                                (lam $ \x15 -> x15 `app` pair x4 x12) `app` x13))
                                        `app` x11))
                                `app` x9))
                        `app` x7))
                `app` x6)
           `app` (lam $ \x6 ->
                  (lam $ \x7 -> x7 `app` (x6 `unpair` \x8 x9 -> x9)) `app` x5))
          `app` x1
          `app` x2
          `app` (lam $ \x3 -> 1))

-- the one we need in testKernel
expr3 :: (Mochastic repr, Lambda repr) => repr (d -> Prob) -> repr (d -> d -> Prob) -> repr d -> repr d -> repr Prob
expr3 x0 x1 x2 x3 = (if_ (1
                    `less` x0 `app` x3 / x1 `app` x2 `app` x3 * x1 `app` x3 `app` x2
                           / x0 `app` x2)
                   1
                   (x0 `app` x3 / x1 `app` x2 `app` x3 * x1 `app` x3 `app` x2
                    / x0 `app` x2))

-- testKernel :: Sample IO (Real -> Measure Real)
testKernel :: (Lambda repr, Mochastic repr) => repr (Real -> Measure Real)
testKernel =
-- Below is the output of testMcmc as of 2014-11-05
    let_ expr1 $ \x0 ->
    let_ expr2 $ \x1 ->
    lam $ \x2 ->
    normal x2 1 `bind` \x3 ->
    let_ (expr3 x0 x1 x2 x3) $ \x4 ->
    categorical [(x4, inl unit), (1 - x4, inr unit)] `bind` \x5 ->
    dirac (uneither x5 (\x6 -> x3) (\x6 -> x2))

-- this should be equivalent to the above
testKernel2 :: (Lambda repr, Mochastic repr) => repr (Real -> Measure Real)
testKernel2 =
  lam $ \x2 ->
  normal x2 1 `bind` \x3 ->
  let_ (if_ (1 `less` exp_(-1/50*(x3-x2)*(x3+x2)))
            1
            (exp_(-1/50*(x3-x2)*(x3+x2)))) $ \x4 ->
 categorical [(x4, x3), (1 - x4, x2)]
