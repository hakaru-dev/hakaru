{-# LANGUAGE NoImplicitPrelude
           , DataKinds
           , TypeOperators
           , TypeFamilies
           , ScopedTypeVariables
           , FlexibleContexts
           , MultiParamTypeClasses
           , FunctionalDependencies
           , TypeSynonymInstances
           , GADTs
           , FlexibleInstances 
           , FlexibleContexts 
           , ConstraintKinds
           #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Tests.RoundTrip where

import           Prelude ((.), ($), asTypeOf, String, FilePath, Show(..), (++), Bool(..), concat)
import qualified Prelude 
import qualified Data.List.NonEmpty as L
import           Data.Ratio
import qualified Data.Text.Utf8 as IO 

import Language.Hakaru.Syntax.Prelude
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Pretty.Concrete (pretty)
import Language.Hakaru.Syntax.AST (Term, PrimOp(..))
import Language.Hakaru.Syntax.AST.Transforms
import Language.Hakaru.Syntax.ABT (ABT, TrivialABT(..))
import Language.Hakaru.Expect     (total)
import Language.Hakaru.Inference  (priorAsProposal, mcmc, mh)
import Language.Hakaru.Types.Sing
import System.IO 
import System.Directory 
import Control.Monad (mapM_, Monad(return))
import Data.Foldable (null)
import Data.List (intercalate) 

import qualified Data.Text as Text 
import Test.HUnit
import Tests.TestTools
import Tests.Models
    (uniform_0_1, normal_0_1, gamma_1_1,
     uniformC, normalC, beta_1_1, norm, unif2)
-- import Tests.Models (t4, t4')
unsafeSuperpose
    :: (ABT Term abt)
    => [(abt '[] 'HProb, abt '[] ('HMeasure a))]
    -> abt '[] ('HMeasure a)
unsafeSuperpose = superpose . L.fromList

testMeasureUnit :: Test
testMeasureUnit = test [
    "t1"      ~: testConcreteFiles "tests/RoundTrip/t1,t5.0.hk" "tests/RoundTrip/t1,t5.expected.hk", -- In Maple, should 'evaluate' to "\c -> 1/2*c(Unit)"
    "t5"      ~: testConcreteFiles "tests/RoundTrip/t1,t5.1.hk" "tests/RoundTrip/t1,t5.expected.hk", -- t5 is "the same" as t1.
    "t10"     ~: testConcreteFiles "tests/RoundTrip/t10.0.hk" "tests/RoundTrip/t10.expected.hk",
    "t11"     ~: testConcreteFiles "tests/RoundTrip/t11,t22.0.hk" "tests/RoundTrip/t11,t22.expected.hk",  
    "t12"     ~: testConcreteFilesMany [] "tests/RoundTrip/t12.hk",
    "t20"     ~: testConcreteFiles "tests/RoundTrip/t20.0.hk" "tests/RoundTrip/t20.expected.hk",
    "t22"     ~: testConcreteFiles "tests/RoundTrip/t11,t22.1.hk" "tests/RoundTrip/t11,t22.expected.hk",
    "t24"     ~: testConcreteFiles "tests/RoundTrip/t24.0.hk" "tests/RoundTrip/t24.expected.hk",
    "t25"     ~: testConcreteFiles "tests/RoundTrip/t25.0.hk" "tests/RoundTrip/t25.expected.hk",
    "t44Add"  ~: testConcreteFiles "tests/RoundTrip/t44Add.0.hk" "tests/RoundTrip/t44Add.expected.hk",
    "t44Mul"  ~: testConcreteFiles "tests/RoundTrip/t44Mul.0.hk" "tests/RoundTrip/t44Mul.expected.hk",
    "t53"     ~: testConcreteFiles "tests/RoundTrip/t53.0.hk" "tests/RoundTrip/t53.expected.hk",
    "t53'"    ~: testConcreteFiles "tests/RoundTrip/t53.1.hk" "tests/RoundTrip/t53.expected.hk",
    "t54"     ~: testConcreteFile "tests/RoundTrip/t54.hk",
    "t55"     ~: testConcreteFiles "tests/RoundTrip/t55.0.hk" "tests/RoundTrip/t55.expected.hk",
    "t56"     ~: testConcreteFiles "tests/RoundTrip/t56.0.hk" "tests/RoundTrip/t56.expected.hk",
    "t56'"    ~: testConcreteFiles "tests/RoundTrip/t56.1.hk" "tests/RoundTrip/t56.expected.hk",
    "t57"     ~: testConcreteFiles "tests/RoundTrip/t57.0.hk" "tests/RoundTrip/t57.expected.hk",
    "t58"     ~: testConcreteFiles "tests/RoundTrip/t58.0.hk" "tests/RoundTrip/t58.expected.hk",
    "t59"     ~: testConcreteFile "tests/RoundTrip/t59.hk",
    "t60"     ~: testConcreteFilesMany [ "tests/RoundTrip/t60.0.hk"
                                       , "tests/RoundTrip/t60.1.hk" ]
                                       "tests/RoundTrip/t60.expected.hk",
    "t62"     ~: testConcreteFiles "tests/RoundTrip/t62.0.hk" "tests/RoundTrip/t62.expected.hk", ---- "Special case" of t56
        "t63"     ~: testConcreteFiles "tests/RoundTrip/t63.0.hk" "tests/RoundTrip/t63.expected.hk", ---- "Scalar multiple" of t62
    "t64"     ~: testConcreteFiles "tests/RoundTrip/t64.0.hk" "tests/RoundTrip/t64.expected.hk", -- Density calculation for (Exp (Log StdRandom)) and StdRandom
    "t64'"    ~: testConcreteFiles "tests/RoundTrip/t64.1.hk" "tests/RoundTrip/t64.expected.hk", -- Density calculation for (Exp (Log StdRandom)) and StdRandom
    "t65"     ~: testConcreteFiles "tests/RoundTrip/t65.0.hk" "tests/RoundTrip/t65.expected.hk", -- Density calculation for (Add StdRandom (Exp (Neg StdRandom))); Maple can integrate this but we don't simplify it for some reason.
    "t77"     ~: testConcreteFilesMany [] "tests/RoundTrip/t77.hk" -- the (x * (-1)) below is an unfortunate artifact not worth fixing
    ]

testMeasureProb :: Test
testMeasureProb = test [
    "t2"    ~: testConcreteFiles "tests/RoundTrip/t2.0.hk" "tests/RoundTrip/t2.expected.hk",
    "t26"   ~: testConcreteFiles "tests/RoundTrip/t26.0.hk" "tests/RoundTrip/t26.expected.hk",
    "t30"   ~: testConcreteFilesMany [] "tests/RoundTrip/t30.hk",
    "t33"   ~: testConcreteFilesMany [] "tests/RoundTrip/t33.hk",
    "t34"   ~: testConcreteFiles "tests/RoundTrip/t34.0.hk" "tests/RoundTrip/t34.expected.hk",
    "t35"   ~: testConcreteFilesMany [] "tests/RoundTrip/t35.0.hk",
    "t35'"  ~: testConcreteFilesMany [] "tests/RoundTrip/t35.expected.hk",
    "t38"   ~: testConcreteFilesMany [] "tests/RoundTrip/t38.hk",
    "t42"   ~: testConcreteFiles "tests/RoundTrip/t42.0.hk" "tests/RoundTrip/t42.expected.hk",
    "t49"   ~: testConcreteFilesMany [] "tests/RoundTrip/t49.hk",
        "t61"   ~: testConcreteFiles "tests/RoundTrip/t61.0.hk" "tests/RoundTrip/t61.expected.hk",
    "t66"   ~: testConcreteFilesMany [] "tests/RoundTrip/t66.hk",
    "t67"   ~: testConcreteFilesMany [] "tests/RoundTrip/t67.hk",
    "t69x"  ~: testConcreteFiles "tests/RoundTrip/t69x.0.hk" "tests/RoundTrip/t69x.expected.hk",
    "t69y"  ~: testConcreteFiles "tests/RoundTrip/t69y.0.hk" "tests/RoundTrip/t69y.expected.hk"
    ]

-- t45, t46, t47 are all equivalent.
-- But t47 is worse than t45 and t46 because the importance weight generated by
-- t47 as a sampler varies between 0 and 1 whereas the importance weight generated
-- by t45 and t46 is always 1.  In general it's good to reduce weight variance.
testMeasureReal :: Test
testMeasureReal = test [ 
        "t3"                ~: testConcreteFilesMany [] "tests/RoundTrip/t3.hk",
    "t6"                ~: testConcreteFiles "tests/RoundTrip/t6.0.hk" "tests/RoundTrip/t6.expected.hk",
    "t7"                ~: testConcreteFiles "tests/RoundTrip/t7.0.hk" "tests/RoundTrip/t7.expected.hk",
    "t7n"               ~: testConcreteFiles "tests/RoundTrip/t7n.0.hk" "tests/RoundTrip/t7n.expected.hk",
    "t8'"               ~: testConcreteFiles "tests/RoundTrip/t8'.0.hk" "tests/RoundTrip/t8'.expected.hk", -- Normal is conjugate to normal
    "t9"                ~: testConcreteFiles "tests/RoundTrip/t9.0.hk" "tests/RoundTrip/t9.expected.hk",
    "t13"               ~: testConcreteFiles "tests/RoundTrip/t13.0.hk" "tests/RoundTrip/t13.expected.hk",
    "t14"               ~: testConcreteFiles "tests/RoundTrip/t14.0.hk" "tests/RoundTrip/t14.expected.hk",
    "t21"               ~: testConcreteFile "tests/RoundTrip/t21.hk",
    "t28"               ~: testConcreteFilesMany [] "tests/RoundTrip/t28.hk",
    "t31"               ~: testConcreteFilesMany [] "tests/RoundTrip/t31.hk",
    "t36"               ~: testConcreteFilesMany [] "tests/RoundTrip/t36.hk",
    "t37"               ~: testConcreteFilesMany [] "tests/RoundTrip/t37.hk",
    "t39"               ~: testConcreteFilesMany [] "tests/RoundTrip/t39.hk",
    "t40"               ~: testConcreteFilesMany [] "tests/RoundTrip/t40.hk",
    "t43"               ~: testConcreteFiles "tests/RoundTrip/t43.0.hk" "tests/RoundTrip/t43.expected.hk",
    "t43'"              ~: testConcreteFiles "tests/RoundTrip/t43.1.hk" "tests/RoundTrip/t43.expected.hk",
    "t45"               ~: testConcreteFiles "tests/RoundTrip/t45.1.hk" "tests/RoundTrip/t45.expected.hk",
    "t46"               ~: testConcreteFilesMany [] "tests/RoundTrip/t45.0.hk",
    "t50"               ~: testConcreteFile "tests/RoundTrip/t50.hk",
    "t51"               ~: testConcreteFile "tests/RoundTrip/t51.hk",
    "t68"               ~: testConcreteFile "tests/RoundTrip/t68.hk",
    "t68'"              ~: testConcreteFile "tests/RoundTrip/t68'.hk",
    "t70a"              ~: testConcreteFiles "tests/RoundTrip/t70a.0.hk" "tests/RoundTrip/t70a.expected.hk",
    "t71a"              ~: testConcreteFiles "tests/RoundTrip/t71a.0.hk" "tests/RoundTrip/t71a.expected.hk",
    "t72a"              ~: testConcreteFiles "tests/RoundTrip/t72a.0.hk" "tests/RoundTrip/t72a.expected.hk",
    "t73a"              ~: testConcreteFiles "tests/RoundTrip/t73a.0.hk" "tests/RoundTrip/t73a.expected.hk",
    "t74a"              ~: testConcreteFiles "tests/RoundTrip/t74a.0.hk" "tests/RoundTrip/t74a.expected.hk",
    "t70b"              ~: testConcreteFiles "tests/RoundTrip/t70b.0.hk" "tests/RoundTrip/t70b.expected.hk",
    "t71b"              ~: testConcreteFiles "tests/RoundTrip/t71b.0.hk" "tests/RoundTrip/t71b.expected.hk",
    "t72b"              ~: testConcreteFiles "tests/RoundTrip/t72b.0.hk" "tests/RoundTrip/t72b.expected.hk",
    "t73b"              ~: testConcreteFiles "tests/RoundTrip/t73b.0.hk" "tests/RoundTrip/t73b.expected.hk",
    "t74b"              ~: testConcreteFiles "tests/RoundTrip/t74b.0.hk" "tests/RoundTrip/t74b.expected.hk",
    "t70c"              ~: testConcreteFiles "tests/RoundTrip/t70c.0.hk" "tests/RoundTrip/t70c.expected.hk",
    "t71c"              ~: testConcreteFiles "tests/RoundTrip/t71c.0.hk" "tests/RoundTrip/t71c.expected.hk",
    "t72c"              ~: testConcreteFiles "tests/RoundTrip/t72c.0.hk" "tests/RoundTrip/t72c.expected.hk",
    "t73c"              ~: testConcreteFiles "tests/RoundTrip/t73c.0.hk" "tests/RoundTrip/t73c.expected.hk",
    "t74c"              ~: testConcreteFiles "tests/RoundTrip/t74c.0.hk" "tests/RoundTrip/t74c.expected.hk",
    "t70d"              ~: testConcreteFiles "tests/RoundTrip/t70d.0.hk" "tests/RoundTrip/t70d.expected.hk",
    "t71d"              ~: testConcreteFiles "tests/RoundTrip/t71d.0.hk" "tests/RoundTrip/t71d.expected.hk",
    "t72d"              ~: testConcreteFiles "tests/RoundTrip/t72d.0.hk" "tests/RoundTrip/t72d.expected.hk",
    "t73d"              ~: testConcreteFiles "tests/RoundTrip/t73d.0.hk" "tests/RoundTrip/t73d.expected.hk",
    "t74d"              ~: testConcreteFiles "tests/RoundTrip/t74d.0.hk" "tests/RoundTrip/t74d.expected.hk",
    "t76"               ~: testConcreteFile "tests/RoundTrip/t76.hk",
    "t78"               ~: testConcreteFiles "tests/RoundTrip/t78.0.hk" "tests/RoundTrip/t78.expected.hk",
    "t79"               ~: testConcreteFiles "tests/RoundTrip/t79.0.hk" "tests/RoundTrip/t79.expected.hk", -- what does this simplify to?
    "t80"               ~: testConcreteFile "tests/RoundTrip/t80.hk",
    "t81"               ~: testConcreteFilesMany [] "tests/RoundTrip/t81.hk",
    -- TODO "kalman"    ~: testConcreteFile "tests/RoundTrip/kalman.hk",
    -- TODO "seismic"         ~: testConcreteFilesMany [] "tests/RoundTrip/seismic.hk",
    "lebesgue1"         ~: testConcreteFiles
                              "tests/RoundTrip/lebesgue1.hk"
                              "tests/RoundTrip/lebesgue1.expected.hk",
    "lebesgue2"         ~: testConcreteFiles
                              "tests/RoundTrip/lebesgue2.hk"
                              "tests/RoundTrip/lebesgue2.expected.hk",
    "lebesgue3"         ~: testConcreteFiles "tests/RoundTrip/lebesgue3.0.hk" "tests/RoundTrip/lebesgue3.expected.hk",
    "testexponential"   ~: testConcreteFile "tests/RoundTrip/testexponential.hk", -- Testing round-tripping of some other distributions
    "testcauchy"        ~: testConcreteFile "tests/RoundTrip/testcauchy.hk",
    "exceptionLebesgue" ~: testConcreteFiles "tests/RoundTrip/exceptionLebesgue.0.hk" "tests/RoundTrip/exceptionLebesgue.expected.hk",
    "exceptionUniform"  ~: testConcreteFiles "tests/RoundTrip/exceptionUniform.0.hk" "tests/RoundTrip/exceptionUniform.expected.hk"
        -- TODO "two_coins" ~: testConcreteFile "tests/RoundTrip/two_coins.hk" -- needs support for lists
    ]

testMeasureNat :: Test 
testMeasureNat = test [ 
    "size" ~: testConcreteFiles "tests/RoundTrip/size.0.hk" "tests/RoundTrip/size.expected.hk"
    ]

testMeasureInt :: Test
testMeasureInt = test [ 
    "t75"                ~: testConcreteFile "tests/RoundTrip/t75.hk",
    "t75'"               ~: testConcreteFile "tests/RoundTrip/t75'.hk",
    "t83"                ~: testConcreteFiles "tests/RoundTrip/t83.0.hk" "tests/RoundTrip/t83.expected.hk",
    "exceptionCounting"  ~: testConcreteFilesMany [] "tests/RoundTrip/exceptionCounting.hk", -- Jacques wrote: "bug: [simp_pw_equal] implicitly assumes the ambient measure is Lebesgue"
    "exceptionSuperpose" ~: testConcreteFiles "tests/RoundTrip/exceptionSuperpose.0.hk" "tests/RoundTrip/exceptionSuperpose.expected.hk"
        ]

testMeasurePair :: Test 
testMeasurePair = test [
    "t4"                ~: testConcreteFiles "tests/RoundTrip/t4.0.hk" "tests/RoundTrip/t4.expected.hk",
    "t8"                ~: testConcreteFile "tests/RoundTrip/t8.hk", -- For sampling efficiency (to keep importance weights at or close to 1); t8 below should read back to uses of "normal", not uses of "lebesgue" then "weight".
    "t23"               ~: testConcreteFiles "tests/RoundTrip/t23.0.hk" "tests/RoundTrip/t23.expected.hk", -- was called bayesNet in Nov.06 msg by Ken for exact inference
    "t48"               ~: testConcreteFile "tests/RoundTrip/t48.hk",
    "t52"               ~: testConcreteFile "tests/RoundTrip/t52.hk", -- Example 1 from Chang & Pollard's Conditioning as Disintegration
    "dup"               ~: testConcreteFiles "tests/RoundTrip/dup.0.hk" "tests/RoundTrip/dup.expected.hk",
    "norm"              ~: testConcreteFile "tests/RoundTrip/norm.hk",
    "norm_nox"          ~: testConcreteFiles "tests/RoundTrip/norm_nox.0.hk" "tests/RoundTrip/norm_nox.expected.hk",
    "norm_noy"          ~: testConcreteFiles "tests/RoundTrip/norm_noy.0.hk" "tests/RoundTrip/norm_noy.expected.hk",
    "flipped_norm"      ~: testConcreteFiles "tests/RoundTrip/flipped_norm.0.hk" "tests/RoundTrip/flipped_norm.expected.hk",
    "priorProp"         ~: testConcreteFiles "tests/RoundTrip/priorProp.0.hk" "tests/RoundTrip/priorProp.expected.hk",
        "mhPriorProp"       ~: testConcreteFiles "tests/RoundTrip/mhPriorProp.0.hk" "tests/RoundTrip/mhPriorProp.expected.hk",
    "unif2"             ~: testConcreteFile "tests/RoundTrip/unif2.hk",
    "easyHMM"           ~: testConcreteFile "tests/RoundTrip/easyHMM.hk",
    "testMCMCPriorProp" ~: testConcreteFile "tests/RoundTrip/testMCMCPriorProp.hk"
    ]

testOther :: Test
testOther = test [
    "t82"              ~: testConcreteFiles "tests/RoundTrip/t82.0.hk" "tests/RoundTrip/t82.expected.hk",
    "testRoadmapProg1" ~: testConcreteFile "tests/RoundTrip/testRoadmapProg1.hk",
    "testKernel"       ~: testConcreteFiles "tests/RoundTrip/testKernel.0.hk" "tests/RoundTrip/testKernel.expected.hk",
    "gmm_gibbs"        ~: testConcreteFiles "tests/RoundTrip/gmm_gibbs.0.hk" "tests/RoundTrip/gmm_gibbs.expected.hk"
    --"testFalseDetection" ~: testStriv (lam seismicFalseDetection),
    --"testTrueDetection" ~: testStriv (lam2 seismicTrueDetection)
    --"testTrueDetectionL" ~: testStriv tdl,
    --"testTrueDetectionR" ~: testStriv tdr
    ]

allTests :: Test 
allTests = test
    [ testMeasureUnit
    , testMeasureProb
    , testMeasureReal
    , testMeasurePair
    , testMeasureNat
    , testMeasureInt
    , testOther
    ]

----------------------------------------------------------------

t46 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t46 = normal (real_ 4) (prob_ 5) >>= \x -> dirac (if_ (x < (real_ 3)) (x*x) (x-one))

t47 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t47 = unsafeSuperpose
    [ (one, normal (real_ 4) (prob_ 5) >>= \x -> if_ (x < (real_ 3)) (dirac (x*x)) (reject sing))
    , (one, normal (real_ 4) (prob_ 5) >>= \x -> if_ (x < (real_ 3)) (reject sing) (dirac (x-one)))
    ]

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
    unsafeSuperpose
        [(one,
            withWeight one $
            lebesgue >>= \x4 ->
            unsafeSuperpose
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
                    unsafeSuperpose
                        [(one,
                            if_ (x5 < (real_ 4))
                                (if_ (one < x5)
                                    (withWeight (recip (prob_ 5)) $
                                    unsafeSuperpose
                                        [(one,
                                            if_ (x4 < (real_ 8))
                                                (if_ ((real_ 3) < x4)
                                                    (dirac (pair (unsafeProb x4)
                                                        (unsafeProb x5)))
                                                    (reject sing))
                                                (reject sing))
                                        , (one, reject sing)])
                                    (reject sing))
                                (reject sing))
                , (one, reject sing)])
            , (one, reject sing)])
        , (one, reject sing)]

-- this comes from Examples.EasierRoadmap.easierRoadmapProg4'.
-- TODO: this needs to be regenerated from original program
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
                                                                                              (pair (reject sing)
                                                                                                    (lam $ \x37 ->
                                                                                                     zero)))
                                                                                         (pair (reject sing)
                                                                                               (lam $ \x37 ->
                                                                                                zero))) $ \x37 ->
                                                                               let_ one $ \x38 ->
                                                                               let_ (pair (reject sing)
                                                                                          (lam $ \x39 ->
                                                                                           zero)) $ \x39 ->
                                                                               pair (unsafeSuperpose [(x36,
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
                                                                        (pair (reject sing)
                                                                              (lam $ \x35 -> zero)))
                                                                   (pair (reject sing)
                                                                         (lam $ \x35 -> zero))) $ \x35 ->
                                                         let_ one $ \x36 ->
                                                         let_ (pair (reject sing)
                                                                    (lam $ \x37 -> zero)) $ \x37 ->
                                                         pair (unsafeSuperpose [(x34,
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
                                 let_ (pair (reject sing) (lam $ \x13 -> zero)) $ \x13 ->
                                 pair (unsafeSuperpose [(x10, x11 `unpair` \x14 x15 -> x14),
                                                  (x12, x13 `unpair` \x14 x15 -> x14)])
                                      (lam $ \x14 ->
                                       zero + x10 * (x11 `unpair` \x15 x16 -> x16) `app` x14
                                       + x12 * (x13 `unpair` \x15 x16 -> x16) `app` x14)) $ \x10 ->
                           pair (withWeight x9 $ x10 `unpair` \x11 x12 -> x11)
                                (lam $ \x11 ->
                                 zero + x9 * (x10 `unpair` \x12 x13 -> x13) `app` x11)) $ \x9 ->
                     let_ one $ \x10 ->
                     let_ (pair (reject sing) (lam $ \x11 -> zero)) $ \x11 ->
                     pair (unsafeSuperpose [(x8, x9 `unpair` \x12 x13 -> x12),
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
   unsafeSuperpose [(half,
               uniform (real_ 3) (real_ 8) >>= \x5 -> dirac (pair (unsafeProb x5) x4)),
              (half,
               uniform one (real_ 4) >>= \x5 ->
               dirac (pair x3 (unsafeProb x5)))]) >>= \x3 ->
  dirac (pair x3 (x1 `app` x3 / x1 `app` x2))


pairReject
    :: (ABT Term abt)
    => abt '[] (HPair ('HMeasure 'HReal) 'HReal)
pairReject =
    pair (reject (SMeasure SReal) >>= \_ -> dirac one)
         (real_ 2)

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
