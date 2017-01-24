{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE EmptyCase                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}

module Tests.ASTTransforms (allTests) where

import           Control.Monad
import qualified Data.Number.LogFloat             as LF
import qualified Data.Vector                      as V
import           GHC.Word                         (Word32)
import           Language.Hakaru.Sample           (runEvaluate)
import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.ANF       (normalize)
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.AST.Eq    (alphaEq)
import           Language.Hakaru.Syntax.Datum
import           Language.Hakaru.Syntax.DatumCase
import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Syntax.Prelude
import           Language.Hakaru.Syntax.Value
import           Language.Hakaru.Syntax.Variable
import           Language.Hakaru.Types.Coercion
import           Language.Hakaru.Types.DataKind
import           Language.Hakaru.Types.HClasses
import           Language.Hakaru.Types.Sing
import           Prelude                          hiding (product, (*), (+),
                                                   (-), (==))

import qualified System.Random.MWC                as MWC
import           Test.HUnit
import           Tests.Disintegrate               hiding (allTests)
import           Tests.TestTools

checkMeasure :: String
             -> Value ('HMeasure a)
             -> Value ('HMeasure a)
             -> Assertion
checkMeasure p (VMeasure m1) (VMeasure m2) = do
  -- Generate 2 copies of the same random seed so that
  g1 <- MWC.createSystemRandom
  s  <- MWC.save g1
  g2 <- MWC.restore s
  forM_ [1 :: Int .. 100] $ \_ -> do
      p1 <- LF.logFloat `fmap` MWC.uniform g1
      p2 <- LF.logFloat `fmap` MWC.uniform g2
      Just (v1, w1) <- m1 (VProb p1) g1
      Just (v2, w2) <- m2 (VProb p2) g2
      assertEqual p v1 v2
      assertEqual p w1 w2

allTests :: Test
allTests = test [ "example1" ~: testNormalizer "example1" example1 example1'
                , "example2" ~: testNormalizer "example2" example2 example2'
                , "example3" ~: testNormalizer "example3" example3 example3'

                -- Test some deterministic results
                , "runExample1" ~: testPreservesResult "example1" example1
                , "runExample2" ~: testPreservesResult "example2" example2
                , "runExample3" ~: testPreservesResult "example3" example3

                -- Test some programs which produce measures, these are
                -- statistical tests
                , "norm1a"      ~: testPreservesMeasure "norm1a" norm1a
                , "norm2"       ~: testPreservesMeasure "norm2" norm2
                ]

example1 :: TrivialABT Term '[] 'HReal
example1 = if_ (real_ 1 == real_ 2)
               (real_ 2 + real_ 3)
               (real_ 3 + real_ 4)

example1' :: TrivialABT Term '[] 'HReal
example1' = let_ (real_ 1 == real_ 2) $ \v ->
            if_ v (real_ 2 + real_ 3)
                  (real_ 3 + real_ 4)

example2 :: TrivialABT Term '[] 'HNat
example2 = let_ (nat_ 1) $ \ a -> triv ((summate a (a + (nat_ 10)) (\i -> i)) +
                                        (product a (a + (nat_ 10)) (\i -> i)))

example2' :: TrivialABT Term '[] 'HNat
example2' = let_ (nat_ 1) $ \ x4 ->
            let_ (x4 + nat_ 10) $ \ x3 ->
            let_ (summate x4 x3 (\ x0 -> x0)) $ \ x2 ->
            let_ (x4 + nat_ 10) $ \ x1 ->
            let_ (product x4 x1 (\ x0 -> x0)) $ \ x0 ->
            x2 + x0

example3 :: TrivialABT Term '[] 'HReal
example3 = triv (real_ 1 * (real_ 2 + real_ 3) * (real_ 4 + (real_ 5 + (real_ 6 * real_ 7))))


example3' :: TrivialABT Term '[] 'HReal
example3' = let_ (real_ 2 + real_ 3) $ \ x2 ->
            let_ (real_ 6 * real_ 7) $ \ x1 ->
            let_ (real_ 4 + real_ 5 + x1) $ \ x0 ->
            real_ 1 * x2 * x0

testNormalizer :: (ABT Term abt) => String -> abt '[] a -> abt '[] a -> Assertion
testNormalizer name a b = assertBool name (alphaEq (normalize a) b)

testPreservesResult
  :: forall (a :: Hakaru) abt . (ABT Term abt)
  => String
  -> abt '[] a
  -> Assertion
testPreservesResult name ast = assertEqual name result1 result2
  where result1 = runEvaluate ast
        result2 = runEvaluate (normalize ast)

testPreservesMeasure
  :: forall (a :: Hakaru) abt . (ABT Term abt)
  => String
  -> abt '[] ('HMeasure a)
  -> Assertion
testPreservesMeasure name ast = checkMeasure name result1 result2
  where result1 = runEvaluate ast
        result2 = runEvaluate (normalize ast)

