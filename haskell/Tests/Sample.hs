{-# LANGUAGE DataKinds
           , GADTs
           , FlexibleContexts
           #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Tests.Sample where

import           Prelude                        hiding ((+))
import           GHC.Word (Word32)
import qualified Data.Vector as V

import           Language.Hakaru.Types.DataKind
import           Language.Hakaru.Syntax.Prelude
import           Language.Hakaru.Syntax.Value
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Sample

import           Tests.Models

import qualified System.Random.MWC as MWC
import           Test.HUnit

seed :: V.Vector Word32
seed = V.singleton 42

testMeasure :: String
          -> Value ('HMeasure a)
          -> Value 'HProb
          -> Value a
          -> Assertion
testMeasure p (VMeasure m) w v = do
  g <- MWC.initialize seed
  Just (v', w') <- m (VProb 1) g
  assertEqual p v' v
  assertEqual p w' w

testEvaluate :: (ABT Term abt)
             => String
             -> abt '[] a
             -> Value a
             -> Assertion
testEvaluate p prog = assertEqual p (runEvaluate prog)

normal01Value :: Value ('HMeasure 'HReal)
normal01Value = runEvaluate (triv normal_0_1)

allTests :: Test
allTests = test
   [ testMeasure "normal01" normal01Value (VProb 1) (VReal 0.35378756491616103)
   , testEvaluate "1+1" (triv $ real_ 1 + real_ 1) (VReal 2)
   ]
