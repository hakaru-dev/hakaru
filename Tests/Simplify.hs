{-# LANGUAGE OverloadedStrings
           , DataKinds
           , FlexibleContexts
           #-}

module Tests.Simplify where

import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Variable
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Simplify

import Language.Hakaru.Syntax.AST.Eq()

import Test.HUnit

x :: (ABT AST abt) => abt '[] 'HNat
x = var (Variable "x" 0 SNat)

freevar :: TrivialABT AST '[] 'HNat
freevar = x

normal01T :: TrivialABT AST '[] ('HMeasure 'HReal)
normal01T = syn (MeasureOp_ Normal
                 :$ (syn $ Literal_ $ LReal 0)
                 :* (syn $ Literal_ $ LProb 1)
                 :* End)

testSimplify :: ( ABT AST abt
                , Show (abt '[] a)
                , Eq   (abt '[] a))
               => abt '[] a -> abt '[] a -> Assertion
testSimplify x y = do
  x' <- simplify x
  assertEqual "" x' y 

allTests :: Test
allTests = test
   [ testSimplify freevar freevar
   --, testSimplify normal01T normal01T
   ]
