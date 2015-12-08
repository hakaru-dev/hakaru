{-# LANGUAGE OverloadedStrings
           , DataKinds
           , FlexibleContexts
           #-}

module Tests.Simplify where

import Language.Hakaru.Syntax.HClasses
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Coercion
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Simplify

import Language.Hakaru.Syntax.AST.Eq()

import Test.HUnit

v :: (ABT Term abt) => abt '[] 'HNat
v = var (Variable "x" 0 SNat)

freevar :: TrivialABT Term '[] 'HNat
freevar = v

normal01T :: TrivialABT Term '[] ('HMeasure 'HReal)
normal01T = syn (MeasureOp_ Normal
                 :$ syn (CoerceTo_ (CCons (Continuous HContinuous_Real) CNil) :$
                           (syn (Literal_ (LInt (-2))) :* End))
                 :* syn (CoerceTo_ (CCons (Continuous HContinuous_Prob) CNil) :$
                           (syn (Literal_ (LNat 1)) :* End))
                 :* End)

testSimplify :: ( ABT Term abt
                , Show (abt '[] a)
                , Eq   (abt '[] a))
               => abt '[] a -> abt '[] a -> Assertion
testSimplify x y = do
  x' <- simplify x
  assertEqual "" x' y 

allTests :: Test
allTests = test
   [ testSimplify freevar freevar
   , testSimplify normal01T normal01T
   ]
