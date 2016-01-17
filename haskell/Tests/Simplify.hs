{-# LANGUAGE OverloadedStrings
           , DataKinds
           , FlexibleContexts
           #-}

module Tests.Simplify where

import Prelude hiding ((>>=))

import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Prelude
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

realpair :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
realpair = ann_ (SMeasure $ sPair SReal SReal)
                (dirac (pair (real_ 1) (real_ 2)))

unifprob, unifprob' :: TrivialABT Term '[] ('HMeasure 'HProb)
unifprob = uniform (real_ 1) (real_ 2) >>= \x -> dirac (unsafeProb x)
unifprob' = uniform 
  (coerceTo_ (CCons (Signed HRing_Int) (CCons (Continuous HContinuous_Real) CNil)) (nat_ 1)) 
  (coerceTo_ (CCons (Signed HRing_Int) (CCons (Continuous HContinuous_Real) CNil)) (nat_ 2)) >>=
  \x -> dirac (unsafeProb x)

true' :: TrivialABT Term '[] HBool
true' = true

testSimplify :: ( ABT Term abt
                , Show (abt '[] a)
                , Eq   (abt '[] a))
               => String -> abt '[] a -> abt '[] a -> Assertion
testSimplify nm x y = do
  x' <- simplify x
  assertEqual nm y x' 

allTests :: Test
allTests = test
   [ testSimplify "freevar" freevar freevar
   , testSimplify "normal01T" normal01T normal01T
   , testSimplify "realpair" realpair realpair
   , testSimplify "unifprob" unifprob unifprob'
   , testSimplify "true'" true' true'
   ]
