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
import Language.Hakaru.Syntax.AST.Eq()
import Language.Hakaru.Simplify

import Test.HUnit
import Tests.TestTools

import Control.Exception

v :: (ABT Term abt) => abt '[] ('HMeasure 'HNat)
v = var (Variable "x" 0 (SMeasure SNat))

freevar :: TrivialABT Term '[] ('HMeasure 'HNat)
freevar = v

normal01T :: TrivialABT Term '[] ('HMeasure 'HReal)
normal01T =
    syn (MeasureOp_ Normal
        :$ syn (CoerceTo_ (CCons (Continuous HContinuous_Real) CNil) :$
            (syn (Literal_ (LInt (-2))) :* End))
        :* syn (CoerceTo_ (CCons (Continuous HContinuous_Prob) CNil) :$
            (syn (Literal_ (LNat 1)) :* End))
        :* End)

realpair :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
realpair =
    ann_ (SMeasure $ sPair SReal SReal)
        (dirac (pair (nat2real $ nat_ 1) (nat2real $ nat_ 2)))

unifprob, unifprob' :: TrivialABT Term '[] ('HMeasure 'HProb)
unifprob =
    uniform (real_ 1) (real_ 2) >>= \x ->
    dirac (unsafeProb x)

unifprob' =
    uniform (nat2real (nat_ 1)) (nat2real (nat_ 2)) >>= \x->
    dirac (unsafeProb x)

testS
    :: (ABT Term abt)
    => String
    -> abt '[] ('HMeasure a)
    -> Assertion
testS p x = do
    _ <- simplify x `catch` handleException (p ++ ": simplify failed")
    return ()

testSimplify
    ::  ( ABT Term abt
        , Show (abt '[] ('HMeasure a))
        , Eq   (abt '[] ('HMeasure a))
        )
    => String
    -> abt '[] ('HMeasure a)
    -> abt '[] ('HMeasure a)
    -> Assertion
testSimplify nm x y = do
    x' <- simplify x
    assertEqual nm y x'

allTests :: Test
allTests = test
    [ testSimplify "freevar" freevar freevar
    , testSimplify "normal01T" normal01T normal01T
    , testSimplify "realpair" realpair realpair
    , testSimplify "unifprob" unifprob unifprob'
    , testS "true" (triv $ ann_ (SMeasure sBool) (dirac true))
    ]
