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

v :: (ABT Term abt) => abt '[] ('HMeasure 'HNat)
v = var (Variable "x" 0 (SMeasure SNat))

freevar :: TrivialABT Term '[] ('HMeasure 'HNat)
freevar = v

normal01T :: TrivialABT Term '[] ('HMeasure 'HReal)
normal01T =
    syn (MeasureOp_ Normal
        :$ syn (Literal_ (LReal (-2)))
        :* syn (Literal_ (LProb 1))
        :* End)

realpair :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
realpair =
    ann_ (SMeasure $ sPair SReal SReal)
        (dirac (pair (nat2real $ nat_ 1) (nat2real $ nat_ 2)))

unifprob  :: TrivialABT Term '[] ('HMeasure 'HProb)
unifprob =
    uniform (real_ 1) (real_ 2) >>= \x ->
    dirac (unsafeProb x)

testSimplify
    ::  ( ABT Term abt
        , Show (abt '[] a)
        , Eq   (abt '[] a)
        )
    => String
    -> abt '[] a
    -> abt '[] a
    -> Assertion
testSimplify nm x y = do
    x' <- simplify x
    assertEqual nm y x'

allTests :: Test
allTests = test
    [ testSimplify "freevar" freevar freevar
    , testSimplify "normal01T" normal01T normal01T
    , testSimplify "realpair" realpair realpair
    , testSimplify "unifprob" unifprob unifprob
    , testS "true" (triv $ ann_ (SMeasure sBool) (dirac true))
    ]
