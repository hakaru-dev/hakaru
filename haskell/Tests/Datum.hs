{-# LANGUAGE TypeFamilies
           , FlexibleContexts
           , DeriveGeneric
           , TemplateHaskell
           , UndecidableInstances
           , ConstraintKinds
           , DeriveDataTypeable
           , ScopedTypeVariables
           , DataKinds
           #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}

module Tests.Datum (allTests) where

import Language.Hakaru.Types.DataKind
import Language.Hakaru.Syntax.Prelude
import Language.Hakaru.Pretty.Haskell

import Data.Foldable       (forM_)
import Data.Function       (on)
import Control.Exception
import Data.Typeable
import Test.HUnit
import Tests.TestTools

import Language.Hakaru.Any (Any(unAny))
import Language.Hakaru.Sample
import Language.Hakaru.Embed
import Language.Hakaru.Maple
import Language.Hakaru.Simplify

----------------------------------------------------------------
----------------------------------------------------------------
-- Variant of testSS for Embeddable a
testSE :: (ABT Term abt, Simplifiable a) => abt '[] a -> Assertion
testSE t = do
    p <- simplify t `catch` handleSimplify t
    let s = result (unAny p)
    assertResult (show s)

testSSE
    :: (ABT Term abt, Simplifiable a) => [Maple a] -> abt '[] a -> Assertion
testSSE ts t' =
    forM_ (t' : ts) $ \t -> do
        p <- simplify t --`catch` handleSimplify t
        (assertEqual "testSS" `on` result) t' (unAny p)


allTests :: Test
allTests = test 
    [ "HPair-elim" ~: testSSE [t1] (uniform 1 2)
    , "HPair-id"   ~: testSSE [] t3
    , "HList-id"   ~: testSSE [] testList0
    ]

testList0 :: (ABT Term abt) => abt '[] (HList 'HInt)
testList0 = foldr cons nil $ map int_ [1, 2, 3, 4]

t1 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
t1 = unpair (pair 1 2) uniform

t3 :: (ABT Term abt) => abt '[] ('HMeasure (HPair 'HInt 'HReal))
t3 = dirac (pair 1 2)

----------------------------------------------------------------
-- The following at not all Datum-related, but were 'generated'
-- through an analysis of Datum-related test failures.
-- Recorded here to that these eventually all pass, and no
-- future regressions happen.  JC (but tests from WR)

-- All of these fail due to the typeOf{Datum} issue
test2a = runM (perform m)  [Some2 m]
    where
    m :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
    m = dirac (pair zero zero) >>= \x -> dirac x

test2b = runM (perform m)  [Some2 m]
    where
    m :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
    m = ann_ sing (dirac (pair zero zero) >>= \x -> dirac x)

test2c = runM (perform m)  [Some2 m]
    where
    m :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
    m = dirac (pair zero zero) >>= \x -> dirac (ann_ sing x)

-- Whereas these do not fail from the typeOf{Datum} issue.
-- However, they still fail for other reasons (which look to be the same
-- SomeSymbol issues as with roundtripping through Maple):
test2d = runM (perform m)  [Some2 m]
    where
    m :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
    m = ann_ sing (dirac (pair zero zero)) >>= \x -> dirac x

test2e = runM (perform m)  [Some2 m]
    where
    m :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
    m = dirac (ann_ sing (pair zero zero)) >>= \x -> dirac x

----------------------------------------------------------------
----------------------------------------------------------- fin.
