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
----------------------------------------------------------- fin.