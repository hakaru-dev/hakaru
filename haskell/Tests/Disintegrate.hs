{-# LANGUAGE DataKinds
           , GADTs
           , TypeOperators
           , NoImplicitPrelude
           , FlexibleContexts
           #-}

module Tests.Disintegrate where

import           Prelude (($), (.), (++), head, String, Maybe(..))
import qualified Prelude

import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Prelude
import Language.Hakaru.Syntax.IClasses (Some2(..), TypeEq(..), jmEq1)
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing
import Language.Hakaru.Syntax.TypeCheck
import Language.Hakaru.Evaluation.Types               (fromWhnf)
import Language.Hakaru.Evaluation.DisintegrationMonad (runDis)
import Language.Hakaru.Disintegrate

import Test.HUnit
import Tests.TestTools
import Tests.Models (match_norm_unif)

----------------------------------------------------------------
----------------------------------------------------------------

-- | A very simple program. Is sufficient for testing escape and
-- capture of substitution.
norm0 :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
norm0 =
    normal (real_ 0) (prob_ 1) >>= \x ->
    normal x         (prob_ 1) >>= \y ->
    dirac (pair y x)

-- | A version of 'norm0' which adds a type annotation at the
-- top-level; useful for testing that using 'Ann_' doesn't cause
-- perform\/disintegrate to loop.
norm0a :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
norm0a = ann_ sing norm0

-- | A version of 'norm0' which inserts an annotation around the
-- 'Datum' constructor itself. The goal here is to circumvent the
-- @typeOf_{Datum_}@ issue without needing to change the 'Datum'
-- type nor the 'typeOf' definition.
norm0b :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
norm0b =
    normal (real_ 0) (prob_ 1) >>= \x ->
    normal x         (prob_ 1) >>= \y ->
    dirac (ann_ sing $ pair y x)

-- | What we expect 'norm0' (and variants) to disintegrate to.
norm0' :: TrivialABT Term '[] ('HReal ':-> 'HMeasure 'HReal)
norm0' =
    lam $ \y ->
    normal (real_ 0) (prob_ 1) >>= \x ->
    ann_ sing $
        withWeight (densityNormal x (prob_ 1) y) (dirac x)
{-
-- Eliminating some redexes of 'norm0'', that is:
    lam $ \y ->
    normal (real_ 0) (prob_ 1) >>= \x ->
    withWeight
        (exp ((x - y) ^ nat_ 2 / real_ 2)
        / (nat_ 2 `thRootOf` (prob_ 2 * pi)))
    $ dirac x

-- N.B., calling 'evaluate' on 'norm0'' doesn't catch those redexes because they're not on the way to computing stuff. need to call 'constantPropagation' to get rid of them.
-}


testPerform0, testPerform0a, testPerform0b
    :: [TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))]
testPerform0  = runPerform norm0
testPerform0a = runPerform norm0a
testPerform0b = runPerform norm0b

-- BUG: at present, these throw errors about @typeOf_{Datum_}@.
testDisintegrate0, testDisintegrate0a, testDisintegrate0b
    :: [TrivialABT Term '[] ('HReal ':-> 'HMeasure 'HReal)]
testDisintegrate0  = disintegrate norm0
testDisintegrate0a = disintegrate norm0a
testDisintegrate0b = disintegrate norm0b

-- | The goal of this test is to be sure we maintain proper hygiene
-- for the weight component when disintegrating superpose. Moreover,
-- in earlier versions it used to throw VarEqTypeError due to
-- 'disintegrate' not choosing a sufficiently fresh variable name
-- for its lambda; thus this also serves as a regression test to
-- make sure we don't run into that problem again.
testHygiene0a :: [TrivialABT Term '[] ('HReal ':-> 'HMeasure 'HReal)]
testHygiene0a =
    disintegrate $
        let_ (prob_ 1) $ \x ->
        withWeight x norm0a

----------------------------------------------------------------
-- | This simple progam is to check for disintegrating case analysis
-- when the scrutinee contains a heap-bound variable.
norm1a :: TrivialABT Term '[] ('HMeasure (HPair 'HReal HUnit))
norm1a =
    normal (real_ 3) (prob_ 2) >>= \x ->
    dirac $ if_ (x < real_ 0)
        (ann_ sing $ pair (negate x) unit)
        (ann_ sing $ pair         x  unit)

norm1b :: TrivialABT Term '[] ('HMeasure (HPair 'HReal HUnit))
norm1b =
    normal (real_ 3) (prob_ 2) >>= \x ->
    if_ (x < real_ 0)
        (ann_ sing . dirac $ pair (negate x) unit)
        (ann_ sing . dirac $ pair         x  unit)


testPerform1a, testPerform1b
    :: [TrivialABT Term '[] ('HMeasure (HPair 'HReal HUnit))]
testPerform1a = runPerform norm1a
testPerform1b = runPerform norm1b

testDisintegrate1a, testDisintegrate1b
    :: [TrivialABT Term '[] ('HReal ':-> 'HMeasure HUnit)]
testDisintegrate1a = disintegrate norm1a
testDisintegrate1b = disintegrate norm1b


----------------------------------------------------------------
norm2 :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
norm2 =
    normal (real_ 3) (prob_ 2) >>= \x ->
    normal (real_ 5) (prob_ 4) >>= \y ->
    dirac $ if_ (x < y)
        (pair y x)
        (pair x x)

testPerform2
    :: [TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))]
testPerform2 = runPerform norm2

testDisintegrate2
    :: [TrivialABT Term '[] ('HReal ':-> 'HMeasure 'HReal)]
testDisintegrate2 = disintegrate norm2


----------------------------------------------------------------
----------------------------------------------------------------
runPerform
    :: TrivialABT Term '[] ('HMeasure a)
    -> [TrivialABT Term '[] ('HMeasure a)]
runPerform e = runDis (fromWhnf `Prelude.fmap` perform e) [Some2 e]


-- | Tests that disintegration doesn't error and produces at least
-- one solution.
testDis
    :: (ABT Term abt)
    => String
    -> abt '[] ('HMeasure (HPair a b))
    -> Assertion
testDis p =
    assertBool (p ++ ": no disintegration found")
    . Prelude.not
    . Prelude.null
    . disintegrate


-- TODO: actually put all the above tests in here!
allTests :: Test
allTests = test
    [ assertAlphaEq "testDisintegrate0a" norm0' (head testDisintegrate0a)
    , assertAlphaEq "testDisintegrate0b" norm0' (head testDisintegrate0b)
    --, assertAlphaEq "testDisintegrate0"  norm0' (head testDisintegrate0)
    , testWithConcrete' match_norm_unif LaxMode $ \(TypedAST _typ ast) ->
        case jmEq1 _typ (SMeasure $ sPair SReal sBool) of
        Just Refl -> testDis "testMatchNormUnif" ast
        Nothing   -> assertFailure "BUG: jmEq1 got the wrong type"
    ]

----------------------------------------------------------------
----------------------------------------------------------- fin.
