{-# LANGUAGE DataKinds
           , GADTs
           , TypeOperators
           , NoImplicitPrelude
           , FlexibleContexts
           #-}

module Tests.Disintegrate where

import           Prelude (($), (++), (>), head,
                          length, String, Maybe(..))
import qualified Prelude

import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Prelude hiding ((>))
import Language.Hakaru.Syntax.IClasses  (Some2(..), TypeEq(..), jmEq1)
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing
import Language.Hakaru.Syntax.TypeCheck
import Language.Hakaru.Evaluation.Types               (fromWhnf)
import Language.Hakaru.Evaluation.DisintegrationMonad (runDis)
import Language.Hakaru.Disintegrate

import qualified Language.Hakaru.Observe as O

import Test.HUnit
import Tests.TestTools
import Tests.Models (match_norm_unif)

-- | Tests that a disintegration is produced without error
testDis :: (ABT Term abt)
        => String
        -> abt '[] ('HMeasure (HPair a b))
        -> Assertion
testDis p a = assertBool (p ++ ": no disintegration found")
               (length (disintegrate a) > 0)

-- | A very simple program. Is sufficient for testing escape and
-- capture of substitution.
norm :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
norm =
    normal (real_ 0) (prob_ 1) >>= \x ->
    normal x         (prob_ 1) >>= \y ->
    dirac (pair y x)

-- | The original test program, useful for testing that using 'Ann_'
-- doesn't loop.
normA :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
normA = ann_ (SMeasure (sPair SReal SReal)) norm

-- | An attempt to deal with the @typeOf_{Datum_}@ issue without
-- changing the 'Datum' type nor the 'typeOf' definition.
normB :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
normB =
    normal (real_ 0) (prob_ 1) >>= \x ->
    normal x         (prob_ 1) >>= \y ->
    dirac (ann_ (sPair SReal SReal) (pair y x))

-- | What we expect norm{A,B} to disintegrate to
normC :: TrivialABT Term '[] ('HReal ':-> 'HMeasure 'HReal)
normC = lam $ \y ->
        normal (real_ 0) (prob_ 1) >>= \x ->
        ann_ (SMeasure SReal) (O.observe (normal x (prob_ 1)) y x)
{-
-- Eliminating some redexes of 'normC', that is:
    lam $ \y ->
    normal (real_ 0) (prob_ 1) >>= \x ->
    withWeight
        (exp ((x - y) ^ nat_ 2 / real_ 2)
        / (nat_ 2 `thRootOf` (prob_ 2 * pi)))
    $ dirac x

-- N.B., calling 'evaluate' on 'normC' doesn't catch those redexes because they're not on the way to computing stuff. need to call 'constantPropagation' to get rid of them.
-}

test0, test0a, test0b
    :: [TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))]
test0  = runDis (fromWhnf `Prelude.fmap` perform norm)  [Some2 norm]
test0a = runDis (fromWhnf `Prelude.fmap` perform normA) [Some2 normA]
test0b = runDis (fromWhnf `Prelude.fmap` perform normB) [Some2 normB]

-- BUG: at present, both 'test1' throws errors about @typeOf_{Datum_}@.
test1, test1a, test1b
    :: [TrivialABT Term '[] ('HReal ':-> 'HMeasure 'HReal)]
test1  = disintegrate norm
test1a = disintegrate normA
test1b = disintegrate normB

-- | The goal of this test is to be sure we maintain proper hygiene
-- for the weight component when disintegrating superpose. Moreover,
-- in earlier versions it used to throw VarEqTypeError due to
-- 'disintegrate' not choosing a sufficiently fresh variable name
-- for its lambda; thus this also serves as a regression test to
-- make sure we don't run into that problem again.
test2
    :: [TrivialABT Term '[] ('HReal ':-> 'HMeasure 'HReal)]
test2 =
    disintegrate $
        let_ (prob_ 1) $ \x ->
        withWeight x normA

allTests :: Test
allTests = test
   [ assertAlphaEq "test1a" normC (head test1a)
   , assertAlphaEq "test1b" normC (head test1b)
   --, assertAlphaEq "test1"  normC (head test1)
   , testWithConcrete' match_norm_unif LaxMode
      (\(TypedAST _typ ast) ->
           case jmEq1 _typ (SMeasure $ sPair SReal sBool) of
             Just Refl -> testDis "testMatchNormUnif" ast
             Nothing   -> assertFailure "Bug: jmEq1 got the wrong type")
   ]
