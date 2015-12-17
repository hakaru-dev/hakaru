{-# LANGUAGE DataKinds
           , TypeOperators
           #-}

module Tests.Disintegrate where

import Prelude hiding ((>>=))

import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.Prelude
import Language.Hakaru.PrettyPrint      (pretty)
import Language.Hakaru.Evaluation.Types (runM)
import Language.Hakaru.Syntax.IClasses  (Some2(..))
import Language.Hakaru.Disintegrate

-- | A very simple program. Is sufficient for testing escape and
-- capture of substitution.
norm :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
norm =
    normal (real_ 0) (prob_ 1) >>= \x ->
    normal x         (prob_ 1) >>= \y ->
    dirac (pair x y)

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
    dirac (ann_ (sPair SReal SReal) (pair x y))

test0, test0a, test0b
    :: [TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))]
test0  = runM (perform norm)  [Some2 norm]
test0a = runM (perform normA) [Some2 normA]
test0b = runM (perform normB) [Some2 normB]

-- BUG: at present, both 'test1' and 'test1a' throw errors about
-- @typeOf_{Datum_}@. Whereas 'test1b' loops.
test1, test1a, test1b
    :: [TrivialABT Term '[] ('HReal ':-> 'HMeasure 'HReal)]
test1  = disintegrate norm
test1a = disintegrate normA
test1b = disintegrate normB
