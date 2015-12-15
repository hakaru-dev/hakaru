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

spreal :: Sing ('HMeasure (HPair 'HReal 'HReal))
spreal = SMeasure (sPair SReal SReal)

norm' :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
norm' = 
    normal (real_ 0) (prob_ 1) >>= \x ->
    normal x         (prob_ 1) >>= \y ->
    dirac (pair x y)

-- BUG: the current code for 'perform' will loop on annotations and coercions!
norm :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
norm = ann_ spreal norm'

test0 :: [TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))]
test0 = runM (perform norm) [Some2 norm]

test1 :: [TrivialABT Term '[] ('HReal ':-> 'HMeasure 'HReal)]
test1 = disintegrate norm
