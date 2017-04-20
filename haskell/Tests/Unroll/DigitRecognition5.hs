{-# LANGUAGE DataKinds, TypeOperators, OverloadedStrings #-}

module DigitRecognition5 where

import Prelude (print, length, IO)
import Language.Hakaru.Syntax.Prelude
import Language.Hakaru.Disintegrate
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing

type Model a b = TrivialABT Term '[] ('HMeasure (HPair a b))
type Cond  a b = TrivialABT Term '[] (a ':-> 'HMeasure b)

digitRecognition :: Model (HPair HBool 
                           (HPair HBool 
                            (HPair HBool 
                             (HPair HBool 
                              HBool))))
                    'HNat
digitRecognition =
    categorical dataPrior >>= \y ->
    bern ((dataParams ! y) ! (nat_ 0)) >>= \x0 ->
    bern ((dataParams ! y) ! (nat_ 1)) >>= \x1 ->
    bern ((dataParams ! y) ! (nat_ 2)) >>= \x2 ->
    bern ((dataParams ! y) ! (nat_ 3)) >>= \x3 ->
    bern ((dataParams ! y) ! (nat_ 4)) >>= \x4 ->
    dirac (pair (pair x0 
                 (pair x1 
                  (pair x2 
                   (pair x3 
                    x4))))
           y)
    where dataPrior  = var (Variable "dataPrior"  73 (SArray SProb))
          dataParams = var (Variable "dataParams" 41 (SArray (SArray SProb)))

main :: IO ()
main = print (length (disintegrate digitRecognition))
