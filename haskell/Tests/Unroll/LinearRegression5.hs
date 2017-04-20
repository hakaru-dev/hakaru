{-# LANGUAGE DataKinds, TypeOperators, OverloadedStrings #-}

module LinearRegression5 where

import Prelude (print, length, IO)
import Language.Hakaru.Syntax.Prelude
import Language.Hakaru.Disintegrate
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing

type Model a b = TrivialABT Term '[] ('HMeasure (HPair a b))
type Cond  a b = TrivialABT Term '[] (a ':-> 'HMeasure b)

linearRegression :: Model (HPair 'HReal 
                           (HPair 'HReal 
                            (HPair 'HReal 
                             (HPair 'HReal 
                              'HReal))))
                    HUnit
linearRegression =
    normal (real_ 0) (prob_ 1) >>= \a ->
    normal (real_ 5) (prob_ 1.825) >>= \b ->
    gamma (prob_ 1) (prob_ 1) >>= \invNoise ->
    normal (a * (dataX ! (nat_ 0))) (recip (sqrt invNoise)) >>= \y0 ->
    normal (a * (dataX ! (nat_ 1))) (recip (sqrt invNoise)) >>= \y1 ->
    normal (a * (dataX ! (nat_ 2))) (recip (sqrt invNoise)) >>= \y2 ->
    normal (a * (dataX ! (nat_ 3))) (recip (sqrt invNoise)) >>= \y3 ->
    normal (a * (dataX ! (nat_ 4))) (recip (sqrt invNoise)) >>= \y4 ->
    dirac (pair (pair y0 
                 (pair y1 
                  (pair y2 
                   (pair y3 
                    y4))))
           unit)
    where dataX = var (Variable "dataX" 73 (SArray SReal))

main :: IO ()
main = print (length (disintegrate linearRegression))
