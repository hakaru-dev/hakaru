{-# LANGUAGE DataKinds, TypeOperators, OverloadedStrings #-}

module LinearRegression20 where

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
                              (HPair 'HReal 
                               (HPair 'HReal 
                                (HPair 'HReal 
                                 (HPair 'HReal 
                                  (HPair 'HReal 
                                   (HPair 'HReal 
                                    (HPair 'HReal 
                                     (HPair 'HReal 
                                      (HPair 'HReal 
                                       (HPair 'HReal 
                                        (HPair 'HReal 
                                         (HPair 'HReal 
                                          (HPair 'HReal 
                                           (HPair 'HReal 
                                            (HPair 'HReal 
                                             'HReal)))))))))))))))))))
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
    normal (a * (dataX ! (nat_ 5))) (recip (sqrt invNoise)) >>= \y5 ->
    normal (a * (dataX ! (nat_ 6))) (recip (sqrt invNoise)) >>= \y6 ->
    normal (a * (dataX ! (nat_ 7))) (recip (sqrt invNoise)) >>= \y7 ->
    normal (a * (dataX ! (nat_ 8))) (recip (sqrt invNoise)) >>= \y8 ->
    normal (a * (dataX ! (nat_ 9))) (recip (sqrt invNoise)) >>= \y9 ->
    normal (a * (dataX ! (nat_ 10))) (recip (sqrt invNoise)) >>= \y10 ->
    normal (a * (dataX ! (nat_ 11))) (recip (sqrt invNoise)) >>= \y11 ->
    normal (a * (dataX ! (nat_ 12))) (recip (sqrt invNoise)) >>= \y12 ->
    normal (a * (dataX ! (nat_ 13))) (recip (sqrt invNoise)) >>= \y13 ->
    normal (a * (dataX ! (nat_ 14))) (recip (sqrt invNoise)) >>= \y14 ->
    normal (a * (dataX ! (nat_ 15))) (recip (sqrt invNoise)) >>= \y15 ->
    normal (a * (dataX ! (nat_ 16))) (recip (sqrt invNoise)) >>= \y16 ->
    normal (a * (dataX ! (nat_ 17))) (recip (sqrt invNoise)) >>= \y17 ->
    normal (a * (dataX ! (nat_ 18))) (recip (sqrt invNoise)) >>= \y18 ->
    normal (a * (dataX ! (nat_ 19))) (recip (sqrt invNoise)) >>= \y19 ->
    dirac (pair (pair y0 
                 (pair y1 
                  (pair y2 
                   (pair y3 
                    (pair y4 
                     (pair y5 
                      (pair y6 
                       (pair y7 
                        (pair y8 
                         (pair y9 
                          (pair y10 
                           (pair y11 
                            (pair y12 
                             (pair y13 
                              (pair y14 
                               (pair y15 
                                (pair y16 
                                 (pair y17 
                                  (pair y18 
                                   y19)))))))))))))))))))
           unit)
    where dataX = var (Variable "dataX" 73 (SArray SReal))

main :: IO ()
main = print (length (disintegrate linearRegression))
