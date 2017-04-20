{-# LANGUAGE DataKinds, TypeOperators, OverloadedStrings #-}

module LinearRegression50 where

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
                                                                           'HReal)))))))))))))))))))))))))))))))))))))))))))))))))
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
    normal (a * (dataX ! (nat_ 20))) (recip (sqrt invNoise)) >>= \y20 ->
    normal (a * (dataX ! (nat_ 21))) (recip (sqrt invNoise)) >>= \y21 ->
    normal (a * (dataX ! (nat_ 22))) (recip (sqrt invNoise)) >>= \y22 ->
    normal (a * (dataX ! (nat_ 23))) (recip (sqrt invNoise)) >>= \y23 ->
    normal (a * (dataX ! (nat_ 24))) (recip (sqrt invNoise)) >>= \y24 ->
    normal (a * (dataX ! (nat_ 25))) (recip (sqrt invNoise)) >>= \y25 ->
    normal (a * (dataX ! (nat_ 26))) (recip (sqrt invNoise)) >>= \y26 ->
    normal (a * (dataX ! (nat_ 27))) (recip (sqrt invNoise)) >>= \y27 ->
    normal (a * (dataX ! (nat_ 28))) (recip (sqrt invNoise)) >>= \y28 ->
    normal (a * (dataX ! (nat_ 29))) (recip (sqrt invNoise)) >>= \y29 ->
    normal (a * (dataX ! (nat_ 30))) (recip (sqrt invNoise)) >>= \y30 ->
    normal (a * (dataX ! (nat_ 31))) (recip (sqrt invNoise)) >>= \y31 ->
    normal (a * (dataX ! (nat_ 32))) (recip (sqrt invNoise)) >>= \y32 ->
    normal (a * (dataX ! (nat_ 33))) (recip (sqrt invNoise)) >>= \y33 ->
    normal (a * (dataX ! (nat_ 34))) (recip (sqrt invNoise)) >>= \y34 ->
    normal (a * (dataX ! (nat_ 35))) (recip (sqrt invNoise)) >>= \y35 ->
    normal (a * (dataX ! (nat_ 36))) (recip (sqrt invNoise)) >>= \y36 ->
    normal (a * (dataX ! (nat_ 37))) (recip (sqrt invNoise)) >>= \y37 ->
    normal (a * (dataX ! (nat_ 38))) (recip (sqrt invNoise)) >>= \y38 ->
    normal (a * (dataX ! (nat_ 39))) (recip (sqrt invNoise)) >>= \y39 ->
    normal (a * (dataX ! (nat_ 40))) (recip (sqrt invNoise)) >>= \y40 ->
    normal (a * (dataX ! (nat_ 41))) (recip (sqrt invNoise)) >>= \y41 ->
    normal (a * (dataX ! (nat_ 42))) (recip (sqrt invNoise)) >>= \y42 ->
    normal (a * (dataX ! (nat_ 43))) (recip (sqrt invNoise)) >>= \y43 ->
    normal (a * (dataX ! (nat_ 44))) (recip (sqrt invNoise)) >>= \y44 ->
    normal (a * (dataX ! (nat_ 45))) (recip (sqrt invNoise)) >>= \y45 ->
    normal (a * (dataX ! (nat_ 46))) (recip (sqrt invNoise)) >>= \y46 ->
    normal (a * (dataX ! (nat_ 47))) (recip (sqrt invNoise)) >>= \y47 ->
    normal (a * (dataX ! (nat_ 48))) (recip (sqrt invNoise)) >>= \y48 ->
    normal (a * (dataX ! (nat_ 49))) (recip (sqrt invNoise)) >>= \y49 ->
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
                                   (pair y19 
                                    (pair y20 
                                     (pair y21 
                                      (pair y22 
                                       (pair y23 
                                        (pair y24 
                                         (pair y25 
                                          (pair y26 
                                           (pair y27 
                                            (pair y28 
                                             (pair y29 
                                              (pair y30 
                                               (pair y31 
                                                (pair y32 
                                                 (pair y33 
                                                  (pair y34 
                                                   (pair y35 
                                                    (pair y36 
                                                     (pair y37 
                                                      (pair y38 
                                                       (pair y39 
                                                        (pair y40 
                                                         (pair y41 
                                                          (pair y42 
                                                           (pair y43 
                                                            (pair y44 
                                                             (pair y45 
                                                              (pair y46 
                                                               (pair y47 
                                                                (pair y48 
                                                                 y49)))))))))))))))))))))))))))))))))))))))))))))))))
           unit)
    where dataX = var (Variable "dataX" 73 (SArray SReal))

main :: IO ()
main = print (length (disintegrate linearRegression))
