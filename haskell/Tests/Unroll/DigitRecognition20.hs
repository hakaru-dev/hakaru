{-# LANGUAGE DataKinds, TypeOperators, OverloadedStrings #-}

module DigitRecognition20 where

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
                              (HPair HBool 
                               (HPair HBool 
                                (HPair HBool 
                                 (HPair HBool 
                                  (HPair HBool 
                                   (HPair HBool 
                                    (HPair HBool 
                                     (HPair HBool 
                                      (HPair HBool 
                                       (HPair HBool 
                                        (HPair HBool 
                                         (HPair HBool 
                                          (HPair HBool 
                                           (HPair HBool 
                                            (HPair HBool 
                                             HBool)))))))))))))))))))
                    'HNat
digitRecognition =
    categorical dataPrior >>= \y ->
    bern ((dataParams ! y) ! (nat_ 0)) >>= \x0 ->
    bern ((dataParams ! y) ! (nat_ 1)) >>= \x1 ->
    bern ((dataParams ! y) ! (nat_ 2)) >>= \x2 ->
    bern ((dataParams ! y) ! (nat_ 3)) >>= \x3 ->
    bern ((dataParams ! y) ! (nat_ 4)) >>= \x4 ->
    bern ((dataParams ! y) ! (nat_ 5)) >>= \x5 ->
    bern ((dataParams ! y) ! (nat_ 6)) >>= \x6 ->
    bern ((dataParams ! y) ! (nat_ 7)) >>= \x7 ->
    bern ((dataParams ! y) ! (nat_ 8)) >>= \x8 ->
    bern ((dataParams ! y) ! (nat_ 9)) >>= \x9 ->
    bern ((dataParams ! y) ! (nat_ 10)) >>= \x10 ->
    bern ((dataParams ! y) ! (nat_ 11)) >>= \x11 ->
    bern ((dataParams ! y) ! (nat_ 12)) >>= \x12 ->
    bern ((dataParams ! y) ! (nat_ 13)) >>= \x13 ->
    bern ((dataParams ! y) ! (nat_ 14)) >>= \x14 ->
    bern ((dataParams ! y) ! (nat_ 15)) >>= \x15 ->
    bern ((dataParams ! y) ! (nat_ 16)) >>= \x16 ->
    bern ((dataParams ! y) ! (nat_ 17)) >>= \x17 ->
    bern ((dataParams ! y) ! (nat_ 18)) >>= \x18 ->
    bern ((dataParams ! y) ! (nat_ 19)) >>= \x19 ->
    dirac (pair (pair x0 
                 (pair x1 
                  (pair x2 
                   (pair x3 
                    (pair x4 
                     (pair x5 
                      (pair x6 
                       (pair x7 
                        (pair x8 
                         (pair x9 
                          (pair x10 
                           (pair x11 
                            (pair x12 
                             (pair x13 
                              (pair x14 
                               (pair x15 
                                (pair x16 
                                 (pair x17 
                                  (pair x18 
                                   x19)))))))))))))))))))
           y)
    where dataPrior  = var (Variable "dataPrior"  73 (SArray SProb))
          dataParams = var (Variable "dataParams" 41 (SArray (SArray SProb)))

main :: IO ()
main = print (length (disintegrate digitRecognition))
