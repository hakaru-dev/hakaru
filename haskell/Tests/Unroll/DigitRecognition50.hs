{-# LANGUAGE DataKinds, TypeOperators, OverloadedStrings #-}

module DigitRecognition50 where

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
                                                                           HBool)))))))))))))))))))))))))))))))))))))))))))))))))
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
    bern ((dataParams ! y) ! (nat_ 20)) >>= \x20 ->
    bern ((dataParams ! y) ! (nat_ 21)) >>= \x21 ->
    bern ((dataParams ! y) ! (nat_ 22)) >>= \x22 ->
    bern ((dataParams ! y) ! (nat_ 23)) >>= \x23 ->
    bern ((dataParams ! y) ! (nat_ 24)) >>= \x24 ->
    bern ((dataParams ! y) ! (nat_ 25)) >>= \x25 ->
    bern ((dataParams ! y) ! (nat_ 26)) >>= \x26 ->
    bern ((dataParams ! y) ! (nat_ 27)) >>= \x27 ->
    bern ((dataParams ! y) ! (nat_ 28)) >>= \x28 ->
    bern ((dataParams ! y) ! (nat_ 29)) >>= \x29 ->
    bern ((dataParams ! y) ! (nat_ 30)) >>= \x30 ->
    bern ((dataParams ! y) ! (nat_ 31)) >>= \x31 ->
    bern ((dataParams ! y) ! (nat_ 32)) >>= \x32 ->
    bern ((dataParams ! y) ! (nat_ 33)) >>= \x33 ->
    bern ((dataParams ! y) ! (nat_ 34)) >>= \x34 ->
    bern ((dataParams ! y) ! (nat_ 35)) >>= \x35 ->
    bern ((dataParams ! y) ! (nat_ 36)) >>= \x36 ->
    bern ((dataParams ! y) ! (nat_ 37)) >>= \x37 ->
    bern ((dataParams ! y) ! (nat_ 38)) >>= \x38 ->
    bern ((dataParams ! y) ! (nat_ 39)) >>= \x39 ->
    bern ((dataParams ! y) ! (nat_ 40)) >>= \x40 ->
    bern ((dataParams ! y) ! (nat_ 41)) >>= \x41 ->
    bern ((dataParams ! y) ! (nat_ 42)) >>= \x42 ->
    bern ((dataParams ! y) ! (nat_ 43)) >>= \x43 ->
    bern ((dataParams ! y) ! (nat_ 44)) >>= \x44 ->
    bern ((dataParams ! y) ! (nat_ 45)) >>= \x45 ->
    bern ((dataParams ! y) ! (nat_ 46)) >>= \x46 ->
    bern ((dataParams ! y) ! (nat_ 47)) >>= \x47 ->
    bern ((dataParams ! y) ! (nat_ 48)) >>= \x48 ->
    bern ((dataParams ! y) ! (nat_ 49)) >>= \x49 ->
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
                                   (pair x19 
                                    (pair x20 
                                     (pair x21 
                                      (pair x22 
                                       (pair x23 
                                        (pair x24 
                                         (pair x25 
                                          (pair x26 
                                           (pair x27 
                                            (pair x28 
                                             (pair x29 
                                              (pair x30 
                                               (pair x31 
                                                (pair x32 
                                                 (pair x33 
                                                  (pair x34 
                                                   (pair x35 
                                                    (pair x36 
                                                     (pair x37 
                                                      (pair x38 
                                                       (pair x39 
                                                        (pair x40 
                                                         (pair x41 
                                                          (pair x42 
                                                           (pair x43 
                                                            (pair x44 
                                                             (pair x45 
                                                              (pair x46 
                                                               (pair x47 
                                                                (pair x48 
                                                                 x49)))))))))))))))))))))))))))))))))))))))))))))))))
           y)
    where dataPrior  = var (Variable "dataPrior"  73 (SArray SProb))
          dataParams = var (Variable "dataParams" 41 (SArray (SArray SProb)))

main :: IO ()
main = print (length (disintegrate digitRecognition))
