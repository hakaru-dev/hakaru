{-# LANGUAGE DataKinds, TypeOperators, OverloadedStrings #-}

module CoinBias50 where

import Prelude (print, length, IO)
import Language.Hakaru.Syntax.Prelude
import Language.Hakaru.Disintegrate
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing

type Model a b = TrivialABT Term '[] ('HMeasure (HPair a b))
type Cond  a b = TrivialABT Term '[] (a ':-> 'HMeasure b)

coinBias :: Model (HPair HBool 
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
            'HProb
coinBias =
    beta (prob_ 2) (prob_ 5) >>= \bias ->
    bern bias >>= \tossResult0 ->
    bern bias >>= \tossResult1 ->
    bern bias >>= \tossResult2 ->
    bern bias >>= \tossResult3 ->
    bern bias >>= \tossResult4 ->
    bern bias >>= \tossResult5 ->
    bern bias >>= \tossResult6 ->
    bern bias >>= \tossResult7 ->
    bern bias >>= \tossResult8 ->
    bern bias >>= \tossResult9 ->
    bern bias >>= \tossResult10 ->
    bern bias >>= \tossResult11 ->
    bern bias >>= \tossResult12 ->
    bern bias >>= \tossResult13 ->
    bern bias >>= \tossResult14 ->
    bern bias >>= \tossResult15 ->
    bern bias >>= \tossResult16 ->
    bern bias >>= \tossResult17 ->
    bern bias >>= \tossResult18 ->
    bern bias >>= \tossResult19 ->
    bern bias >>= \tossResult20 ->
    bern bias >>= \tossResult21 ->
    bern bias >>= \tossResult22 ->
    bern bias >>= \tossResult23 ->
    bern bias >>= \tossResult24 ->
    bern bias >>= \tossResult25 ->
    bern bias >>= \tossResult26 ->
    bern bias >>= \tossResult27 ->
    bern bias >>= \tossResult28 ->
    bern bias >>= \tossResult29 ->
    bern bias >>= \tossResult30 ->
    bern bias >>= \tossResult31 ->
    bern bias >>= \tossResult32 ->
    bern bias >>= \tossResult33 ->
    bern bias >>= \tossResult34 ->
    bern bias >>= \tossResult35 ->
    bern bias >>= \tossResult36 ->
    bern bias >>= \tossResult37 ->
    bern bias >>= \tossResult38 ->
    bern bias >>= \tossResult39 ->
    bern bias >>= \tossResult40 ->
    bern bias >>= \tossResult41 ->
    bern bias >>= \tossResult42 ->
    bern bias >>= \tossResult43 ->
    bern bias >>= \tossResult44 ->
    bern bias >>= \tossResult45 ->
    bern bias >>= \tossResult46 ->
    bern bias >>= \tossResult47 ->
    bern bias >>= \tossResult48 ->
    bern bias >>= \tossResult49 ->
    dirac (pair (pair tossResult0 
                 (pair tossResult1 
                  (pair tossResult2 
                   (pair tossResult3 
                    (pair tossResult4 
                     (pair tossResult5 
                      (pair tossResult6 
                       (pair tossResult7 
                        (pair tossResult8 
                         (pair tossResult9 
                          (pair tossResult10 
                           (pair tossResult11 
                            (pair tossResult12 
                             (pair tossResult13 
                              (pair tossResult14 
                               (pair tossResult15 
                                (pair tossResult16 
                                 (pair tossResult17 
                                  (pair tossResult18 
                                   (pair tossResult19 
                                    (pair tossResult20 
                                     (pair tossResult21 
                                      (pair tossResult22 
                                       (pair tossResult23 
                                        (pair tossResult24 
                                         (pair tossResult25 
                                          (pair tossResult26 
                                           (pair tossResult27 
                                            (pair tossResult28 
                                             (pair tossResult29 
                                              (pair tossResult30 
                                               (pair tossResult31 
                                                (pair tossResult32 
                                                 (pair tossResult33 
                                                  (pair tossResult34 
                                                   (pair tossResult35 
                                                    (pair tossResult36 
                                                     (pair tossResult37 
                                                      (pair tossResult38 
                                                       (pair tossResult39 
                                                        (pair tossResult40 
                                                         (pair tossResult41 
                                                          (pair tossResult42 
                                                           (pair tossResult43 
                                                            (pair tossResult44 
                                                             (pair tossResult45 
                                                              (pair tossResult46 
                                                               (pair tossResult47 
                                                                (pair tossResult48 
                                                                 tossResult49)))))))))))))))))))))))))))))))))))))))))))))))))
           bias)

main :: IO ()
main = print (length (disintegrate coinBias))
