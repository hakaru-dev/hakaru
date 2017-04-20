{-# LANGUAGE DataKinds, TypeOperators, OverloadedStrings #-}

module CoinBias20 where

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
                                     HBool)))))))))))))))))))
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
                                   tossResult19)))))))))))))))))))
           bias)

main :: IO ()
main = print (length (disintegrate coinBias))
