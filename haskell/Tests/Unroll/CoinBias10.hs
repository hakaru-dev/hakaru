{-# LANGUAGE DataKinds, TypeOperators, OverloadedStrings #-}

module CoinBias10 where

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
                           HBool)))))))))
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
    dirac (pair (pair tossResult0 
                 (pair tossResult1 
                  (pair tossResult2 
                   (pair tossResult3 
                    (pair tossResult4 
                     (pair tossResult5 
                      (pair tossResult6 
                       (pair tossResult7 
                        (pair tossResult8 
                         tossResult9)))))))))
           bias)

main :: IO ()
main = print (length (disintegrate coinBias))
