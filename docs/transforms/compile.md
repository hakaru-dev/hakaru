# Compiling to Haskell

Hakaru can be compiled to Haskell using the `compile` command.

For example if we wish to compile `example.hk`

````nohighlight
x <~ normal(0,1)
y <~ normal(x,1)
return y
````

We call `compile example.hk`, which produces a file `example.hs`.

````bash
cat example.hs
````

````haskell
{-# LANGUAGE DataKinds, NegativeLiterals #-}
module Main where

import           Prelude                          hiding (product)
import           Language.Hakaru.Runtime.Prelude
import           Language.Hakaru.Types.Sing
import qualified System.Random.MWC                as MWC
import           Control.Monad

prog = 
  normal (nat2real (nat_ 0)) (nat2prob (nat_ 1)) >>= \ x0 ->
  normal x0 (nat2prob (nat_ 1)) >>= \ y1 ->
  dirac y1

main :: IO ()
main = do
  g <- MWC.createSystemRandom
  forever $ run g prog
````

This is a regular Haskell file, which can then be furthered compiled into
machine code.



