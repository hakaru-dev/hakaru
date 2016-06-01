module Main where

import           Language.Hakaru.Runtime.Prelude
import qualified System.Random.MWC               as MWC
import           Control.Monad

prog :: MWC.GenIO -> IO Double
prog = normal (real_ 0) (prob_ 3)

main :: IO ()
main = do
  g <- MWC.createSystemRandom
  forever $ run g prog
  
