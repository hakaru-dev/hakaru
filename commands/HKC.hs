{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Main where

import           Data.Text
import qualified Data.Text.IO as IO

import Language.Hakaru.Parser.Parser hiding (style)

import System.Environment
import Text.RawString.QQ

main :: IO ()
main = do
  args   <- getArgs
  progs  <- mapM readFromFile args
  case progs of
      -- [prog1, prog2] -> randomWalk g prog1 prog2
      [prog] -> compileHakaru prog
      _      -> IO.putStrLn "Usage: hakaru <file>"

readFromFile :: String -> IO Text
readFromFile "-" = IO.getContents
readFromFile x   = IO.readFile x

compileHakaru :: Text -> IO ()
compileHakaru prog =
    case parseHakaru prog of
      Left err                 -> putStrLn $ show err
      Right x -> IO.putStrLn $ build prog -- $ pack $ show x

    --(TypedAST typ ast) -> IO.putStrLn prog
        -- case typ of
        --   SMeasure _ -> forever (illustrate typ g $ run ast)
        --   _          -> illustrate typ g $ run ast
    -- where
    -- run :: TrivialABT T.Term '[] a -> Value a
    -- run = runEvaluate

build :: Text -> Text
build p = mconcat
  [[r|#include <time.h>
#include <stdlib.h>
#include <stdio.h>
#include <math.h>
|]
   ,normalC
   ,[r|void main(){ srand(time(NULL)); while(1) { printf("%.17g\n",|]
   ,p
   ,[r|);}
}|]
  ]

normalC :: Text
normalC =
  [r|double normal(double mu, double sd) {
  double u = ((double)rand() / (RAND_MAX)) * 2 - 1;
  double v = ((double)rand() / (RAND_MAX)) * 2 - 1;
  double r = u*u + v*v;
  if (r==0 || r>1) return normal(mu,sd);
  double c = sqrt(-2 * log(r) / r);
  return mu + u * c * sd;
  }
|]
