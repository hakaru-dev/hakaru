{-# LANGUAGE OverloadedStrings #-}

module Main where

import           Data.Text
import qualified Data.Text.IO as IO

import Language.Hakaru.Parser.Parser hiding (style)

import System.Environment

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
      Right x -> IO.putStrLn $ pack $ show x

    --(TypedAST typ ast) -> IO.putStrLn prog
        -- case typ of
        --   SMeasure _ -> forever (illustrate typ g $ run ast)
        --   _          -> illustrate typ g $ run ast
    -- where
    -- run :: TrivialABT T.Term '[] a -> Value a
    -- run = runEvaluate
