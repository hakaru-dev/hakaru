{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Main where

import           Data.Text
import qualified Data.Text.IO as IO

import Language.Hakaru.Parser.Parser hiding (style)
import Language.Hakaru.Syntax.ABT

import HKC.Flatten
import HKC.Prelude

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

-- This is nice for testing programs quickly
readFromFile :: String -> IO Text
readFromFile "-" = IO.getContents
readFromFile x   = IO.readFile x

compileHakaru :: Text -> IO ()
compileHakaru prog =
    case parseHakaru prog of
      Left err                 -> putStrLn $ show err
      Right x -> IO.putStrLn $ pack $ show x
