{-# LANGUAGE OverloadedStrings, DataKinds, GADTs #-}

module Main where

import qualified Language.Hakaru.Pretty.Maple as Maple
import           Language.Hakaru.Syntax.AST.Transforms
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Command

import           Data.Text
import qualified Data.Text.Utf8 as U

import           System.IO (stderr)

main :: IO ()
main = simpleCommand runPretty "momiji"

runPretty :: Text -> IO ()
runPretty prog =
    case parseAndInfer prog of
    Left  err              -> U.hPut stderr err
    Right (TypedAST typ ast) -> do
      U.putStrLnS $ Maple.pretty (expandTransformations ast)
      U.putStrLn  $ ","
      U.putStrLnS $ Maple.mapleType typ ""

