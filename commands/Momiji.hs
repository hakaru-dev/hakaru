{-# LANGUAGE OverloadedStrings, DataKinds, GADTs #-}

module Main where

import qualified Language.Hakaru.Pretty.Maple as Maple
import           Language.Hakaru.Syntax.AST.Transforms
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Command

import           Data.Text
import qualified Data.Text.IO as IO
import           System.IO (stderr)

import           System.Environment

main :: IO ()
main = simpleCommand runPretty "momiji"

runPretty :: Text -> IO ()
runPretty prog =
    case parseAndInfer prog of
    Left  err              -> hPut_utf8 stderr err
    Right (TypedAST typ ast) -> do
      putStrLn_utf8 $ pack $ Maple.pretty (expandTransformations ast)
      putStrLn_utf8 $ ","
      putStrLn_utf8 $ pack $ Maple.mapleType typ ""

