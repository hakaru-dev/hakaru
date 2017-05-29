{-# LANGUAGE OverloadedStrings, DataKinds, GADTs #-}

module Main where

import           Language.Hakaru.Pretty.Concrete
import           Language.Hakaru.Syntax.AST.Transforms
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Command

import           Data.Text
import qualified Data.Text.IO as IO
import           System.IO (stderr)

import           System.Environment

main :: IO ()
main = simpleCommand runPretty "pretty"

runPretty :: Text -> IO ()
runPretty prog =
    case parseAndInfer prog of
    Left  err              -> IO.hPutStrLn stderr err
    Right (TypedAST _ ast) -> print . pretty . expandTransformations $ ast

