{-# LANGUAGE OverloadedStrings, DataKinds, GADTs #-}

module Main where

import           Language.Hakaru.Pretty.Concrete
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Syntax.IClasses

import           Language.Hakaru.Types.Sing
import           Language.Hakaru.Disintegrate
import           Language.Hakaru.Evaluation.ConstantPropagation
import           Language.Hakaru.Command

import           Data.Text
import qualified Data.Text.IO as IO

import           System.Environment

main :: IO ()
main = do
  args  <- getArgs
  progs <- mapM readFromFile args
  case progs of
      [prog] -> runDensity prog
      _      -> IO.putStrLn "Usage: density <file>"

runDensity :: Text -> IO ()
runDensity prog =
    case parseAndInfer prog of
    Left  err                -> IO.putStrLn err
    Right (TypedAST typ ast) ->
        case typ of
            SMeasure _ ->
                case determine (density ast) of
                  Just ast' -> print . pretty $ constantPropagation ast'
                  Nothing   -> error "No density found"
            _               -> error "Density is only available for measure terms"

