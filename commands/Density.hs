{-# LANGUAGE OverloadedStrings, DataKinds, GADTs #-}

module Main where

import           Language.Hakaru.Pretty.Concrete
import           Language.Hakaru.Syntax.TypeCheck

import           Language.Hakaru.Types.Sing
import           Language.Hakaru.Disintegrate
import           Language.Hakaru.Evaluation.ConstantPropagation
import           Language.Hakaru.Command

import           Data.Text
import qualified Data.Text.IO as IO
import           System.IO (stderr)

import           System.Environment

main :: IO ()
main = do
  args  <- getArgs
  progs <- mapM readFromFile args
  case progs of
      [prog] -> runDensity prog
      _      -> IO.hPutStrLn stderr "Usage: density <file>"

runDensity :: Text -> IO ()
runDensity prog =
    case parseAndInfer prog of
    Left  err                -> IO.hPutStrLn stderr err
    Right (TypedAST typ ast) ->
        case typ of
            SMeasure _ ->
                case determine (density ast) of
                  Just ast' -> print . pretty $ constantPropagation ast'
                  Nothing   -> IO.hPutStrLn stderr "No density found"
            _               -> IO.hPutStrLn stderr "Density is only available for measure terms"

