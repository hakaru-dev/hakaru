{-# LANGUAGE OverloadedStrings, PatternGuards, DataKinds, GADTs #-}

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
import           System.IO (stderr)

import           System.Environment

main :: IO ()
main = do
  args  <- getArgs
  progs <- mapM readFromFile args
  case progs of
      [prog] -> runDisintegrate prog
      _      -> IO.hPutStrLn stderr "Usage: disintegrate <file>"

runDisintegrate :: Text -> IO ()
runDisintegrate prog =
    case parseAndInfer prog of
    Left  err                -> IO.hPutStrLn stderr err
    Right (TypedAST typ ast) ->
        case typ of
          SMeasure (SData (STyCon sym `STyApp` _ `STyApp` _) _)
            | Just Refl <- jmEq1 sym sSymbol_Pair
            -> case determine (disintegrate ast) of
               Just ast' -> print . pretty $ constantPropagation ast'
               Nothing   -> IO.hPutStrLn stderr "No disintegration found"
          _ -> IO.hPutStrLn stderr "Can only disintegrate a measure over pairs"

