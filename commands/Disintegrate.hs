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
  args <- getArgs
  case args of
      [prog] -> IO.readFile prog >>= runDisintegrate
      []     -> IO.getContents   >>= runDisintegrate
      _      -> IO.putStrLn "Usage: simplify <file>"

runDisintegrate :: Text -> IO ()
runDisintegrate prog =
    case parseAndInfer prog of
    Left  err                -> IO.putStrLn err
    Right (TypedAST typ ast) ->
        case typ of
            SMeasure (SData (STyCon sym `STyApp` _ `STyApp` _) _) ->
                case jmEq1 sym sSymbol_Pair of
                Just Refl ->
                    case determine (disintegrate ast) of
                    Just ast' -> print . pretty $ constantPropagation ast'
                    Nothing   -> error "No disintegration found"
                Nothing   -> error "Can only disintegrate a measure over pairs"
            _               -> error "Can only disintegrate a measure over pairs"

