{-# LANGUAGE CPP, OverloadedStrings, DataKinds, GADTs #-}

module Main where

import           Language.Hakaru.Pretty.SExpression
import           Language.Hakaru.Syntax.AST.Transforms
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Command
import           Language.Hakaru.Summary

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..), (<$>))
#endif

import           Data.Monoid
import           Data.Text
import qualified Data.Text.IO as IO
import           System.IO (stderr)

import qualified Options.Applicative as O

import           System.Environment

data Options = Options
  { opt :: Bool
  , program :: String}

options :: O.Parser Options
options = Options
  <$> O.switch
      ( O.long "opt" <>
        O.help "enables summary optimization for sexpr printer" )
  <*> O.strArgument
      ( O.metavar "PROGRAM" <>
        O.help "Program to be pretty printed")

parseOpts :: IO Options
parseOpts = O.execParser $ O.info (O.helper <*> options)
  (O.fullDesc <> O.progDesc "Pretty print a hakaru program in S-expression")

main :: IO ()
main = do
  args <- parseOpts
  case args of
    Options opt program -> do
      IO.readFile program >>= runPretty opt

runPretty :: Bool -> Text-> IO ()
runPretty opt prog =
    case parseAndInfer prog of
    Left  err              -> IO.hPutStrLn stderr err
    Right (TypedAST _ ast) -> do
      ast' <-  summary . expandTransformations $ ast
      print . pretty $ ast'
