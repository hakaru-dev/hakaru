{-# LANGUAGE OverloadedStrings #-}

module Main where

import Language.Hakaru.Evaluation.ConstantPropagation
import Language.Hakaru.Syntax.TypeCheck
import Language.Hakaru.Command
import Language.Hakaru.CodeGen.Wrapper

import           Control.Monad.Reader
import           Data.Text hiding (any,map,filter)
import qualified Data.Text.IO as IO
import           Options.Applicative
import           System.IO (stderr)

data Options = Options { debug    :: Bool
                       , optimize :: Bool
                       , file     :: String } deriving Show

main :: IO ()
main = do
  opts <- parseOpts
  prog <- readFromFile (file opts)
  runReaderT (compileHakaru prog) opts

options :: Parser Options
options = Options
  <$> switch ( long "debug"
             <> short 'D'
             <> help "Prints Hakaru src, Hakaru AST, C AST, C src" )
  <*> switch ( long "optimize"
             <> short 'O'
             <> help "Performs constant folding on Hakaru AST" )
  <*> strArgument (metavar "PROGRAM" <> help "Program to be compiled")

parseOpts :: IO Options
parseOpts = execParser $ info (helper <*> options)
                       $ fullDesc <> progDesc "Compile Hakaru to C"

compileHakaru :: Text -> ReaderT Options IO ()
compileHakaru prog = ask >>= \config -> lift $ do
  case parseAndInfer prog of
    Left err -> putStrLn err
    Right (TypedAST typ ast) -> do
      let ast' = TypedAST typ (if optimize config
                               then constantPropagation ast
                               else ast)
      when (debug config) $ do
        putErrorLn "\n<=====================AST==========================>\n"
        putErrorLn $ pack $ show ast
        when (optimize config) $ do
          putErrorLn "\n<=================Constant Prop====================>\n"
          putErrorLn $ pack $ show ast'
        putErrorLn "\n<==================================================>\n"
      IO.putStrLn $ createProgram ast'

putErrorLn :: Text -> IO ()
putErrorLn = IO.hPutStrLn stderr
