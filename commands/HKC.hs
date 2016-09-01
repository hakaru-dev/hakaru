{-# LANGUAGE GADTs,
             OverloadedStrings #-}

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

data Options =
 Options { debug    :: Bool
         , optimize :: Bool
         -- , accelerate :: Either CUDA OpenCL
         -- , jobs       :: Maybe Int
         , asFunc   :: Maybe String
         , fileIn   :: String
         , fileOut  :: Maybe String
         } deriving Show


main :: IO ()
main = do
  opts <- parseOpts
  prog <- readFromFile (fileIn opts)
  runReaderT (compileHakaru prog) opts

options :: Parser Options
options = Options
  <$> switch ( long "debug"
             <> short 'D'
             <> help "Prints Hakaru src, Hakaru AST, C AST, C src" )
  <*> switch ( long "optimize"
             <> short 'O'
             <> help "Performs constant folding on Hakaru AST" )
  <*> (optional $ strOption ( long "as-function"
                            <> short 'F'
                            <> help "Compiles to a sampling C function with the name ARG" ))
  <*> strArgument (metavar "INPUT" <> help "Program to be compiled")
  <*> (optional $ strOption (short 'o' <> metavar "OUTPUT" <> help "output FILE"))

parseOpts :: IO Options
parseOpts = execParser $ info (helper <*> options)
                       $ fullDesc <> progDesc "Compile Hakaru to C"

compileHakaru :: Text -> ReaderT Options IO ()
compileHakaru prog = ask >>= \config -> lift $ do
  case parseAndInfer prog of
    Left err -> IO.putStrLn err
    Right (TypedAST typ ast) -> do
      let ast'    = TypedAST typ $ if optimize config
                                   then constantPropagation ast
                                   else ast
          outPath = case fileOut config of
                      (Just f) -> f
                      Nothing  -> "-"
          output  = wrapProgram ast' (asFunc config)
      when (debug config) $ do
        putErrorLn hrule
        putErrorLn $ pack $ show ast
        when (optimize config) $ do
          putErrorLn hrule
          putErrorLn $ pack $ show ast'
        putErrorLn hrule
      writeToFile outPath output

  where hrule = "\n----------------------------------------------------------------\n"

putErrorLn :: Text -> IO ()
putErrorLn = IO.hPutStrLn stderr
