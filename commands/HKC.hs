{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}

module Main where

import Language.Hakaru.Evaluation.ConstantPropagation
import Language.Hakaru.Syntax.TypeCheck
import Language.Hakaru.Syntax.AST.Transforms (expandTransformations)
import Language.Hakaru.Syntax.ANF      (normalize)
import Language.Hakaru.Syntax.CSE      (cse)
import Language.Hakaru.Syntax.Prune    (prune)
import Language.Hakaru.Syntax.Uniquify (uniquify)
import Language.Hakaru.Syntax.Hoist    (hoist)
import Language.Hakaru.Summary
import Language.Hakaru.Command
import Language.Hakaru.CodeGen.Wrapper
import Language.Hakaru.CodeGen.CodeGenMonad
import Language.Hakaru.CodeGen.AST
import Language.Hakaru.CodeGen.Pretty

import           Control.Monad.Reader

import           Data.Monoid
import           Data.Maybe (isJust)
import           Data.Text hiding (any,map,filter,foldr)
import qualified Data.Text.IO as IO
import           Text.PrettyPrint (render)
import           Options.Applicative
import           System.IO
import           System.Process
import           System.Exit
import           Prelude hiding (concat)

data Options =
 Options { debug            :: Bool
         , optimize         :: Maybe Int
         , summaryOpt       :: Bool
         , make             :: Maybe String
         , asFunc           :: Maybe String
         , fileIn           :: String
         , fileOut          :: Maybe String
         , par              :: Bool -- turns on simd and sharedMem
         , noWeightsOpt     :: Bool
         , showProbInLogOpt :: Bool
         , garbageCollector :: Bool
         -- , logProbs         :: Bool
         } deriving Show


main :: IO ()
main = do
  opts <- parseOpts
  prog <- readFromFile (fileIn opts)
  runReaderT (compileHakaru prog) opts

options :: Parser Options
options = Options
  <$> switch (  long "debug"
             <> short 'D'
             <> help "Prints Hakaru src, Hakaru AST, C AST, C src" )
  <*> (optional $ option auto (  short 'O'
                              <> metavar "{0,1,2}"
                              <> help "perform Hakaru AST optimizations. optimization levels 0,1,2." ))
  <*> switch (  long "summary"
             <> short 'S'
             <> help "Performs summarization optimization" )
  <*> (optional $ strOption (  long "make"
                            <> short 'm'
                            <> help "Compiles generated C code with the compiler ARG"))
  <*> (optional $ strOption (  long "as-function"
                            <> short 'F'
                            <> help "Compiles to a sampling C function with the name ARG" ))
  <*> strArgument (  metavar "INPUT"
                  <> help "Program to be compiled")
  <*> (optional $ strOption (  short 'o'
                            <> metavar "OUTPUT"
                            <> help "output FILE"))
  <*> switch (  short 'j'
             <> help "Generates multithreaded and simd parallel programs using OpenMP directives")
  <*> switch (  long "no-weights"
             <> short 'w'
             <> help "Don't print the weights")
  <*> switch (  long "show-prob-log"
             <> help "Shows prob types as 'exp(<log-domain-value>)' instead of '<value>'")
  <*> switch (  long "garbage-collector"
             <> short 'g'
             <> help "Use Boehm Garbage Collector")
  -- <*> switch (  long "-no-log-space-probs"
  --            <> help "Do not log `prob` types; WARNING this is more likely to underflow.")

parseOpts :: IO Options
parseOpts = execParser $ info (helper <*> options)
                       $ fullDesc <> progDesc "Compile Hakaru to C"

compileHakaru :: Text -> ReaderT Options IO ()
compileHakaru prog = ask >>= \config -> lift $ do
  prog' <- parseAndInferWithDebug (debug config) prog
  case prog' of
    Left err -> IO.hPutStrLn stderr err
    Right (TypedAST typ ast) -> do
      astS <- case summaryOpt config of
                True  -> summary (expandTransformations ast)
                False -> return (expandTransformations ast)
      let ast'    = TypedAST typ $ foldr id astS (abtPasses $ optimize config)
          outPath = case fileOut config of
                      (Just f) -> f
                      Nothing  -> "-"
          codeGen = wrapProgram ast'
                                (asFunc config)
                                (PrintConfig { noWeights     = noWeightsOpt config
                                             , showProbInLog = showProbInLogOpt config })
          codeGenConfig = emptyCG { sharedMem = par config
                                  , simd      = par config
                                  , managedMem = garbageCollector config}
          cast    = CAST $ runCodeGenWith codeGen codeGenConfig
          output  = pack . render . pretty $ cast
      when (debug config) $ do
        putErrorLn $ hrule "Hakaru Type"
        putErrorLn . pack . show $ typ
        putErrorLn $ hrule "Hakaru AST"
        putErrorLn $ pack $ show ast
        when (isJust . optimize $ config) $ do
          putErrorLn $ hrule "Hakaru AST'"
          putErrorLn $ pack $ show ast'
        putErrorLn $ hrule "C AST"
        putErrorLn $ pack $ show cast
        putErrorLn $ hrule "Fin"
      case make config of
        Nothing -> writeToFile outPath output
        Just cc -> makeFile cc (fileOut config) (unpack output) config

  where hrule s = concat [ "\n<=======================| "
                         , s
                         ," |=======================>\n"]
        abtPasses Nothing  = []
        abtPasses (Just 0) = [ constantPropagation ]
        abtPasses (Just 1) = [ constantPropagation
                             , uniquify
                             , prune
                             , cse
                             , hoist
                             , uniquify ]
        abtPasses (Just 2) = abtPasses (Just 1) ++ [normalize]

        abtPasses _ = error "only optimization levels are 0, 1, and 2"

putErrorLn :: Text -> IO ()
putErrorLn = IO.hPutStrLn stderr


makeFile :: String -> Maybe String -> String -> Options -> IO ()
makeFile cc mout prog opts =
  do let p = proc cc $ ["-pedantic"
                       ,"-std=c99"
                       ,"-lm"
                       ,"-xc"
                       ,"-"]
                       ++ (case mout of
                            Nothing -> []
                            Just o  -> ["-o" ++ o])
                       ++ (if par opts then ["-fopenmp"] else [])
     (Just inH, _, _, pH) <- createProcess p { std_in    = CreatePipe
                                             , std_out   = CreatePipe }
     hPutStrLn inH prog
     hClose inH
     exit <- waitForProcess pH
     case exit of
       ExitSuccess -> return ()
       _           -> error $ cc ++ " returned exit code: " ++ show exit
