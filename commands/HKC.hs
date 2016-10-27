{-# LANGUAGE GADTs,
             OverloadedStrings #-}

module Main where

import Language.Hakaru.Evaluation.ConstantPropagation
import Language.Hakaru.Syntax.TypeCheck
import Language.Hakaru.Syntax.AST.Transforms (expandTransformations)
import Language.Hakaru.Command
import Language.Hakaru.CodeGen.Wrapper
import Language.Hakaru.CodeGen.CodeGenMonad
import Language.Hakaru.CodeGen.AST
import Language.Hakaru.CodeGen.Pretty

import           Control.Monad.Reader
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
         , optimize         :: Bool
         , make             :: Maybe String
         , asFunc           :: Maybe String
         , fileIn           :: String
         , fileOut          :: Maybe String
         , par              :: Bool
         , showWeightsOpt   :: Bool
         , showProbInLogOpt :: Bool
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
  <*> switch (  long "optimize"
             <> short 'O'
             <> help "Performs constant folding on Hakaru AST" )
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
             <> help "Generates parallel programs using OpenMP directives")
  <*> switch (  long "show-weights"
             <> short 'w'
             <> help "Shows the weights along with the samples in samplers")
  <*> switch (  long "show-prob-log"
             <> help "Shows prob types as 'exp(<log-domain-value>)' instead of '<value>'")

parseOpts :: IO Options
parseOpts = execParser $ info (helper <*> options)
                       $ fullDesc <> progDesc "Compile Hakaru to C"

compileHakaru :: Text -> ReaderT Options IO ()
compileHakaru prog = ask >>= \config -> lift $ do
  case parseAndInfer prog of
    Left err -> IO.hPutStrLn stderr err
    Right (TypedAST typ ast) -> do
      let ast'    = TypedAST typ $ foldr id ast abtPasses
          outPath = case fileOut config of
                      (Just f) -> f
                      Nothing  -> "-"
          codeGen = wrapProgram ast'
                                (asFunc config)
                                (PrintConfig { showWeights   = showWeightsOpt config
                                             , showProbInLog = showProbInLogOpt config })
          cast    = CAST $ runCodeGenWith codeGen (emptyCG {parallel = par config})
          output  = pack . render . pretty $ cast
      when (debug config) $ do
        putErrorLn $ hrule "Hakaru Type"
        putErrorLn . pack . show $ typ
        when (optimize config) $ do
          putErrorLn $ hrule "Hakaru AST"
          putErrorLn $ pack $ show ast
        putErrorLn $ hrule "Hakaru AST'"
        putErrorLn $ pack $ show ast
        putErrorLn $ hrule "C AST"
        putErrorLn $ pack $ show cast
        putErrorLn $ hrule "Fin"
      case make config of
        Nothing -> writeToFile outPath output
        Just cc -> makeFile cc (fileOut config) (unpack output) config

  where hrule s = concat ["\n<=======================| "
                         ,s," |=======================>\n"]
        abtPasses = [ expandTransformations
                    , constantPropagation ]

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
