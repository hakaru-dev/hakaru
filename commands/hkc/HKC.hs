{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Main where

import Language.Hakaru.Parser.Parser hiding (style)
import Language.Hakaru.Parser.SymbolResolve (resolveAST)
import Language.Hakaru.Syntax.TypeCheck
import Language.Hakaru.Evaluation.ConstantPropagation

import           Language.Hakaru.Syntax.ABT
import qualified Language.Hakaru.Syntax.AST as T

import HKC.CodeGen

import Control.Monad.Reader
import Data.Text hiding (any,map,filter)
import qualified Data.Text.IO as IO
import System.Environment

data Config = DEBUG | DEFAULT deriving (Show,Eq)

main :: IO ()
main = do
  args   <- getArgs
  let (files,config) = parseArgs args
  progs  <- mapM readFromFile files
  case progs of
      [prog] -> runReaderT (compileHakaru prog) config
      _      -> IO.putStrLn "Usage: hkc <input> <output>"

readFromFile :: String -> IO Text
readFromFile "-" = IO.getContents
readFromFile x   = IO.readFile x

parseArgs :: [String] -> ([FilePath],Config)
parseArgs input = (filter (not . debugState) input
                  , if any debugState input
                    then DEBUG
                    else DEFAULT)
  where debugState = (== "-D")


-- TODO: parseAndInfer has been copied to hkc, compile, and hakaru commands
parseAndInfer :: Text
              -> Either String (TypedAST (TrivialABT T.Term))
parseAndInfer x =
    case parseHakaru x of
    Left  err  -> Left (show err)
    Right past ->
        let m = inferType (resolveAST past) in
        runTCM m LaxMode

compileHakaru :: Text -> ReaderT Config IO ()
compileHakaru prog = ask >>= \config -> lift $ do
  case parseAndInfer prog of
    Left err -> putStrLn $ show err
    Right (TypedAST typ ast) -> do
      let ast' = TypedAST typ (constantPropagation ast)
      when (config == DEBUG) $ do
        IO.putStrLn "\n<=====================AST==========================>\n"
        IO.putStrLn $ pack $ show ast
        IO.putStrLn "\n<=================Constant Prop====================>\n"
        IO.putStrLn $ pack $ show ast'
        IO.putStrLn "\n<======================C===========================>\n"
      IO.putStrLn $ createProgram ast'
