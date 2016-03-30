{-# LANGUAGE OverloadedStrings, DataKinds, GADTs #-}

module Main where

import qualified Language.Hakaru.Parser.AST as U
import           Language.Hakaru.Parser.Parser
import           Language.Hakaru.Parser.SymbolResolve (resolveAST)
import           Language.Hakaru.Pretty.Concrete  
import qualified Language.Hakaru.Syntax.AST as T
import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.TypeCheck

import           Language.Hakaru.Simplify
  
import           Data.Text
import qualified Data.Text.IO as IO

import           System.Environment

main :: IO ()
main = do
  args <- getArgs
  case args of
      [prog] -> IO.readFile prog >>= runSimplify
      []     -> IO.getContents   >>= runSimplify
      _      -> IO.putStrLn "Usage: simplify <file>"

inferType' :: U.AST -> TypeCheckMonad (TypedAST (TrivialABT T.Term))
inferType' = inferType

runSimplify :: Text -> IO ()
runSimplify prog =
    case parseHakaru prog of
    Left  err  -> print err
    Right past ->
        let m = inferType' (resolveAST past) in
        case runTCM m LaxMode of
        Left err                 -> putStrLn err
        Right (TypedAST typ ast) -> simplify    ast >>= print . pretty

