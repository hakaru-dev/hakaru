{-# LANGUAGE OverloadedStrings, DataKinds, GADTs #-}

module Main where

import qualified Language.Hakaru.Parser.AST as U
import           Language.Hakaru.Parser.Parser
import           Language.Hakaru.Parser.SymbolResolve (resolveAST)
import           Language.Hakaru.Pretty.Concrete  
import qualified Language.Hakaru.Syntax.AST as T
import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Syntax.IClasses

import           Language.Hakaru.Types.Sing
import           Language.Hakaru.Disintegrate
  
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

inferType' :: U.AST -> TypeCheckMonad (TypedAST (TrivialABT T.Term))
inferType' = inferType

runDisintegrate :: Text -> IO ()
runDisintegrate prog =
    case parseHakaru prog of
    Left  err  -> print err
    Right past ->
        let m = inferType' (resolveAST past) in
        case runTCM m LaxMode of
        Left err                 -> putStrLn err
        Right (TypedAST typ ast) -> do
          case typ of
            SMeasure _ ->
                case determine (disintegrate ast) of
                Nothing   -> error "No disintegration found"
                Just ast' -> print (pretty ast')
            _             -> error "Can only disintegrate a measure over pairs"

