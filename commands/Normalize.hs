{-# LANGUAGE OverloadedStrings, DataKinds, GADTs #-}

module Main where

import qualified Language.Hakaru.Parser.AST as U
import           Language.Hakaru.Parser.Parser
import           Language.Hakaru.Parser.SymbolResolve (resolveAST)
import           Language.Hakaru.Pretty.Concrete  
import qualified Language.Hakaru.Syntax.AST as T
import           Language.Hakaru.Syntax.AST.Transforms
import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Types.Sing

import           Language.Hakaru.Expect (normalize)

import           Data.Text
import qualified Data.Text.IO as IO
import           Control.Monad.Identity

import           System.Environment

main :: IO ()
main = do
  args <- getArgs
  case args of
      [prog] -> IO.readFile prog >>= runNormalize
      []     -> IO.getContents   >>= runNormalize
      _      -> IO.putStrLn "Usage: normalize <file>"

inferType' :: U.AST -> TypeCheckMonad (TypedAST (TrivialABT T.Term))
inferType' = inferType

runNormalize :: Text -> IO ()
runNormalize prog =
    case parseHakaru prog of
    Left  err  -> print err
    Right past ->
        let m = inferType' (resolveAST past) in
        case runTCM m LaxMode of
        Left err                 -> putStrLn err
        Right (TypedAST typ ast) -> do
          case typ of
            SMeasure _          -> print . pretty . normalize $ ast
            SFun _ (SMeasure _) -> print . pretty . runIdentity $
                                    underLam (return . normalize) ast
            _                   -> error "Can only normalize measures"
