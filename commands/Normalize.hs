{-# LANGUAGE OverloadedStrings, DataKinds, GADTs #-}

module Main where

import           Language.Hakaru.Pretty.Concrete  
import           Language.Hakaru.Syntax.AST.Transforms
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Types.Sing

import           Language.Hakaru.Expect (normalize)
import           Language.Hakaru.Evaluation.ConstantPropagation
import           Language.Hakaru.Command

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

runNormalize :: Text -> IO ()
runNormalize prog =
    case parseAndInfer prog of
    Left  err                -> putStrLn err
    Right (TypedAST typ ast) -> do
      case typ of
        SMeasure _          -> print . pretty . constantPropagation . normalize $ ast
        SFun _ (SMeasure _) -> print . pretty . runIdentity $
                                 underLam (return . constantPropagation . normalize) ast
        _                   -> error "Can only normalize measures"
