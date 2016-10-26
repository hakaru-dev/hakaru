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
import           System.IO (stderr)

import           System.Environment

main :: IO ()
main = do
  args <- getArgs
  case args of
      [prog] -> IO.readFile prog >>= runNormalize
      []     -> IO.getContents   >>= runNormalize
      _      -> IO.hPutStrLn stderr "Usage: normalize <file>"

runNormalize :: Text -> IO ()
runNormalize prog = either (IO.hPutStrLn stderr) print $ do
  TypedAST typ ast <- parseAndInfer prog
  res <- normalizeUnderLams typ ast
  return (pretty res)

normalizeUnderLams :: Sing a -> Term a -> Either Text (Term a)
normalizeUnderLams (SMeasure _) ast = Right . constantPropagation . normalize $ ast
normalizeUnderLams (SFun _ typ) ast = underLam (normalizeUnderLams typ) ast
normalizeUnderLams _            _   = Left "Can only normalize measures"
