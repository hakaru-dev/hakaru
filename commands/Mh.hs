{-# LANGUAGE OverloadedStrings, DataKinds, GADTs #-}

module Main where

import           Language.Hakaru.Pretty.Concrete  
import           Language.Hakaru.Syntax.TypeCheck

import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Types.Sing
import           Language.Hakaru.Inference
import           Language.Hakaru.Command
  
import           Data.Text
import qualified Data.Text.IO as IO

import           System.Environment

main :: IO ()
main = do
  args  <- getArgs
  progs <- mapM readFromFile args
  case progs of
      [prog2, prog1] -> runMH prog1 prog2
      _              -> IO.putStrLn "Usage: mh <target> <proposal>"

runMH :: Text -> Text -> IO ()
runMH prog1 prog2 =
    case (parseAndInfer prog1, parseAndInfer prog2) of
      (Right (TypedAST typ1 ast1), Right (TypedAST typ2 ast2)) ->
          -- TODO: Use better error messages for type mismatch
          case (typ1, typ2) of
            (SFun a (SMeasure b), SMeasure c) ->
                case (jmEq1 a b, jmEq1 b c) of
                  (Just Refl, Just Refl) ->
                      print . pretty $ mcmc ast1 ast2
                  _ -> putStrLn "mh: programs have wrong type"
            _ -> putStrLn "mh: programs have wrong type"
      (Left err, _) -> print err
      (_, Left err) -> print err
