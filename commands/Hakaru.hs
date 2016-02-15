{-# LANGUAGE OverloadedStrings, DataKinds, GADTs #-}

module Main where

import qualified Language.Hakaru.Parser.AST as U
import           Language.Hakaru.Parser.Parser
import           Language.Hakaru.Parser.SymbolResolve (resolveAST)


import qualified Language.Hakaru.Syntax.AST as T
import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Syntax.Datum
import           Language.Hakaru.Syntax.Value
import           Language.Hakaru.Syntax.IClasses

import           Language.Hakaru.Types.Sing

import           Language.Hakaru.Sample
import           Language.Hakaru.Pretty.Concrete

import           Control.Monad
import           Data.Text hiding (intercalate)
import qualified Data.Text.IO as IO
import           Data.List (intercalate)

import qualified System.Random.MWC as MWC
import           System.Environment

main :: IO ()
main = do
  args <- getArgs
  g    <- MWC.create
  case args of
      [prog] -> IO.readFile prog >>= runHakaru g
      []     -> IO.getContents   >>= runHakaru g
      _      -> IO.putStrLn "Usage: hakaru <file>"

inferType' :: U.AST -> TypeCheckMonad (TypedAST (TrivialABT T.Term))
inferType' = inferType


illustrate :: Sing a -> MWC.GenIO -> Value a -> IO ()
illustrate SNat  _ x = print x
illustrate SInt  _ x = print x
illustrate SProb _ x = print x
illustrate SReal _ x = print x
illustrate (SData _ _) _ v@(VDatum (Datum hint d)) =
    case unpack hint of
      "pair"  -> putStrLn ("(" ++ intercalate ", "
                                   (foldMap11 ((:[]) . show) d) ++ ")")
      "true"  -> putStrLn "true"
      "false" -> putStrLn "false"
      _       -> print v
illustrate (SMeasure s) g (VMeasure m) = do
    Just (samp,_) <- m (VProb 1) g
    illustrate s g samp
illustrate s _ _ = putStrLn ("<" ++ show s ++ ">")

runHakaru :: MWC.GenIO -> Text -> IO ()
runHakaru g prog =
    case parseHakaru prog of
    Left  err  -> print err
    Right past ->
        let m = inferType' (resolveAST past) in
        case runTCM m LaxMode of
        Left err                 -> putStrLn err
        Right (TypedAST typ ast) -> do
          case typ of
            SMeasure _ -> forever (illustrate typ g $ run ast)
            _          -> illustrate typ g $ run ast
    where
    run :: TrivialABT T.Term '[] a -> Value a
    run = runEvaluate

