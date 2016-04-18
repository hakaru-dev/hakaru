{-# LANGUAGE OverloadedStrings, DataKinds, GADTs #-}

module Main where

import qualified Language.Hakaru.Parser.AST as U
import           Language.Hakaru.Parser.Parser hiding (style)
import           Language.Hakaru.Parser.SymbolResolve (resolveAST)


import qualified Language.Hakaru.Syntax.AST as T
import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Syntax.Value

import           Language.Hakaru.Types.Sing

import           Language.Hakaru.Sample
import           Language.Hakaru.Pretty.Concrete

import           Control.Monad
import           Data.Text
import qualified Data.Text.IO as IO
import           Text.PrettyPrint

import qualified System.Random.MWC as MWC
import           System.Environment
import           System.Posix.Terminal

main :: IO ()
main = do
  args   <- getArgs
  g      <- MWC.createSystemRandom
  b      <- queryTerminal 0
  progs  <- mapM IO.readFile args
  progs' <- addStdin b progs
  case progs' of
      [prog] -> runHakaru g prog
      _      -> IO.putStrLn "Usage: hakaru <file>"

addStdin :: Bool -> [Text] -> IO [Text]
addStdin True  xs = return xs
addStdin False xs = do x <- IO.getContents
                       return (x:xs)

inferType' :: U.AST -> TypeCheckMonad (TypedAST (TrivialABT T.Term))
inferType' = inferType


illustrate :: Sing a -> MWC.GenIO -> Value a -> IO ()
illustrate (SMeasure s) g (VMeasure m) = do
    Just (samp,_) <- m (VProb 1) g
    illustrate s g samp
illustrate _ _ x =   putStrLn
                   . renderStyle style {mode = LeftMode}
                   . prettyValue $ x

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

