{-# LANGUAGE OverloadedStrings,
             DataKinds,
             GADTs,
             TypeOperators
             #-}

module Main where

import           Language.Hakaru.Parser.Parser (parseHakaru)
import           Language.Hakaru.Parser.SymbolResolve (resolveAST)


import qualified Language.Hakaru.Syntax.AST as T
import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Syntax.Value

import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Types.Sing
import           Language.Hakaru.Types.DataKind

import           Language.Hakaru.Sample
import           Language.Hakaru.Pretty.Concrete

import           Control.Monad

import           Data.Text
import qualified Data.Text.IO as IO
import           Text.PrettyPrint

import qualified System.Random.MWC as MWC
import           System.Environment

main :: IO ()
main = do
  args   <- getArgs
  g      <- MWC.createSystemRandom
  progs  <- mapM readFromFile args
  case progs of
      [prog1, prog2] -> randomWalk g prog1 prog2
      [prog] -> runHakaru g prog
      _      -> IO.putStrLn "Usage: hakaru <file>"

readFromFile :: String -> IO Text
readFromFile "-" = IO.getContents
readFromFile x   = IO.readFile x

parseAndInfer :: Text
              -> Either String (TypedAST (TrivialABT T.Term))
parseAndInfer x =
    case parseHakaru x of
    Left  err  -> Left (show err)
    Right past ->
        let m = inferType (resolveAST past) in
        runTCM m LaxMode

illustrate :: Sing a -> MWC.GenIO -> Value a -> IO ()
illustrate (SMeasure s) g (VMeasure m) = do
    x <- m (VProb 1) g
    case x of
      Just (samp, _) -> illustrate s g samp
      Nothing        -> illustrate (SMeasure s) g (VMeasure m)

illustrate _ _ x =   putStrLn
                   . renderStyle style {mode = LeftMode}
                   . prettyValue $ x

runHakaru :: MWC.GenIO -> Text -> IO ()
runHakaru g prog =
    case parseAndInfer prog of
      Left err                 -> putStrLn err
      Right (TypedAST typ ast) -> do
        case typ of
          SMeasure _ -> forever (illustrate typ g $ run ast)
          _          -> illustrate typ g $ run ast
    where
    run :: TrivialABT T.Term '[] a -> Value a
    run = runEvaluate

randomWalk ::MWC.GenIO -> Text -> Text -> IO ()
randomWalk g p1 p2 =
    case (parseAndInfer p1, parseAndInfer p2) of
      (Right (TypedAST typ1 ast1), Right (TypedAST typ2 ast2)) ->
          -- TODO: Use better error messages for type mismatch
          case (typ1, typ2) of
            (SFun a (SMeasure b), SMeasure c) ->
                case (jmEq1 a b, jmEq1 b c) of
                  (Just Refl, Just Refl) ->
                      iterateM_ (chain $ run ast1) (run ast2)
                  _ -> putStrLn "hakaru: programs have wrong type"
            _ -> putStrLn "hakaru: programs have wrong type"
      (Left err, _) -> print err
      (_, Left err) -> print err
    where
    run :: TrivialABT T.Term '[] a -> Value a
    run = runEvaluate

    chain :: Value (a ':-> b) -> Value ('HMeasure a) -> IO (Value b)
    chain (VLam f) (VMeasure m) = do
      Just (samp,_) <- m (VProb 1) g
      putStrLn . renderStyle style {mode = LeftMode}
               . prettyValue $ samp
      return (f samp)

-- From monad-loops
iterateM_ :: Monad m => (a -> m a) -> a -> m b
iterateM_ f = g
    where g x = f x >>= g

      
