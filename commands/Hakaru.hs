{-# LANGUAGE OverloadedStrings,
             PatternGuards,
             DataKinds,
             GADTs,
             TypeOperators
             #-}

module Main where

import           Language.Hakaru.Syntax.AST.Transforms
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Syntax.Value

import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Types.Sing
import           Language.Hakaru.Types.DataKind

import           Language.Hakaru.Sample
import           Language.Hakaru.Pretty.Concrete
import           Language.Hakaru.Command ( parseAndInfer, parseAndInfer'
                                         , readFromFile, Term)

import           Control.Monad

import           Data.Text
import qualified Data.Text.IO as IO
import           System.IO (stderr)
import           Text.PrettyPrint (renderStyle, style, mode, Mode(LeftMode))

import qualified System.Random.MWC as MWC
import           System.Environment

main :: IO ()
main = do
  args   <- getArgs
  g      <- MWC.createSystemRandom
  progs  <- mapM readFromFile args
  case progs of
      [prog1, prog2] -> randomWalk' g prog1 prog2
      [prog]         -> runHakaru'  g prog
      _              -> IO.hPutStrLn stderr
                          "Usage: hakaru <file>\n\
                          \     | hakaru <transition_kernel> <initial_measure>"

illustrate :: Sing a -> MWC.GenIO -> Value a -> IO ()
illustrate (SMeasure s) g (VMeasure m) = do
    x <- m (VProb 1) g
    case x of
      Just (samp, _) -> illustrate s g samp
      Nothing        -> illustrate (SMeasure s) g (VMeasure m)

illustrate _ _ x = render x

render :: Value a -> IO ()
render = putStrLn . renderStyle style {mode = LeftMode} . prettyValue

runHakaru :: MWC.GenIO -> Text -> IO ()
runHakaru g prog =
    case parseAndInfer prog of
      Left err                 -> IO.hPutStrLn stderr err
      Right (TypedAST typ ast) -> do
        case typ of
          SMeasure _ -> forever (illustrate typ g $ run ast)
          _          -> illustrate typ g $ run ast
    where
    run :: Term a -> Value a
    run = runEvaluate . expandTransformations

runHakaru' :: MWC.GenIO -> Text -> IO ()
runHakaru' g prog = do
    prog' <- parseAndInfer' prog
    case prog' of
      Left err                 -> IO.hPutStrLn stderr err
      Right (TypedAST typ ast) -> do
        case typ of
          SMeasure _ -> forever (illustrate typ g $ run ast)
          _          -> illustrate typ g $ run ast
    where
    run :: Term a -> Value a
    run = runEvaluate . expandTransformations

randomWalk ::MWC.GenIO -> Text -> Text -> IO ()
randomWalk g p1 p2 =
    case (parseAndInfer p1, parseAndInfer p2) of
      (Right (TypedAST typ1 ast1), Right (TypedAST typ2 ast2)) ->
          -- TODO: Use better error messages for type mismatch
          case (typ1, typ2) of
            (SFun a (SMeasure b), SMeasure c)
              | (Just Refl, Just Refl) <- (jmEq1 a b, jmEq1 b c)
              -> iterateM_ (chain $ run ast1) (run ast2)
            _ -> IO.hPutStrLn stderr "hakaru: programs have wrong type"
      (Left err, _) -> IO.hPutStrLn stderr err
      (_, Left err) -> IO.hPutStrLn stderr err
    where
    run :: Term a -> Value a
    run = runEvaluate . expandTransformations

    chain :: Value (a ':-> b) -> Value ('HMeasure a) -> IO (Value b)
    chain (VLam f) (VMeasure m) = do
      Just (samp,_) <- m (VProb 1) g
      render samp
      return (f samp)

randomWalk' ::MWC.GenIO -> Text -> Text -> IO ()
randomWalk' g p1 p2 = do
    p1' <- parseAndInfer' p1
    p2' <- parseAndInfer' p2
    case (p1', p2') of
      (Right (TypedAST typ1 ast1), Right (TypedAST typ2 ast2)) ->
          -- TODO: Use better error messages for type mismatch
          case (typ1, typ2) of
            (SFun a (SMeasure b), SMeasure c)
              | (Just Refl, Just Refl) <- (jmEq1 a b, jmEq1 b c)
              -> iterateM_ (chain $ run ast1) (run ast2)
            _ -> IO.hPutStrLn stderr "hakaru: programs have wrong type"
      (Left err, _) -> IO.hPutStrLn stderr err
      (_, Left err) -> IO.hPutStrLn stderr err
    where
    run :: Term a -> Value a
    run = runEvaluate . expandTransformations

    chain :: Value (a ':-> b) -> Value ('HMeasure a) -> IO (Value b)
    chain (VLam f) (VMeasure m) = do
      Just (samp,_) <- m (VProb 1) g
      render samp
      return (f samp)

-- From monad-loops
iterateM_ :: Monad m => (a -> m a) -> a -> m b
iterateM_ f = g
    where g x = f x >>= g
