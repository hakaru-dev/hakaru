{-# LANGUAGE OverloadedStrings, DataKinds, GADTs #-}

module Main where

import qualified Language.Hakaru.Parser.AST as U
import Language.Hakaru.Parser.Parser
import Language.Hakaru.Parser.SymbolResolve (resolveAST)


import qualified Language.Hakaru.Syntax.AST as T
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Syntax.Nat
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Types.Sing
import Language.Hakaru.Types.DataKind

import Language.Hakaru.Syntax.TypeCheck
import Language.Hakaru.Pretty.Concrete
import Language.Hakaru.Sample hiding (SData, SKonst, SEt, SDone, SPlus, SVoid)
import Language.Hakaru.Observe
import Language.Hakaru.Expect
import Language.Hakaru.Syntax.Prelude (prob_, fromProb, real_)
import Language.Hakaru.Simplify

import           Control.Monad
import           Data.Text
import qualified Data.Text.IO as IO
import           Text.PrettyPrint

import qualified System.Random.MWC as MWC
import           System.Environment

main :: IO ()
main = do
  args <- getArgs
  g    <- MWC.create
  case args of
      [prog] -> IO.readFile prog >>= runHakaru g
      _      -> IO.putStrLn "Usage: hakaru <file>"

inferType' :: U.AST a -> TypeCheckMonad (TypedAST (TrivialABT T.Term))
inferType' = inferType


illustrate :: Sing a -> MWC.GenIO -> Sample IO a -> IO ()
illustrate SNat  g x = print x
illustrate SInt  g x = print x
illustrate SProb g x = print x
illustrate SReal g x = print x
illustrate (SData _ _) g (SDatum d) = print d
illustrate (SMeasure s) g m = do
    Just (samp,_) <- m 1 g
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
            SMeasure _ -> forever (illustrate typ g . unS $ runSample' ast)
            _          -> illustrate typ g . unS $ runSample' ast
    where
    runSample' :: TrivialABT T.Term '[] a -> S IO a
    runSample' = runSample

