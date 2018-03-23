{-# LANGUAGE OverloadedStrings
           , PatternGuards
           , DataKinds
           , GADTs
           , KindSignatures
           , RankNTypes
           , TypeOperators
           , FlexibleContexts #-}

module Main where

import           Language.Hakaru.Pretty.Concrete  
import           Language.Hakaru.Syntax.TypeCheck

import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Syntax.ABT (ABT(..), dupABT)
import           Language.Hakaru.Syntax.AST (Term(..), Transform(..))
import           Language.Hakaru.Syntax.AST.Transforms (expandTransformations)
import qualified Language.Hakaru.Parser.AST as U
import           Language.Hakaru.Command hiding (Term)
  
import           Data.Text
import qualified Data.Text.IO as IO
import           System.IO (stderr)

import           System.Environment

main :: IO ()
main = do
  args  <- getArgs
  progs <- mapM readFromFile args
  case progs of
      [prog2, prog1] -> runMH prog1 prog2
      _              -> IO.hPutStrLn stderr "Usage: mh <target> <proposal>"

runMH :: Text -> Text -> IO ()
runMH prog1 prog2 =
    case (parseAndInfer prog1, parseAndInfer prog2) of
      (Right (TypedAST _ ast1), Right (TypedAST _ ast2)) ->
         either (IO.hPutStrLn stderr)
                (elimTypedAST $ \_ -> print . pretty) $
         runMH' ast1 ast2
      (Left err, _) -> IO.hPutStrLn stderr err
      (_, Left err) -> IO.hPutStrLn stderr err

runMH' :: (ABT Term abt)
       => abt '[] a
       -> abt '[] b
       -> Either Text (TypedAST abt)
runMH' prop tgt =
  let uast = syn $ U.Transform_ MCMC $
               (Nil2, syn $ U.InjTyped $ dupABT prop) U.:*
               (Nil2, syn $ U.InjTyped $ dupABT tgt ) U.:* U.End
  in do TypedAST rty res <- runTCM (inferType uast) Nothing LaxMode
        return $ TypedAST rty $ expandTransformations res
