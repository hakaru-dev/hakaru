{-# LANGUAGE OverloadedStrings
           , PatternGuards
           , TypeOperators
           , DataKinds
           , GADTs
           , KindSignatures
           , FlexibleContexts
           , RankNTypes #-}

module Main where

import           Language.Hakaru.Pretty.Concrete
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST as T

import           Language.Hakaru.Types.Sing
import           Language.Hakaru.Types.DataKind
import           Language.Hakaru.Disintegrate
import           Language.Hakaru.Evaluation.ConstantPropagation
import           Language.Hakaru.Command

import           Data.Text
import qualified Data.Text.IO as IO
import           System.IO (stderr)

import           System.Environment

main :: IO ()
main = do
  args  <- getArgs
  progs <- mapM readFromFile args
  case progs of
      [prog] -> runDisintegrate prog
      _      -> IO.hPutStrLn stderr "Usage: disintegrate <file>"

runDisintegrate :: Text -> IO ()
runDisintegrate prog =
    case parseAndInfer prog of
    Left  err      -> IO.hPutStrLn stderr err
    Right typedAST -> go Nil1 typedAST
    where
      go :: List1 Variable (xs :: [Hakaru])
         -> TypedAST (TrivialABT T.Term)
         -> IO ()
      go xs (TypedAST typ ast)
          = case typ of
              SMeasure (SData (STyCon sym `STyApp` _ `STyApp` _) _)
                  | Just Refl <- jmEq1 sym sSymbol_Pair
                     -> case determine (disintegrate ast) of
                          Just ast' ->
                              lams xs (print.pretty.constantPropagation) ast'
                          Nothing   -> IO.hPutStrLn stderr
                                       "No disintegration found"
              SFun _ b ->
                caseVarSyn ast putErrorMsg $ \t ->
                case t of
                  Lam_ :$ body :* End ->
                      caseBind body $ \x e ->
                      go (append1 xs (Cons1 x Nil1)) (TypedAST b e)
                  _ -> putErrorMsg ast
              _ -> putErrorMsg ast
                   
putErrorMsg :: (Show a) => a -> IO ()
putErrorMsg a = IO.hPutStrLn stderr . pack $
                "Can only disintegrate (functions over) measures over pairs"
                ++ "\nGiven\n" -- ++ show a
                
              
lams :: (ABT T.Term abt)
     => List1 Variable (xs :: [Hakaru])
     -> (forall a. abt '[] a -> IO ()) -> abt '[] a -> IO ()
lams Nil1         k = k
lams (Cons1 x xs) k = lams xs (k . lam_ x)
