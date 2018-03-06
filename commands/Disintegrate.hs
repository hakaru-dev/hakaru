{-# LANGUAGE OverloadedStrings
           , PatternGuards
           , TypeOperators
           , DataKinds
           , GADTs
           , KindSignatures
           , FlexibleContexts
           , RankNTypes
           , CPP #-}

module Main where

import           Language.Hakaru.Pretty.Concrete
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST as AST

import           Language.Hakaru.Types.Sing
import           Language.Hakaru.Types.DataKind
import           Language.Hakaru.Disintegrate
import           Language.Hakaru.Evaluation.ConstantPropagation
import           Language.Hakaru.Command

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..), (<$>))
#endif

import           Data.Monoid
import           Control.Monad (when)
import qualified Data.Text as T
import qualified Data.Text.IO as IO
import           System.IO (stderr)

import           Options.Applicative as O

data Options = Options { total   :: Bool
                       , index   :: Int
                       , program :: String }

options :: Parser Options
options = Options
          <$> switch
              ( long "total" <>
                short 't' <>
                help "Whether to show the total number of disintegrations" )
          <*> option auto
              ( long "index" <>
                short 'i' <>
                metavar "INDEX" <>
                value 0 <>
                help "The index of the desired result in the list of disintegrations (default: 0)" )
          <*> strArgument
              ( metavar "PROGRAM" <>
                help "File containing program to disintegrate" )

parseOpts :: IO Options
parseOpts = execParser $ info (helper <*> options) $
            fullDesc <>
            progDesc "Disintegrate a Hakaru program" <>
            header
            "disintegrate: symbolic conditioning of probabilistic programs"

main :: IO ()
main = do
  args  <- parseOpts
  case args of
    Options t i infile -> do
      prog <- readFromFile infile
      runDisintegrate prog t i

runDisintegrate :: T.Text -> Bool -> Int -> IO ()
runDisintegrate prog showTotal i =
    case parseAndInfer prog of
    Left  err      -> IO.hPutStrLn stderr err
    Right typedAST -> go Nil1 typedAST
    where
      go :: List1 Variable (xs :: [Hakaru])
         -> TypedAST (TrivialABT AST.Term)
         -> IO ()
      go xs (TypedAST typ ast)
          = case typ of
              SMeasure (SData (STyCon sym `STyApp` _ `STyApp` _) _)
                  | Just Refl <- jmEq1 sym sSymbol_Pair
                     -> case disintegrate ast of
                          [] -> IO.hPutStrLn stderr
                                "No disintegration found"
                          rs -> when showTotal
                                (IO.hPutStrLn stderr.T.pack $
                                 "Number of disintegrations: " ++ show (length rs)) >>
                                lams xs (print.pretty.constantPropagation) (rs Prelude.!! i)
              SFun _ b ->
                caseVarSyn ast putErrorMsg $ \t ->
                case t of
                  Lam_ :$ body :* End ->
                      caseBind body $ \x e ->
                      go (append1 xs (Cons1 x Nil1)) (TypedAST b e)
                  _ -> putErrorMsg ast
              _ -> putErrorMsg ast
                   
putErrorMsg :: (Show a) => a -> IO ()
putErrorMsg _ = IO.hPutStrLn stderr . T.pack $
                "Can only disintegrate (functions over) measures over pairs"
                -- ++ "\nGiven\n" ++ show a

-- | Use a list of variables to wrap lambdas around a given term
lams :: (ABT AST.Term abt)
     => List1 Variable (xs :: [Hakaru])
     -> (forall b. abt '[] b -> IO ()) -> abt '[] a -> IO ()
lams Nil1         k = k
lams (Cons1 x xs) k = lams xs (k . lam_ x)
