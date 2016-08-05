{-# LANGUAGE CPP, OverloadedStrings, DataKinds, GADTs #-}

module Main where

import           Language.Hakaru.Pretty.Concrete  
import           Language.Hakaru.Syntax.AST.Transforms
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Command (parseAndInfer, readFromFile, Term)

import           Language.Hakaru.Simplify

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..), (<$>))
#endif

import           Data.Text
import qualified Data.Text.IO as IO

import qualified Options.Applicative as O

data Options = Options
  { debug   :: Bool
  , program :: String }

options :: O.Parser Options
options = Options
  <$> O.switch
      ( O.long "debug" O.<>
        O.help "Prints output that is sent to Maple" )
  <*> O.strArgument
      ( O.metavar "PROGRAM" O.<> 
        O.help "Program to be simplified" )

parseOpts :: IO Options
parseOpts = O.execParser $ O.info (O.helper <*> options)
      (O.fullDesc O.<> O.progDesc "Simplify a hakaru program")

et :: Term a -> Term a
et = expandTransformations

main :: IO ()
main = do
  args <- parseOpts
  case args of
   Options debug_ file -> do
    prog <- readFromFile file
    runSimplify prog debug_

runSimplify :: Text -> Bool -> IO ()
runSimplify prog debug_ =
    case parseAndInfer prog of
    Left  err              -> IO.putStrLn err
    Right (TypedAST _ ast) -> simplifyDebug debug_ (et ast) >>= print . pretty

