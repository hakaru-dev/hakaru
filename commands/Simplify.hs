{-# LANGUAGE CPP, OverloadedStrings, DataKinds, GADTs, RecordWildCards #-}

module Main where

import           Language.Hakaru.Pretty.Concrete  
import           Language.Hakaru.Syntax.AST.Transforms
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Command (parseAndInfer, readFromFile, Term)

import           Language.Hakaru.Syntax.Rename
import           Language.Hakaru.Simplify

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..), (<$>))
#endif

import           Data.Monoid
import           Data.Text
import qualified Data.Text.IO as IO
import           System.IO (stderr)

import qualified Options.Applicative as O

data Options a = Options
  { debug      :: Bool
  , timelimit  :: Int
  , no_unicode :: Bool
  , program    :: a }

options :: O.Parser (Options FilePath)
options = Options
  <$> O.switch
      ( O.long "debug" <>
        O.help "Prints output that is sent to Maple" )
  <*> O.option O.auto
      ( O.long "timelimit" <>
        O.help "Set simplify to timeout in N seconds" <>
        O.showDefault <>
        O.value 90 <>
        O.metavar "N")
  <*> O.switch 
      ( O.long "no-unicode" <> 
        O.short 'u' <> 
        O.help "Removes unicode characters from names in the Maple output")
  <*> O.strArgument
      ( O.metavar "PROGRAM" <> 
        O.help "Program to be simplified" )

parseOpts :: IO (Options FilePath)
parseOpts = O.execParser $ O.info (O.helper <*> options)
      (O.fullDesc <> O.progDesc "Simplify a hakaru program")

et :: Term a -> Term a
et = expandTransformations

main :: IO ()
main = do
  args <- parseOpts
  prog <- readFromFile (program args) 
  runSimplify args{program=prog}

runSimplify :: Options Text -> IO ()
runSimplify Options{..} =
    case parseAndInfer program of
    Left  err              -> IO.hPutStrLn stderr err
    Right (TypedAST _ ast) -> do ast' <- simplifyDebug debug timelimit (et ast)
                                 print $ pretty 
                                  $ (if no_unicode then renameAST removeUnicodeChars else id) 
                                  $ ast' 

