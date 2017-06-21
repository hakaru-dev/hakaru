{-# LANGUAGE OverloadedStrings, DataKinds, GADTs, CPP, RecordWildCards #-}

module Main where

import           Language.Hakaru.Pretty.Concrete
import           Language.Hakaru.Syntax.AST.Transforms
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Command

import           Data.Text (Text)
import qualified Data.Text as T 
import qualified Data.Text.Utf8 as IO
import           System.IO (stderr)
import           Data.Monoid

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..), (<$>), (<*>))
#endif
import qualified Options.Applicative as O

data Options = Options
  { printType :: Bool 
  , internal  :: Bool 
  , program   :: FilePath 
  }

options :: O.Parser Options
options = Options
  <$> O.switch
      ( O.short 't' <>
        O.long "print-type" <>
        O.help "Annotate the program with its type." )
  <*> O.switch
      ( O.short 'i' <>
        O.long "internal-syntax" <>
        O.help "Print the program in internal Haskell syntax instead of in concrete syntax." )
  <*> O.strArgument
      ( O.metavar "PROGRAM" <> 
        O.help "Filename containing program to be pretty printed, or \"-\" to read from input." ) 

parseOpts :: IO Options
parseOpts = O.execParser $ O.info (O.helper <*> options)
      (O.fullDesc <> O.progDesc "Parse, typecheck, and pretty print a Hakaru program")

main :: IO ()
main = parseOpts >>= runPretty 

runPretty :: Options -> IO ()
runPretty Options{..} = readFromFile program >>= \prog -> 
    case parseAndInfer prog of
    Left  err               -> IO.hPutStrLn stderr err
    Right (TypedAST ty ast) -> IO.putStrLn $
      (if printType then \x -> T.concat [ "(", x, ")", "\n.\n" <> T.pack ((if internal then show else show . prettyType 12) ty) ] else id)
      (T.pack . (if internal then show else show.pretty) . expandTransformations . normalizeLiterals $ ast)

