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
  , program   :: FilePath 
  }

options :: O.Parser Options
options = Options
  <$> O.switch
      ( O.short 't' <>
        O.long "print-type" <>
        O.help "Print the type of the program as well." )
  <*> O.strArgument
      ( O.metavar "PROGRAM" <> 
        O.help "Filename containing program to be printed, or \"-\" to read from input." ) 

parseOpts :: IO Options
parseOpts = O.execParser $ O.info (O.helper <*> options)
      (O.fullDesc <> O.progDesc "Parse, typecheck, and print (in internal syntax) a Hakaru program")

main :: IO ()
main = parseOpts >>= runPretty 

runPretty :: Options -> IO ()
runPretty Options{..} = readFromFile' program >>= parseAndInfer' >>= \prog ->
    case prog of
    Left  err               -> IO.hPutStrLn stderr err
    Right (TypedAST ty ast) -> IO.putStrLn $
      -- TODO: prettier (than `show') printing of internal syntax
      (if printType then \x ->
          T.concat [ "(", x, ")"
                   , "\n.\n" <> T.pack (show ty) ]
       else id)
      (T.pack $ show $ expandTransformations ast)
