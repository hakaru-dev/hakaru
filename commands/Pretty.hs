{-# LANGUAGE OverloadedStrings
           , DataKinds
           , GADTs
           , CPP
           , RecordWildCards
           #-}

module Main where

import           Language.Hakaru.Pretty.Concrete
import           Language.Hakaru.Syntax.AST.Transforms
import           Language.Hakaru.Syntax.Transform (Transform(..)
                                                  ,someTransformations)
import           Language.Hakaru.Syntax.IClasses (Some2(..))
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Command

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
  , toExpand  :: [Some2 Transform]
  }

options :: O.Parser Options
options = Options
  <$> O.switch
      ( O.short 't' <>
        O.long "print-type" <>
        O.help "Annotate the program with its type." )
  <*> O.strArgument
      ( O.metavar "PROGRAM" <> 
        O.help "Filename containing program to be pretty printed, or \"-\" to read from input." ) 
  <*> O.option O.auto
      ( O.short 'e' <>
        O.long "to-expand" <>
        O.value [Some2 Expect, Some2 Observe] <>
        O.help "Transformations to be expanded; default [Expect, Observe]" )

parseOpts :: IO Options
parseOpts = O.execParser $ O.info (O.helper <*> options)
      (O.fullDesc <> O.progDesc "Parse, typecheck, and pretty print a Hakaru program")

main :: IO ()
main = parseOpts >>= runPretty 

runPretty :: Options -> IO ()
runPretty Options{..} = readFromFile' program >>= parseAndInfer' >>= \prog ->
    case prog of
    Left  err                -> IO.hPutStrLn stderr err
    Right (TypedAST typ ast) -> IO.putStrLn . T.pack $
      let et = expandTransformationsWith'
                 (someTransformations toExpand haskellTransformations)
          concreteProgram = show . pretty . et $ ast
          withType t x = concat [ "(", x, ")"
                                , "\n.\n"
                                , show (prettyType 12 t)
                                ] in

      if printType then
          withType typ concreteProgram
      else concreteProgram

