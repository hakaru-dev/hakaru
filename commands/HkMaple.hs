{-# LANGUAGE CPP
           , OverloadedStrings
           , DataKinds
           , GADTs
           , RecordWildCards
           , ScopedTypeVariables
           #-}

module Main where

import           Language.Hakaru.Pretty.Concrete  
import           Language.Hakaru.Syntax.AST.Transforms
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Command (parseAndInfer', readFromFile', Term)

import           Language.Hakaru.Syntax.Rename
import           Language.Hakaru.Simplify
import           Language.Hakaru.Maple 
import           Language.Hakaru.Parser.Maple 

import           Language.Hakaru.Syntax.Transform (Transform(..))
import           Language.Hakaru.Syntax.IClasses (Some2(..))

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..), (<$>))
#endif

import           Data.Monoid ((<>), mconcat)
import           Data.Text (Text, unpack, pack)
import qualified Data.Text as Text 
import qualified Data.Text.Utf8 as IO
import           System.IO (stderr)
import           Data.List (intercalate) 
import           Text.Read (readMaybe)
import           Control.Exception(throw)
import qualified Options.Applicative as O
import qualified Data.Map as M 


data Options a 
  = Options
    { moptions      :: MapleOptions (Maybe String)
    , no_unicode    :: Bool
    , toExpand      :: Maybe [Some2 Transform]
    , program       :: a } 
  | ListCommands 


parseKeyVal :: O.ReadM (String, String) 
parseKeyVal = 
  O.maybeReader $ (\str -> 
    case map Text.strip $ Text.splitOn "," str of 
      [k,v] -> return (unpack k, unpack v)
      _     -> Nothing) . pack 

options :: O.Parser (Options FilePath)
options = (Options
  <$> (MapleOptions <$> 
        O.option (O.maybeReader (Just . Just))
        ( O.long "command" <>
          O.help ("Command to send to Maple. You may enter a prefix of the command string if "
                 ++"it uniquely identifies a command. ") <>
          O.short 'c' <> 
          O.value Nothing ) 
    <*> O.switch
        ( O.long "debug" <>
          O.help "Prints output that is sent to Maple." )
    <*> O.option O.auto
        ( O.long "timelimit" <>
          O.help "Set Maple to timeout in N seconds." <>
          O.showDefault <>
          O.value 90 <>
          O.metavar "N")
    <*> (M.fromList <$> 
          O.many (O.option parseKeyVal
        ( O.long "maple-opt" <> 
          O.short 'm' <> 
          O.help ( "Extra options to send to Maple\neach options is of the form KEY=VAL\n"
                 ++"where KEY is a Maple name, and VAL is a Maple expression.")
        ))))
  <*> O.switch 
      ( O.long "no-unicode" <> 
        O.short 'u' <> 
        O.help "Removes unicode characters from names in the Maple output.")
  <*> O.option (O.maybeReader $ fmap (fmap Just) readMaybe)
      ( O.short 'e' <>
        O.long "to-expand" <>
        O.value Nothing <>
        O.help "Transformations to be expanded; default is all transformations" )
  <*> O.strArgument
      ( O.metavar "PROGRAM" <> 
        O.help "Filename containing program to be simplified, or \"-\" to read from input." )) O.<|> 
  ( O.flag' ListCommands  
      ( O.long "list-commands" <>
        O.help "Get list of available commands from Maple." <>
        O.short 'l') )

parseOpts :: IO (Options FilePath)
parseOpts = O.execParser $ O.info (O.helper <*> options)
      (O.fullDesc <> O.progDesc progDesc)

progDesc :: String 
progDesc = unwords  
  ["hk-maple: invokes a Maple command on a Hakaru program. "
  ,"Given a Hakaru program in concrete syntax and a Maple-Hakaru command,"
  ,"typecheck the program"
  ,"invoke the Maple command on the program and its type"
  ,"pretty print, parse and typecheck the program resulting from Maple"
  ]

main :: IO ()
main = parseOpts >>= runMaple

runMaple :: Options FilePath -> IO ()
runMaple ListCommands = 
  listCommands >>= \cs -> putStrLn $ "Available Hakaru Maple commands:\n\t"++ intercalate ", " cs

runMaple Options{..} = readFromFile' program >>= parseAndInfer' >>= \prog ->
  case prog of
    Left  err  -> IO.hPutStrLn stderr err
    Right ast  -> do
      let et = onTypedASTM $ expandTransformationsWith $
                (maybe id someTransformations toExpand) allTransformations
      TypedAST _ ast' <-
        (case command moptions of
           Just c  -> sendToMaple' moptions{command=c}
           Nothing -> return) =<< et ast
      IO.print
            $ pretty 
            $ (if no_unicode then renameAST removeUnicodeChars else id) 
            $ ast'

listCommands :: IO [String] 
listCommands = do 
    let toMaple_ = "use Hakaru, NewSLO in lprint(map(curry(sprintf,`%s`),NewSLO:-Commands)) end use;"
    fromMaple <- maple toMaple_
    maybe (throw $ MapleInterpreterException fromMaple toMaple_)
          return 
          (readMaybe fromMaple) 
