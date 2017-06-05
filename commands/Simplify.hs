{-# LANGUAGE CPP, OverloadedStrings, DataKinds, GADTs, RecordWildCards, ScopedTypeVariables #-}

module Main where

import           Language.Hakaru.Pretty.Concrete  
import           Language.Hakaru.Syntax.AST.Transforms
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Command (parseAndInfer, readFromFile, Term)

import           Language.Hakaru.Syntax.Rename
import           Language.Hakaru.Simplify
import           Language.Hakaru.Maple 


#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..), (<$>))
#endif

import           Data.Monoid ((<>), mconcat)
import           Data.Text (Text, unpack, pack)
import qualified Data.Text.IO as IO
import           System.IO (stderr)
import           Data.List (intercalate) 
import           Text.Read (readMaybe)
import           Control.Exception(throw)
import qualified Options.Applicative as O


data Options a 
  = Options
    { moptions      :: MapleOptions (Maybe String) 
    , no_unicode    :: Bool
    , program       :: a } 
  | ListCommands 

options :: O.Parser (Options FilePath)
options = (Options
  <$> (MapleOptions <$> 
        O.option (Just <$> O.str)
        ( O.long "command" <>
          O.help "Command to send to Maple" <>
          O.short 'c' <> 
          O.value Nothing ) 
    <*> O.switch
        ( O.long "debug" <>
          O.help "Prints output that is sent to Maple" )
    <*> O.option O.auto
        ( O.long "timelimit" <>
          O.help "Set simplify to timeout in N seconds" <>
          O.showDefault <>
          O.value 90 <>
          O.metavar "N"))
  <*> O.switch 
      ( O.long "no-unicode" <> 
        O.short 'u' <> 
        O.help "Removes unicode characters from names in the Maple output")
  <*> O.strArgument
      ( O.metavar "PROGRAM" <> 
        O.help "Program to be simplified" )) O.<|> 
  ( O.flag' ListCommands  
      ( O.long "list-commands" <>
        O.help "Get list of available commands from Maple" <>
        O.short 'l') )

parseOpts :: IO (Options FilePath)
parseOpts = O.execParser $ O.info (O.helper <*> options)
      (O.fullDesc <> O.progDesc "Simplify a hakaru program")

et (TypedAST t (x :: Term a)) = TypedAST t (expandTransformations x)

main :: IO ()
main = parseOpts >>= runSimplify

runSimplify :: Options FilePath -> IO ()
runSimplify ListCommands = 
  listCommands >>= \cs -> putStrLn $ "Available Hakaru Maple commands:\n\t"++ intercalate ", " cs

runSimplify Options{..} = readFromFile program >>= \prog -> 
  case parseAndInfer prog of
    Left  err  -> IO.hPutStrLn stderr err
    Right ast  -> do 
      TypedAST _ ast' <- sendToMaple' (fmap (maybe "Simplify" id) moptions) (et ast)
      print $ pretty 
            $ (if no_unicode then renameAST removeUnicodeChars else id) 
            $ ast'

listCommands :: IO [String] 
listCommands = do 
    let toMaple_ = "use Hakaru, NewSLO in lprint(map(curry(sprintf,`%s`),NewSLO:-Commands)) end use;"
    fromMaple <- maple toMaple_
    maybe (throw $ MapleException fromMaple toMaple_)
          return 
          (readMaybe fromMaple) 
