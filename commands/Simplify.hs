{-# LANGUAGE CPP, OverloadedStrings, DataKinds, GADTs #-}

module Main where

import qualified Language.Hakaru.Parser.AST as U
import           Language.Hakaru.Parser.Parser
import           Language.Hakaru.Parser.SymbolResolve (resolveAST)
import           Language.Hakaru.Pretty.Concrete  
import qualified Language.Hakaru.Syntax.AST as T
import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.TypeCheck

import           Language.Hakaru.Simplify


#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..), (<$>))
#endif

import           Data.Text
import qualified Data.Text.IO as IO

import qualified Options.Applicative as O

data Options = Options
  { program :: String
  , debug   :: Bool }

options :: O.Parser Options
options = Options
  <$> O.strArgument
      ( O.metavar "PROGRAM" O.<> 
        O.help "Program to be simplified" )
  <*> O.switch
      ( O.long "debug" O.<>
        O.help "Prints output that is sent to Maple" )

parseOpts :: IO Options
parseOpts = O.execParser $ O.info (O.helper <*> options)
      (O.fullDesc O.<> O.progDesc "Simplify a hakaru program")

readFromFile :: String -> IO Text
readFromFile "-" = IO.getContents
readFromFile x   = IO.readFile x

main :: IO ()
main = do
  args <- parseOpts
  case args of
   Options file debug -> do
    prog <- readFromFile file
    runSimplify prog debug

inferType' :: U.AST -> TypeCheckMonad (TypedAST (TrivialABT T.Term))
inferType' = inferType

runSimplify :: Text -> Bool -> IO ()
runSimplify prog debug =
    case parseHakaru prog of
    Left  err  -> print err
    Right past ->
        let m = inferType' (resolveAST past) in
        case (runTCM m LaxMode, debug) of
        (Left err, _)                   -> putStrLn err
        (Right (TypedAST _ ast), True)  -> simplifyDebug ast >>= print . pretty
        (Right (TypedAST _ ast), False) -> simplify      ast >>= print . pretty

