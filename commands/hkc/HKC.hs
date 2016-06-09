{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Main where

import Language.Hakaru.Parser.Parser hiding (style)
import Language.Hakaru.Parser.SymbolResolve (resolveAST)
import qualified Language.Hakaru.Pretty.Concrete as HK (pretty)

import           Language.Hakaru.Syntax.ABT
import qualified Language.Hakaru.Syntax.AST as T
import           Language.Hakaru.Syntax.TypeCheck

import qualified Language.C.Pretty as C

import HKC.Flatten

import           Data.Text
import qualified Data.Text.IO as IO
import           Text.PrettyPrint

import System.Environment

main :: IO ()
main = do
  args   <- getArgs
  progs  <- mapM readFromFile args
  case progs of
      [prog] -> compileHakaru prog
      _      -> IO.putStrLn "Usage: hkc <input> <output>"

readFromFile :: String -> IO Text
readFromFile "-" = IO.getContents
readFromFile x   = IO.readFile x


-- TODO: parseAndInfer has been copied to hkc, compile, and hakaru commands
parseAndInfer :: Text
              -> Either String (TypedAST (TrivialABT T.Term))
parseAndInfer x =
    case parseHakaru x of
    Left  err  -> Left (show err)
    Right past ->
        let m = inferType (resolveAST past) in
        runTCM m LaxMode

compileHakaru :: Text -> IO ()
compileHakaru prog =
  case parseAndInfer prog of
    Left err -> putStrLn $ show err
    Right (TypedAST _ ast) ->
      do let ast' = flatten ast
             doc  = render (C.prettyUsingInclude ast')
         IO.putStrLn "\nHakaru |===================================>\n"
         IO.putStrLn (pack $ show $ HK.pretty ast)
         IO.putStrLn "\nC |===================================>\n"
         IO.putStrLn (Data.Text.unlines [includes,pack doc])

includes :: Text
includes = Data.Text.unlines
           [ "#include <time.h>"
           , "#include <stdlib.h>"
           , "#include <stdio.h>"
           , "#include <math.h>" ]
