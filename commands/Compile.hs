{-# LANGUAGE OverloadedStrings,
             DataKinds,
             KindSignatures,
             GADTs,
             FlexibleContexts,
             TypeOperators
             #-}

module Main where

import           Language.Hakaru.Parser.Parser (parseHakaru)
import           Language.Hakaru.Parser.SymbolResolve (resolveAST)


import qualified Language.Hakaru.Syntax.AST as T
import           Language.Hakaru.Syntax.AST.Transforms
import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.TypeCheck

import           Language.Hakaru.Types.Sing
import           Language.Hakaru.Types.DataKind

import           Language.Hakaru.Pretty.Haskell

import           Data.Text
import qualified Data.Text.IO as IO
import           Text.PrettyPrint

import           System.Environment
import           System.FilePath

main :: IO ()
main = do
  args   <- getArgs
  case args of
      [prog] -> compileHakaru prog
      _      -> IO.putStrLn "Usage: compile <file>"

parseAndInfer :: Text
              -> Either String (TypedAST (TrivialABT T.Term))
parseAndInfer x =
    case parseHakaru x of
    Left  err  -> Left (show err)
    Right past ->
        let m = inferType (resolveAST past) in
        runTCM m LaxMode

prettyProg :: (ABT T.Term abt)
           => abt '[] a -> String
prettyProg ast = renderStyle style
                 (cat [ text "prog = "
                      , nest 2 (pretty ast)
                      ])

compileHakaru :: String -> IO ()
compileHakaru file = do
    prog <- IO.readFile file
    let target = replaceFileName file (takeBaseName file) ++ ".hs"
    case parseAndInfer prog of
      Left err                 -> putStrLn err
      Right (TypedAST typ ast) -> do
        IO.writeFile target . Data.Text.unlines $
          header ++ [ pack $ prettyProg (et ast) ] ++ footer typ
  where et = expandTransformations

header :: [Text]
header =
  [ "module Main where"
  , ""
  , "import           Prelude                          hiding ((>>=))"
  , "import           Language.Hakaru.Runtime.Prelude"
  , "import qualified System.Random.MWC                as MWC"
  , "import           Control.Monad                    hiding ((>>=))"
  , ""
  ]

footer :: Sing (a :: Hakaru) -> [Text]
footer typ =
  [ ""
  , "main :: IO ()"
  , "main = do"
  , "  g <- MWC.createSystemRandom"
  , case typ of
      SMeasure _ -> "  forever $ run g prog"
      _          -> "  run g prog"
  ]
