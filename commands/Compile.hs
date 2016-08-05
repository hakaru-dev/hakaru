{-# LANGUAGE OverloadedStrings,
             DataKinds,
             KindSignatures,
             GADTs,
             FlexibleContexts,
             TypeOperators
             #-}

module Main where

import qualified Language.Hakaru.Syntax.AST as T
import           Language.Hakaru.Syntax.AST.Transforms
import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.TypeCheck

import           Language.Hakaru.Types.Sing
import           Language.Hakaru.Types.DataKind

import           Language.Hakaru.Pretty.Haskell
import           Language.Hakaru.Command (parseAndInfer)

import           Data.Text
import qualified Data.Text.IO as IO
import           Text.PrettyPrint

import           System.Environment
import           System.FilePath

main :: IO ()
main = do
  args   <- getArgs
  case args of
      [prog1, prog2] -> compileRandomWalk prog1 prog2
      [prog] -> compileHakaru prog
      _      -> IO.putStrLn "Usage: compile <file>"

prettyProg :: (ABT T.Term abt)
           => String
           -> abt '[] a
           -> String
prettyProg name ast =
    renderStyle style
    (cat [ text (name ++ " = ")
         , nest 2 (pretty ast)
         ])

compileHakaru :: String -> IO ()
compileHakaru file = do
    prog <- IO.readFile file
    let target = replaceFileName file (takeBaseName file) ++ ".hs"
    case parseAndInfer prog of
      Left err                 -> IO.putStrLn err
      Right (TypedAST typ ast) -> do
        IO.writeFile target . Data.Text.unlines $
          header ++
          [ pack $ prettyProg "prog" (et ast) ] ++
          footer typ
  where et = expandTransformations

compileRandomWalk :: String -> String -> IO ()
compileRandomWalk f1 f2 = do
    p1 <- IO.readFile f1
    p2 <- IO.readFile f2
    let output = replaceFileName f1 (takeBaseName f1) ++ ".hs"
    case (parseAndInfer p1, parseAndInfer p2) of
      ( Right (TypedAST _ ast1), Right (TypedAST _ ast2)) -> do
        -- TODO: Check that programs have the right types before
        --       compiling them.
        IO.writeFile output . Data.Text.unlines $
          header ++
          [ pack $ prettyProg "prog1" (et ast1) ] ++
          [ pack $ prettyProg "prog2" (et ast2) ] ++
          footerWalk
      (Left err, _) -> print err
      (_, Left err) -> print err

  where et = expandTransformations


header :: [Text]
header =
  [ "{-# LANGUAGE DataKinds, NegativeLiterals #-}"
  , "module Main where"
  , ""
  , "import           Prelude                          hiding ((>>=))"
  , "import           Language.Hakaru.Runtime.Prelude"
  , "import           Language.Hakaru.Types.Sing"
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

footerWalk :: [Text]
footerWalk =
  [ ""
  , "main :: IO ()"
  , "main = do"
  , "  g <- MWC.createSystemRandom"
  , "  x <- prog2 g"
  , "  iterateM_ (withPrint $ flip prog1 g) x"
  ]
