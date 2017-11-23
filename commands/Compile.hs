{-# LANGUAGE CPP,
             OverloadedStrings,
             PatternGuards,
             DataKinds,
             KindSignatures,
             GADTs,
             FlexibleContexts,
             TypeOperators,
             RankNTypes
             #-}

module Main where

import qualified Language.Hakaru.Syntax.AST as T
import           Language.Hakaru.Syntax.AST.Transforms
import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.TypeCheck

import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Types.Sing (Sing(SFun, SMeasure))

import           Language.Hakaru.Pretty.Haskell
import           Language.Hakaru.Command

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..), (<$>))
#endif

import           Data.Text                  as TxT
import qualified Data.Text.IO               as IO
import           Data.Maybe (fromJust)
import           Data.Monoid ((<>))
import           System.IO (stderr)
import           Text.PrettyPrint    hiding ((<>))
import qualified Options.Applicative as O
import           System.FilePath


data Options =
  Options { fileIn          :: String
          , fileOut         :: Maybe String
          , asModule        :: Maybe String
          , fileIn2         :: Maybe String
          , logFloatPrelude :: Bool
          , optimize        :: Bool
          } deriving Show

main :: IO ()
main = do
  opts <- parseOpts
  case fileIn2 opts of
    Just _  -> compileRandomWalk opts
    Nothing -> compileHakaru opts

parseOpts :: IO Options
parseOpts = O.execParser $ O.info (O.helper <*> options)
                         $ O.fullDesc <> O.progDesc "Compile Hakaru to Haskell"

{-

There is some redundancy in Compile.hs, Hakaru.hs, and HKC.hs in how we decide
what to run given which arguments. There may be a way to unify these.

-}

options :: O.Parser Options
options = Options
  <$> O.strArgument (O.metavar "INPUT" <>
                     O.help "Program to be compiled" )
  <*> (O.optional $
        O.strOption (O.metavar "FILE" <>
                     O.short 'o' <>
                     O.help "Optional output file name"))
  <*> (O.optional $
        O.strOption (O.long "as-module" <>
                     O.short 'M' <>
                     O.help "creates a haskell module with this name"))
  <*> (O.optional $
        O.strOption (O.long "transition-kernel" <>
                     O.help "Use this program as transition kernel for running a markov chain"))
  <*> O.switch (O.long "logfloat-prelude" <>
                O.help "use logfloat prelude for numeric stability")
  <*> O.switch (O.short 'O' <>
                O.help "perform Hakaru AST optimizations")

prettyProg :: (ABT T.Term abt)
           => String
           -> Sing a
           -> abt '[] a
           -> String
prettyProg name typ ast =
    renderStyle style
    (    sep [text (name ++ " ::"), nest 2 (prettyType typ)]
     $+$ sep [text (name ++ " =") , nest 2 (pretty     ast)] )

compileHakaru
    :: Options
    -> IO ()
compileHakaru opts = do
    let file = fileIn opts
    prog <- readFromFile file
    case parseAndInfer prog of
      Left err                 -> IO.hPutStrLn stderr err
      Right (TypedAST typ ast) -> do
        let ast' = (if optimize opts then optimizations else id) (et ast)
        writeHkHsToFile file (fileOut opts) . TxT.unlines $
          header (logFloatPrelude opts) (asModule opts) ++
          [ pack $ prettyProg "prog" typ ast' ] ++
          (case asModule opts of
             Nothing -> footer
             Just _  -> [])
  where et = expandTransformations

compileRandomWalk
    :: Options
    -> IO ()
compileRandomWalk opts = do
    let f1 = fileIn opts
        f2 = fromJust . fileIn2 $ opts
    p1 <- readFromFile f1
    p2 <- readFromFile f2
    case (parseAndInfer p1, parseAndInfer p2) of
      (Right (TypedAST typ1 ast1), Right (TypedAST typ2 ast2)) ->
          -- TODO: Use better error messages for type mismatch
          case (typ1, typ2) of
            (SFun a (SMeasure b), SMeasure c)
              | (Just Refl, Just Refl) <- (jmEq1 a b, jmEq1 b c)
              -> writeHkHsToFile f1 (fileOut opts) . TxT.unlines $
                   header (logFloatPrelude opts) (asModule opts) ++
                   [ pack $ prettyProg "prog1" typ1 (expandTransformations ast1) ] ++
                   [ pack $ prettyProg "prog2" typ2 (expandTransformations ast2) ] ++
                   (case asModule opts of
                      Nothing -> footerWalk
                      Just _  -> [])
            _ -> IO.hPutStrLn stderr "compile: programs have wrong type"
      (Left err, _) -> IO.hPutStrLn stderr err
      (_, Left err) -> IO.hPutStrLn stderr err

writeHkHsToFile :: String -> Maybe String -> Text -> IO ()
writeHkHsToFile inFile moutFile content =
  let outFile =  case moutFile of
                   Nothing -> replaceFileName inFile (takeBaseName inFile) ++ ".hs"
                   Just x  -> x
  in  writeToFile outFile content

header :: Bool -> Maybe String -> [Text]
header logfloats mmodule =
  [ "{-# LANGUAGE DataKinds, NegativeLiterals #-}"
  , TxT.unwords [ "module"
                , case mmodule of
                    Just m  -> pack m
                    Nothing -> "Main"
                , "where" ]
  , ""
  , if logfloats
    then TxT.unlines [ "import           Data.Number.LogFloat (LogFloat)"
                     , "import           Prelude hiding (product, exp, log, (**), pi)"
                     , "import           Language.Hakaru.Runtime.LogFloatPrelude"
                     ]
    else TxT.unlines [ "import           Prelude hiding (product)"
                     , "import           Language.Hakaru.Runtime.Prelude"
                     ]
  , "import           Language.Hakaru.Runtime.CmdLine"
  , "import           Language.Hakaru.Types.Sing"
  , "import qualified System.Random.MWC                as MWC"
  , "import           Control.Monad"
  , "import           System.Environment (getArgs)"
  , ""
  ]

footer :: [Text]
footer =
    ["","main :: IO ()"
    , TxT.concat ["main = makeMain prog =<< getArgs"]]

footerWalk :: [Text]
footerWalk =
  [ ""
  , "main :: IO ()"
  , "main = do"
  , "  g <- MWC.createSystemRandom"
  , "  x <- prog2 g"
  , "  iterateM_ (withPrint $ flip prog1 g) x"
  ]
