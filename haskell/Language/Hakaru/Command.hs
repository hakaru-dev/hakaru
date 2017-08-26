{-# LANGUAGE CPP
           , DataKinds
           , OverloadedStrings
           , FlexibleContexts
           #-}
module Language.Hakaru.Command where

import           Language.Hakaru.Syntax.ABT
import qualified Language.Hakaru.Syntax.AST as T
import           Language.Hakaru.Parser.Import (expandImports)
import           Language.Hakaru.Parser.Parser (parseHakaru, parseHakaruWithImports)
import           Language.Hakaru.Parser.SymbolResolve (resolveAST)
import           Language.Hakaru.Syntax.TypeCheck

import           Control.Monad.Trans.Except
import           Control.Monad (when)
import qualified Data.Text      as Text
import qualified Data.Text.IO   as IO
import qualified Data.Text.Utf8 as U
import qualified Options.Applicative as O
import           Data.Vector
import           System.IO (stderr)
import           System.Environment (getArgs)
import           Data.Monoid ((<>),mconcat)
import           System.FilePath (takeDirectory)

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..), (<$>))
#endif

type Term a = TrivialABT T.Term '[] a

parseAndInfer :: Text.Text
              -> Either Text.Text (TypedAST (TrivialABT T.Term))
parseAndInfer x = parseAndInferWithMode x LaxMode

parseAndInferWithMode
  :: ABT T.Term abt
  => Text.Text
  -> TypeCheckMode
  -> Either Text.Text (TypedAST abt)
parseAndInferWithMode x mode =
    case parseHakaru x of
    Left  err  -> Left (Text.pack . show $ err)
    Right past ->
        let m = inferType (resolveAST past) in
        runTCM m (splitLines x) mode

-- The filepath from which the text came and the text itself. If the filepath is
-- Nothing, imports are searched for in the current directory.
data Source = Source { file :: Maybe FilePath, source :: Text.Text }

sourceInput :: Source -> Maybe (Vector Text.Text)
sourceInput = splitLines . source

noFileSource :: Text.Text -> Source
noFileSource = Source Nothing

fileSource :: FilePath -> Text.Text -> Source
fileSource = Source . Just

parseAndInfer' :: Source
               -> IO (Either Text.Text (TypedAST (TrivialABT T.Term)))
parseAndInfer' s = parseAndInferWithMode' s LaxMode

parseAndInferWithMode'
  :: ABT T.Term abt
  => Source
  -> TypeCheckMode
  -> IO (Either Text.Text (TypedAST abt))
parseAndInferWithMode' (Source dir x) mode =
    case parseHakaruWithImports x of
    Left  err  -> return . Left $ Text.pack . show $ err
    Right past -> do
      past' <- runExceptT (expandImports (fmap takeDirectory dir) past)
      case past' of
        Left err     -> return . Left $ Text.pack . show $ err
        Right past'' -> do
          let m = inferType (resolveAST past'')
          return (runTCM m (splitLines x) mode)

parseAndInferWithDebug
    :: Bool
    -> Text.Text
    -> IO (Either Text.Text (TypedAST (TrivialABT T.Term)))
parseAndInferWithDebug debug x =
  case parseHakaru x of
    Left err -> return $ Left (Text.pack . show $ err)
    Right past -> do
      when debug $ putErrorLn $ hrule "Parsed AST"
      when debug $ putErrorLn . Text.pack . show $ past
      let resolved = resolveAST past
      let inferred  = runTCM (inferType resolved) (splitLines x) LaxMode
      when debug $ putErrorLn $ hrule "Inferred AST"
      when debug $ putErrorLn . Text.pack . show $ inferred
      return $ inferred
  where hrule s = Text.concat ["\n<=======================| "
                              ,s," |=======================>\n"]
        putErrorLn = IO.hPutStrLn stderr


splitLines :: Text.Text -> Maybe (Vector Text.Text)
splitLines = Just . fromList . Text.lines

readFromFile :: String -> IO Text.Text
readFromFile "-" = U.getContents
readFromFile x   = U.readFile x

readFromFile' :: String -> IO Source
readFromFile' x = Source (if x=="-" then Nothing else Just x) <$> readFromFile x

simpleCommand :: (Text.Text -> IO ()) -> Text.Text -> IO ()
simpleCommand k fnName = 
  let parser = 
        O.info (O.helper <*> opts)
               (O.fullDesc <> O.progDesc 
                 (mconcat["Hakaru:", Text.unpack fnName, " command"]))
      opts = 
        O.strArgument
           ( O.metavar "PROGRAM" <> 
             O.showDefault <> O.value "-" <> 
             O.help "Filepath to Hakaru program OR \"-\"" )

  in O.execParser parser >>= readFromFile >>= k 

writeToFile :: String -> (Text.Text -> IO ())
writeToFile "-" = U.putStrLn 
writeToFile x   = U.writeFile x
