{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Hakaru.Command where

import           Language.Hakaru.Syntax.ABT
import qualified Language.Hakaru.Syntax.AST as T
import           Language.Hakaru.Parser.Import (expandImports)
import           Language.Hakaru.Parser.Parser hiding (style)
import           Language.Hakaru.Parser.SymbolResolve (resolveAST)
import           Language.Hakaru.Syntax.TypeCheck

import           Control.Monad.Trans.Except
import           Control.Monad (when)
import qualified Data.Text    as Text
import qualified Data.Text.IO as IO
import           Data.Vector
import           System.IO (stderr)

type Term a = TrivialABT T.Term '[] a

parseAndInfer :: Text.Text
              -> Either Text.Text (TypedAST (TrivialABT T.Term))
parseAndInfer x =
    case parseHakaru x of
    Left  err  -> Left (Text.pack . show $ err)
    Right past ->
        let m = inferType (resolveAST past) in
        runTCM m (splitLines x) LaxMode

parseAndInfer' :: Text.Text
               -> IO (Either Text.Text (TypedAST (TrivialABT T.Term)))
parseAndInfer' x =
    case parseHakaruWithImports x of
    Left  err  -> return . Left $ Text.pack . show $ err
    Right past -> do
      past' <- runExceptT (expandImports past)
      case past' of
        Left err     -> return . Left $ Text.pack . show $ err
        Right past'' -> do
          let m = inferType (resolveAST past'')
          return (runTCM m (splitLines x) LaxMode)

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
  where hrule s = mconcat ["\n<=======================| "
                          ,s," |=======================>\n"]
        putErrorLn = IO.hPutStrLn stderr




splitLines :: Text.Text -> Maybe (Vector Text.Text)
splitLines = Just . fromList . Text.lines

readFromFile :: String -> IO Text.Text
readFromFile "-" = IO.getContents
readFromFile x   = IO.readFile x

writeToFile :: String -> (Text.Text -> IO ())
writeToFile "-" = IO.putStrLn
writeToFile x   = IO.writeFile x
