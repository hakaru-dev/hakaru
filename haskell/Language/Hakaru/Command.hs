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
import           Data.Text.Encoding (decodeUtf8, encodeUtf8)
import qualified Data.Text.IO as IO
import qualified Data.ByteString as BIO 
import           Data.Vector
import           System.IO (stderr, Handle)
import           System.Environment (getArgs) 
import           Control.Applicative (liftA)
import           Data.Monoid ((<>))

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
  where hrule s = Text.concat ["\n<=======================| "
                              ,s," |=======================>\n"]
        putErrorLn = IO.hPutStrLn stderr




splitLines :: Text.Text -> Maybe (Vector Text.Text)
splitLines = Just . fromList . Text.lines

readFile_utf8 :: FilePath -> IO Text.Text
readFile_utf8 = liftA (liftA decodeUtf8) BIO.readFile  

getContents_utf8 :: IO Text.Text 
getContents_utf8 = liftA decodeUtf8 BIO.getContents

readFromFile :: String -> IO Text.Text
readFromFile "-" = getContents_utf8
readFromFile x   = readFile_utf8 x

simpleCommand :: (Text.Text -> IO ()) -> Text.Text -> IO ()
simpleCommand k fnName = do 
  args <- getArgs
  case args of
      [prog] -> readFile_utf8 prog >>= k
      []     -> getContents_utf8   >>= k 
      _      -> IO.hPutStrLn stderr $ "Usage: " <> fnName <> " <file>"


putStr_utf8 :: Text.Text -> IO ()
putStr_utf8 = BIO.putStr . encodeUtf8

putStrLn_utf8 :: Text.Text -> IO ()
putStrLn_utf8 x = BIO.putStr (encodeUtf8 x <> "\n")

writeFile_utf8 :: FilePath -> Text.Text -> IO ()
writeFile_utf8 f x = BIO.writeFile f (encodeUtf8 x) 

hPut_utf8 :: Handle -> Text.Text -> IO ()
hPut_utf8 h x = BIO.hPut h (encodeUtf8 x) 

writeToFile :: String -> (Text.Text -> IO ())
writeToFile "-" = putStrLn_utf8 
writeToFile x   = writeFile_utf8 x
