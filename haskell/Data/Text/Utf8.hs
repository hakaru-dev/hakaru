{-# LANGUAGE CPP, OverloadedStrings #-}

module Data.Text.Utf8 where

import           Prelude               hiding (putStr, putStrLn)

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..), (<$>))
#endif

import qualified Data.ByteString.Char8 as BIO 
import qualified Data.Text             as Text
import           Data.Text.Encoding    (decodeUtf8, encodeUtf8)
import           System.IO (Handle)

readFile :: FilePath -> IO Text.Text
readFile f = decodeUtf8 <$> (BIO.readFile f)

getContents :: IO Text.Text 
getContents = decodeUtf8 <$> BIO.getContents

putStr :: Text.Text -> IO ()
putStr = BIO.putStr . encodeUtf8

putStrLn :: Text.Text -> IO ()
putStrLn = BIO.putStrLn . encodeUtf8

writeFile :: FilePath -> Text.Text -> IO ()
writeFile f x = BIO.writeFile f (encodeUtf8 x) 

hPut :: Handle -> Text.Text -> IO ()
hPut h x = BIO.hPut h (encodeUtf8 x) 

hPutStrLn :: Handle -> Text.Text -> IO ()
hPutStrLn h x = BIO.hPutStrLn h (encodeUtf8 x)

putStrS :: String -> IO ()
putStrS = putStr . Text.pack

putStrLnS :: String -> IO ()
putStrLnS = putStrLn . Text.pack

print :: Show a => a -> IO ()
print = BIO.putStrLn . encodeUtf8 . Text.pack . show 

