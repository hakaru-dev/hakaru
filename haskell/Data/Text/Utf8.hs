module Data.Text.Utf8 where

import           Prelude               hiding (putStr, putStrLn)
import           Control.Applicative   (liftA)
import qualified Data.ByteString.Char8 as BIO 
import qualified Data.Text             as Text
import           Data.Text.Encoding    (decodeUtf8, encodeUtf8)
import           System.IO (Handle)

readFile :: FilePath -> IO Text.Text
readFile = liftA (liftA decodeUtf8) BIO.readFile  

getContents :: IO Text.Text 
getContents = liftA decodeUtf8 BIO.getContents

putStr :: Text.Text -> IO ()
putStr = BIO.putStr . encodeUtf8

putStrLn :: Text.Text -> IO ()
putStrLn = BIO.putStrLn . encodeUtf8

writeFile :: FilePath -> Text.Text -> IO ()
writeFile f x = BIO.writeFile f (encodeUtf8 x) 

hPut :: Handle -> Text.Text -> IO ()
hPut h x = BIO.hPut h (encodeUtf8 x) 

putStrS :: String -> IO ()
putStrS = putStr . Text.pack

putStrLnS :: String -> IO ()
putStrLnS = putStrLn . Text.pack
