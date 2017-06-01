{-# LANGUAGE 
    TypeSynonymInstances
  , FlexibleInstances
  , OverloadedStrings
  #-}

module Data.Utf8.IO 
  ( putStr, putStrLn, hPut, hPutStr, hPutStrLn
  , print 
  , readFile, writeFile 
  , getContents  
  ) where 

import           Control.Applicative (liftA)
import qualified Data.ByteString as BIO 
import           Data.Text.Encoding (decodeUtf8, encodeUtf8)
import           Data.Text (Text, pack, unpack)
import qualified Data.Text.IO as IO
import           Data.Monoid ((<>))
import           Prelude hiding (putStr, putStrLn, readFile, writeFile, getContents, print)
import           System.IO (Handle)

readFile :: FilePath -> IO Text
readFile = liftA (liftA decodeUtf8) BIO.readFile  

getContents :: IO Text 
getContents = liftA decodeUtf8 BIO.getContents

putStr :: Text -> IO ()
putStr = BIO.putStr . encodeUtf8

putStrLn :: Text -> IO ()
putStrLn = putStr . (<>"\n")

writeFile :: FilePath -> Text -> IO ()
writeFile f x = BIO.writeFile f (encodeUtf8 x) 

hPut :: Handle -> Text -> IO ()
hPut h x = BIO.hPut h (encodeUtf8 x) 

hPutStr :: Handle -> Text -> IO ()
hPutStr = hPut 

hPutStrLn :: Handle -> Text -> IO ()
hPutStrLn h x = hPutStr h (x<>"\n")

print :: Show a => a -> IO ()
print = putStrLn . pack . show 
