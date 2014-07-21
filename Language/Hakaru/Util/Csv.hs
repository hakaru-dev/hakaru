{-# LANGUAGE TypeOperators #-}

module Language.Hakaru.Util.Csv ((:::)((:::)), decodeFile, decodeGZipFile,
                 decodeFileStream, decodeGZipFileStream) where

import Data.Csv ( HasHeader(..), FromRecord(..), FromField(..)
                , ToRecord(..), ToField(..), decode)
import qualified Data.Csv.Streaming as CS (decode)
import Codec.Compression.GZip (decompress)
import qualified Data.Foldable as F
import qualified Data.ByteString.Lazy as B
import qualified Data.Vector as V
import Control.Applicative ((<*>), (<$>))

data a ::: b = a ::: b deriving (Eq, Ord, Read, Show)
infixr 5 :::

instance (FromField a, FromRecord b) => FromRecord (a ::: b) where
  parseRecord v | V.null v  = fail "too few fields in input record"
                | otherwise = (:::) <$> parseField (V.head v) <*> parseRecord (V.tail v)

instance (ToField a, ToRecord b) => ToRecord (a ::: b) where
  toRecord (a ::: b) = V.cons (toField a) (toRecord b)

decodeBytes :: FromRecord a => B.ByteString -> [a]
decodeBytes bs = case decode HasHeader bs of
                   Left _ -> []
                   Right v -> V.toList v

decodeFile :: FromRecord a => FilePath -> IO [a]
decodeFile = fmap decodeBytes . B.readFile

decodeGZipFile :: FromRecord a => FilePath -> IO [a]
decodeGZipFile = fmap (decodeBytes . decompress) . B.readFile

decodeFileStream :: FromRecord a => FilePath -> IO [a]
decodeFileStream = fmap (F.toList . CS.decode HasHeader) . B.readFile

decodeGZipFileStream :: FromRecord a => FilePath -> IO [a]
decodeGZipFileStream = fmap (F.toList . CS.decode HasHeader . decompress) . B.readFile
