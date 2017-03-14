{-# LANGUAGE OverloadedStrings #-}

module Data.News (getNews) where

import qualified Data.HashMap.Strict as H
import Data.HashMap.Strict (HashMap)
import Control.Monad.State.Strict 
import Data.Hashable (Hashable)

import qualified Data.ByteString.Char8 as B
import Data.Char (toLower, isLower)
import System.Directory
import System.FilePath

import qualified Data.Vector.Unboxed as V
import Data.Vector.Unboxed (Vector)

-- import Filesystem.Path.Internal.FilePath (FilePath)

-- | An 'Encoding a' is a bijection from some set of values from 'a' to 'Int's '[0..(n-1)]'. 
-- 'Encoding n xs h' has the following invariants:
-- * length xs == H.size h == n
-- * n>0 => H.lookup (head xs) h == Just (n-1)
-- * n>0 => H.lookup (last xs) h == Just 0
data Encoding a = Encoding 
  Int              -- The number of entries
  [a]              -- The decoded values
  (HashMap a Int)  -- The integer encoding
    deriving Show

type EncodeState a = StateT (Encoding B.ByteString) IO a

empty :: Encoding a
empty = Encoding 0 [] H.empty

run :: EncodeState a -> IO a
run x = evalStateT x empty

encode :: B.ByteString -> EncodeState Int
encode x = do
  Encoding n xs h <- get
  case H.lookup x h of
    -- If 'x' has already been seen, just return the code
    Just k -> return k

    -- If not, update the encoding and return the code
    Nothing -> do
      put $ Encoding (n+1) (x:xs) (H.insert x n h)
      return n

encodeFile :: FilePath -> EncodeState [Int]
encodeFile fname = do
  ws <- liftIO . fmap (filter (/= "") . B.splitWith (not . isLower) . B.map toLower) . B.readFile $ fname 
  traverse encode ws

encodeDir :: FilePath -> EncodeState [[Int]]
encodeDir path = do
  fnames <- liftIO $ do
    names <- listDirectory path
    filterM doesFileExist $ map (path </>) names
  traverse encodeFile fnames

encodeDirs :: FilePath -> EncodeState [[[Int]]]
encodeDirs path = do
  dnames <- liftIO $ do
    names <- listDirectory path
    filterM doesDirectoryExist $ map (path </>) names
  traverse encodeDir dnames

path = "/home/chad/git/iu/hakaru/examples/naive_bayes/20_newsgroups"
  
asArrays :: [[[Int]]] -> (Vector Int, Vector Int)
asArrays groupList = (wordIndices, docIndices)
  where
  docList = concat groupList
  docIndices = V.fromList . concat $ zipWith replicate (map length docList) [0..]
  wordIndices = V.fromList . concat $ docList

getNews :: IO (Vector Int, Vector Int)
getNews = fmap asArrays . run $ encodeDirs path