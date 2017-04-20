module Main where

import qualified Data.ByteString.Char8 as B
import News (getNews)
import qualified System.Random.MWC as MWC
import Scaffold
import qualified Data.Vector.Unboxed as V
import Data.Vector.Unboxed ((!))
import Text.Printf (printf)
import NaiveBayes (prog)
import Control.Monad (forever, replicateM, forM_)
import Data.List (sort)
import Data.Number.LogFloat
import System.IO


writeVec :: String -> V.Vector Int -> IO ()
writeVec file v = withFile file WriteMode $ \h -> do
  V.forM_ v $ \x -> hPrint h x

main = do
  (words, docs, topics) <- getNews Nothing [0..]
  writeVec "words" words
  writeVec "docs" docs
  writeVec "topics" topics
