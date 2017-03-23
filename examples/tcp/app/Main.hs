module Main where

import qualified Data.ByteString.Char8 as B
import News (getNews)
import qualified System.Random.MWC as MWC
import Scaffold (samples, z0, next)

main = do
  (words, docs, topics) <- getNews (Just 5) [0,1]
  g <- MWC.create
  samples print g topics next