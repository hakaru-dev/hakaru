module Main where

import qualified Data.ByteString.Char8 as B
import News (getNews)
import qualified System.Random.MWC as MWC
import Scaffold
import qualified Data.Vector.Unboxed as V
import Text.Printf (printf)

main = do
  (words, docs, topics) <- getNews (Just 3) [0,2,4]
  g <- MWC.create
  let 
    zPrior = onesFrom topics
    wPrior = onesFrom words
    next z = gibbsRound zPrior wPrior z words docs
  printf "length zPrior == %d\n" (V.length zPrior)
  printf "length wPrior == %d\n" (V.length wPrior)
  printf "length words  == %d\n"  (V.length words)
  printf "length docs   == %d\n"   (V.length docs)
  printf "length topics == %d\n" (V.length topics)
  samples print g topics next