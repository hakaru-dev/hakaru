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

main = do
  (words, docs, topics) <- getNews (Just 100) [0..]
  g <- MWC.create
  let 
    zPrior = onesFrom topics
    wPrior = onesFrom words
    predict = prog zPrior wPrior topics words docs
  printf "length zPrior == %d\n" (V.length zPrior)
  printf "length wPrior == %d\n" (V.length wPrior)
  printf "length words  == %d\n" (V.length words)
  printf "length docs   == %d\n" (V.length docs)
  printf "length topics == %d\n" (V.length topics)
  forM_ [0..(V.length topics - 1)] $ \i -> do
    print $ V.toList $ predict i

    -- printf "%d %d\n" (topics ! i) (V.maxIndex $ predict i)
  -- replicateM 5 . withGen g (print . sort) $ do
  --   pred <- predict
  --   let p = pred $ V.fromList $ [0,1,7]
  --   replicateM 100 p