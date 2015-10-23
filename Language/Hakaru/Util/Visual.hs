-- TODO: [wrengr 2015.10.23] (a) remove this file entirely, or (b) move it somewhere more helpful.

{-# LANGUAGE OverloadedStrings #-}

module Language.Hakaru.Util.Visual where

import System.IO
import Control.Monad

import Data.Aeson
import Data.List
import qualified Data.Text as T
import qualified Data.ByteString.Lazy.Char8 as B
--import qualified Data.ByteString.Char8 as BS

plot :: Show a => [a] -> String -> IO ()
plot samples filename = do
  h <- openFile filename WriteMode
  hPrint h samples
  hClose h

batchPrint :: Show a => Int -> [a] -> IO ()
batchPrint n l = do
  let batch = take n l
  print batch
  when (length batch == n) $ batchPrint n (drop n l)

viz :: ToJSON a => Int -> [String] -> [[a]] -> IO ()
viz n name samples = viz' n 50 0 name samples

viz' :: ToJSON a => Int -> Int -> Int -> [String] -> [[a]] -> IO ()
viz' n c cur name samples = do
  putStrLn batch
  when (c+cur < n) $
       viz' n c (cur+c) name (drop c samples)
  where
    total = "total_samples" .= n
    current_sample = "current_sample" .= cur
    chunk = object (zipWith (\ name' s -> T.pack name' .= s)
                            name
                            (transpose $ take c samples))
    batch = B.unpack $ encode
            (object ["rvars" .= chunk,
                     total,
                     current_sample])
