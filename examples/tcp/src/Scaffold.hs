module Scaffold where

import NaiveBayes (prog)
import qualified Data.Vector.Unboxed as V
import qualified Data.Vector.Unboxed.Mutable as MV
import Data.Vector.Unboxed (Vector)
import           Prelude                          hiding (product)
import           Language.Hakaru.Runtime.Prelude
import           Language.Hakaru.Types.Sing
import qualified System.Random.MWC                as MWC
import           Control.Monad
import           Data.Number.LogFloat hiding (product)
import News (getNews)

{-
`prog` imported from NaiveBayes.hs has this type:

prog
  :: Vector Double  -- prior probability of each topic
  -> Vector Double  -- prior probability of each word
  -> Vector Int     -- topics, indexed by document
  -> Vector Int     -- words, indexed by token position
  -> Vector Int     -- document, indexed by token position
  -> Int            -- index of the doc whose topic we'd like to update
  -> Measure Int    -- distribution over the updated topic
-}



-- |Step through documents, performing one Gibbs sampling iteration
-- on each to select a new topic. 
-- gibbsRound 
--      :: Vector Double        -- prior probability of each topic
--      -> Vector Double        -- prior probability of each word
--      -> Vector Int           -- topics, indexed by document 
--      -> Vector Int           -- words, indexed by token position
--      -> Vector Int           -- document, indexed by token position
--      -> Measure (Vector Int) -- distribution over the updated topic
-- gibbsRound zPrior wPrior z w d = Measure $ \g -> do
--   let
--     numTokens = V.length z
--     loop i mz = 
--       if i == numTokens then Just <$> V.unsafeFreeze mz
--       else do
--         z <- V.unsafeFreeze mz
--         maybeTopic <- unMeasure (prog zPrior wPrior z w d i) g
--         case maybeTopic of
--           Nothing -> return Nothing
--           Just topic -> do
--             mz' <- V.unsafeThaw z
--             MV.write mz' i topic
--             loop (i + 1) mz'
--   loop 0 =<< V.thaw z
-- 
-- -- |Wrap 'gibbsRound' for simple testing
-- next :: Vector Int -> Measure (Vector Int)
-- next z = gibbsRound zPrior wPrior z w d
--   where
--   r = replicate 5
--   zPrior = V.fromList [1,1]
--   wPrior = V.fromList [1,1,1]
--   w      = V.fromList $ r 0 ++ r 1 ++ r 0 ++ r 2
--   d      = V.fromList $ r 0 ++ r 0 ++ r 1 ++ r 1

z0 :: Vector Int
z0 = V.fromList [0,1]

-- | Build a vector of ones with length given by the maximal element of a given vector.
-- 
onesFrom :: Vector Int -> Vector Double
onesFrom v = V.replicate (V.maximum v + 1) 1

-- |Make it easier to draw a sample
sample g m = do
  maybeX <- unMeasure m g
  case maybeX of
    Nothing -> fail "Sample rejected"
    Just x  -> return x

-- |Draw an infinite stream of samples, passing each to the action 'k'
withGen 
  :: MWC.GenIO
  -> (x -> IO a)
  -> Measure x
  -> IO a
withGen g k m = k =<< sample g m