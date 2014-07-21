{-|
  Functions on lists and sequences.
  Some of the functions follow the style of Data.Random.Extras 
  (from the random-extras package), but are written for use with
  PRNGs from System.Random rather than from the random-fu package.
-}

module Language.Hakaru.Util.Extras where

import qualified Data.Sequence as S
import System.Random
import Data.Maybe
import qualified Data.Foldable as F

extract :: S.Seq a -> Int -> Maybe (S.Seq a, a)
extract s i | S.null r = Nothing
            | otherwise  = Just (a S.>< c, b)
    where (a, r) = S.splitAt i s 
          (b S.:< c) = S.viewl r

randomExtract :: S.Seq a -> IO (Maybe (S.Seq a, a))
randomExtract s = do
  g <- newStdGen
  let (i,_) = randomR (0, S.length s - 1) g
  return $ extract s i

{-| 
  Given a sequence, return a *sorted* sequence of
  n randomly selected elements from *distinct positions* in the sequence
-}

randomElems :: Ord a => S.Seq a -> Int -> IO (S.Seq a)
randomElems = randomElemsTR S.empty

randomElemsTR :: Ord a => S.Seq a -> S.Seq a -> Int -> IO (S.Seq a)
randomElemsTR ixs s n
    | n == S.length s = return $ S.unstableSort s
    | n == 1 = do (_,i) <- fmap fromJust (randomExtract s)
                  return.S.unstableSort $ i S.<| ixs
    | otherwise = do (s',i) <- fmap fromJust (randomExtract s)
                     (randomElemsTR $! (i S.<| ixs)) s' (n-1)

{-|
  Chop a sequence at the given indices. 
  Assume number of indices given < length of sequence to be chopped
-}

pieces :: S.Seq a -> S.Seq Int -> [S.Seq a]
pieces s ixs = let f (ps,r,x) y = let (p,r') = S.splitAt (y-x) r
                                  in (p:ps,r',y)
                   g (a,b,_) = b:a
               in g $ F.foldl f ([],s,0) ixs

{-|
  Given n, chop a sequence at m random points
  where m = min (length-1, n-1)
-}

randomPieces :: Int -> S.Seq a -> IO [S.Seq a]
randomPieces n s
    | n >= l = return $ F.toList $ fmap S.singleton s
    | otherwise = do ixs <- randomElems (S.fromList [1..l-1]) (n-1)
                     return $ pieces s ixs
    where l = S.length s

{-|
  > pairs [1,2,3,4]
  [(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
  > pairs [1,2,4,4]
  [(1,2),(1,4),(1,4),(2,4),(2,4),(4,4)]
-}

pairs :: [a] -> [(a,a)]
pairs [] = []
pairs (x:xs) = (zip (repeat x) xs) ++ pairs xs

l2Norm :: Floating a => [a] -> a
l2Norm l = sqrt.sum $ zipWith (*) l l