module Tracklets where

import Control.Applicative
import Control.Monad
import Data.Maybe
import Data.Dynamic (toDyn)
import Foreign.Marshal.Utils (fromBool)

import Util.Csv

import System.Random
import System.IO.Unsafe (unsafePerformIO)

import qualified Data.Map.Strict as M
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as VU
import qualified Data.Sequence as S
import qualified Data.Foldable as F
import qualified Data.List as L
import qualified Data.Array.Unboxed as AU

import Data.Algorithm.Munkres

import InterpreterDynamic (logit)
import InterpreterMH hiding (main)

type EID = Double
type Timestamp = Double

data Point = Point { eid :: EID
                   -- , uid :: Double
                   -- , frame :: Int
                   , timestamp :: Timestamp
                   -- , pX :: Double
                   -- , pY :: Double
                   -- , ulX :: Int
                   -- , ulY :: Int
                   -- , lrX :: Int
                   -- , lrY :: Int
                   , worldX :: Double
                   , worldY :: Double
                   -- , worldZ :: Double
                   -- , gcs :: Int
                   , velocityX :: Double
                   , velocityY :: Double
                   } deriving (Eq) -- Show

toPoint :: V.Vector (Maybe Double) -> Point
toPoint v = Point
            (get 0)
            -- (get 1)
            -- (get 2)
            (get 3)
            -- (get 4)
            -- (get 5)
            -- (get 6)
            -- (get 7)
            -- (get 8)
            -- (get 9)
            (get 10)
            (get 11)
            -- (get 12)
            -- (get 13)
            (get 14)
            (get 15)
    where get n = fromJust $ v V.! n

instance Show Point where
    show (Point e t _ _ _ _) = "Point {"++ show e ++ "," ++ show t ++ "}"

points :: M.Map EID (S.Seq Point)
points = M.fromAscListWith (flip (S.><))
         [ (eid p, S.singleton p) 
               | v <- unsafePerformIO (decodeFileStream fullSet),
                      let p = toPoint v, valid v ]

instance Ord Point where
    compare p1 p2 = compare (timestamp p1) (timestamp p2)

type Tracklet = (Point,Point)

toTracklet :: S.Seq Point -> Tracklet
toTracklet s 
    | S.null s = error "toTracklet : empty sequence of points"
    | otherwise = (start,end)
    where len = S.length s
          start = S.index s 0
          end = S.index s (len-1)

npieces :: Int
npieces = 2

tracklets :: IO (M.Map (Timestamp,Timestamp) [Tracklet])
tracklets = liftM (M.fromListWith (++) . concat) $ mapM convert (M.elems points)
    where timeTrack tlet = (tStamps tlet, [tlet])
          convert = liftM (map $ timeTrack . toTracklet) . randomPieces npieces . S.unstableSort

-- (srcTracklet,destTracklet), i.e., order matters for track linking
type TlPair = (Tracklet,Tracklet)

data Info = Info { known :: [(Bool,TlPair)] 
                 , unknown :: [TlPair] 
                 } deriving (Show)

updateKnown :: Info -> (Bool,TlPair) -> Info
updateKnown (Info k u) obs = Info (obs:k) u

updateUnknown :: Info -> TlPair -> Info
updateUnknown (Info k u) p = Info k (p:u)

classify :: Info -> TlPair -> Info
classify info p@(t,u)
    | endTime t >= startTime u || sameID = updateKnown info (sameID, p)
    | otherwise = updateUnknown info p
    where sameID = tID t == tID u

information :: IO Info
information = do
  tmap <- tracklets
  let build info ts =
          let info' = foldl (\i -> updateKnown i . (,) False) info $ pairs ts
              (_,laterTracklets) = M.split (tStamps $ head ts) tmap
              bar ts' newInfo t = foldl classify newInfo $ zip (repeat t) ts'
              foo i ts' = foldl (bar ts') i ts
          in M.foldl foo info' laterTracklets
  return $ M.foldl build (Info [] []) tmap

nfeatures :: Int
nfeatures = 2

link :: [TlPair] -> [TlPair] -> Measure Double
link observed unknowns = do
  weight <- unconditioned (normal 0 1)
  let score (tlet,tlet') = 
          let tmin = (startTime tlet' - endTime tlet) / 2
              dist = l2Norm $ zipWith (-)
                     (extrapolate (fst tlet') (-1 + tmin))
                     (extrapolate (snd tlet) tmin)
          in exp (-dist*dist / (2*weight*weight)) -- weight * dist
      transition p = bern $ logit (score p)
  forM_ observed (\p -> conditioned $ transition p)
  -- liftM (map fromBool) $ 
  forM_ unknowns (\p -> unconditioned $ transition p)
  -- return $ map score $ take 50 unknowns
  return weight

nsamples :: Int
nsamples = 1000

-- stitch :: IO [(EID,EID)]
-- stitch = do
--   info <- information >>= curate
--   let unknowns = unknown info
--       (conds,observed) = getConds info
--   samples <- liftM (take nsamples) $ mcmc (link observed unknowns) $ conds
--   let weights = map ((/).fromIntegral $ length samples) $ foldl1 (zipWith (+)) samples      
--   return $ hungarian unknowns weights

main :: IO ()
main = infoTest
 
-------------------- Helpers

fullSet, testSet1, testSet2 :: FilePath

fullSet = "../problems/tracklets/tracks/computed-tracks-v1.csv"
testSet1 = "../problems/tracklets/tracks/test.csv"
testSet2 = "../problems/tracklets/tracks/test2.csv"

valid :: V.Vector (Maybe Double) -> Bool
valid v = all isJust $ map (v V.!) [0,3,10,11,14,15]

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

-- Given a sequence, return a *sorted* sequence of
-- n randomly selected elements from *distinct positions* in the sequence
-- Assume n <= seq length

randomElems :: Ord a => S.Seq a -> Int -> IO (S.Seq a)
randomElems = randomElemsTR S.empty

randomElemsTR :: Ord a => S.Seq a -> S.Seq a -> Int -> IO (S.Seq a)
randomElemsTR ixs s n
    | n == 1 = do (_,i) <- fmap fromJust (randomExtract s)
                  return.S.unstableSort $ i S.<| ixs
    | otherwise = do (s',i) <- fmap fromJust (randomExtract s)
                     randomElemsTR (i S.<| ixs) s' (n-1)

-- Chop a sequence at the given indices
-- Assume number of indices given < length of sequence to be chopped

pieces :: S.Seq a -> S.Seq Int -> [S.Seq a]
pieces s ixs = let f (ps,r,x) y = let (p,r') = S.splitAt (y-x) r
                                  in (p:ps,r',y)
                   g (a,b,_) = b:a
               in g $ F.foldl f ([],s,0) ixs

-- Given n, chop a sequence at m random points
-- where m = min (length-1, n-1)

randomPieces :: Int -> S.Seq a -> IO [S.Seq a]
randomPieces n s
    | n >= l = return $ F.toList $ fmap S.singleton s
    | otherwise = do ixs <- randomElems (S.fromList [1..l-1]) (n-1)
                     return $ pieces s ixs
    where l = S.length s

curate :: Info -> IO Info
curate pre@(Info k u)
    | flen > tlen = do putStr "Curating gathered information..."
                       ixs <- randomElems (S.fromList [0..flen-1]) tlen
                       ixs' <- randomElems (S.fromList [0..ulen - 1]) (ulen `div` 10)
                       let post = Info (t ++ subsample f ixs) (subsample u ixs')
                       putStrLn " done." >> return post
    | otherwise = return pre
    where (t,f) = L.partition fst k
          (flen,tlen) = (length f, length t)
          ulen = length u
          subsample ls ixs = map (ls !!) $ F.toList ixs

pairsTR :: [a] -> [(a,a)] -> [(a,a)]
pairsTR [] ps = ps
pairsTR (x:xs) ps = pairsTR xs $ (zip (repeat x) xs) ++ ps

pairs :: [a] -> [(a,a)]
pairs ls = pairsTR ls []

tID :: Tracklet -> EID
tID = eid.fst

tStamps :: Tracklet -> (Timestamp,Timestamp)
tStamps (start,end) = (timestamp start, timestamp end)

startTime :: Tracklet -> Timestamp
startTime = fst . tStamps

endTime :: Tracklet -> Timestamp
endTime = snd . tStamps

extrapolate :: Point -> Double -> [Double]
extrapolate p tmin
    = let vels = [velocityX p, velocityY p]
          pos = [worldX p, worldY p]
      in zipWith (+) pos $ map (*tmin) vels

getConds :: Info -> ([Cond],[TlPair])
getConds (Info k _) = let (bs,ps) = unzip k in (map (Just . toDyn) bs, ps)

l2Norm :: Floating a => [a] -> a
l2Norm l = sqrt.sum $ zipWith (*) l l

hungarian :: [TlPair] -> [Double] -> [(EID, EID)]
hungarian unknowns weights
    = let ids = VU.fromList $ M.keys points
          getIx tlet = (+) 1 $ fromJust $ VU.elemIndex (tID tlet) ids
          f acc ((t,u),w) = ((getIx t, getIx u), 1-w) :
                            ((getIx u, getIx t), 1) : acc
          alist = foldl f [] $ zip unknowns weights
          arr = AU.array ((1,1),(VU.length ids,VU.length ids)) alist
          (ixs,_) = hungarianMethodDouble arr
          getId ix = ids VU.! (ix - 1)
      in map ( \(a,b) -> (getId a, getId b) ) ixs

-------------------- Tests

linkTest :: IO ()
linkTest = do 
  info <- information >>= curate
  let (conds,observed) = getConds info
  samples <- liftM (take nsamples) $ mcmc (link observed $ unknown info) $ conds
  mapM_ print $ filter (\(i,_) -> i `mod` (nsamples`div`20) == 0) $ zip [1..] samples

infoTest :: IO ()
infoTest = do
  info <- information >>= curate
  let (k,u) = (known info, unknown info)
  -- print $ length k + length u
  print $ length $ filter fst k
  print $ length $ filter (not.fst) k
  print $ length u
  -- print $ take 50 $ filter fst k
  -- print $ take 50 u

