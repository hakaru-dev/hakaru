module Tracklets0 where

import Control.Monad
import Data.Maybe
import Data.Dynamic (toDyn)

import Data.Csv
import System.Environment (getArgs, getProgName)
import System.IO (stderr, hPutStrLn)
import System.Exit (exitFailure)

import qualified Data.Map.Strict as M
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as VU
import qualified Data.Sequence as S
import qualified Data.Foldable as F
import qualified Data.List as L
import qualified Data.Array.Unboxed as AU
import qualified Data.Set as Set
import qualified Data.ByteString.Lazy as B
import qualified Data.ByteString as BNL

import Data.Algorithm.Munkres
import qualified Data.UnionFind.IO as UF

import InterpreterDynamic
import Types (Cond(..))
import Mixture
import Util.Csv
import Util.Extras

npieces, nsamples, frameThreshold, nIds :: Int

npieces = 2
nsamples = 6000
frameThreshold = 70
nIds = 638 -- * 3

type EID = Int
type Timestamp = Integer

data DataRow = TrackHeader EID | Track Point

data Point = Point { eid :: EID
                   -- , uid :: Int
                   , frame :: Int
                   , timestamp :: Timestamp
                   , pX :: Double
                   , pY :: Double
                   , ulX :: Double
                   , ulY :: Double
                   , lrX :: Double
                   , lrY :: Double
                   , worldX :: Double
                   , worldY :: Double
                   , worldZ :: Double
                   , gcs :: Double
                   , velocityX :: Double
                   , velocityY :: Double
                   } deriving (Eq, Show)

points :: FilePath -> IO (M.Map EID (S.Seq Point))
points path = do
  dat <- decodeFileStream path
  return $ M.fromListWith (flip (S.><))
         [ (eid p, S.singleton p) | v <- dat, let p = toPoint v, valid v
                                         -- p <- [q, updateEID (638 + eid q) q
                                         --      , updateEID (638*2 + eid q) q]
         ]

instance Ord Point where
    compare p1 p2 = compare (timestamp p1) (timestamp p2)

-- | (startPoint, endPoint)
type Tracklet = (Point,Point)

tracklets :: FilePath -> IO (M.Map (Timestamp,Timestamp) [Tracklet])
tracklets path = liftM (M.fromListWith (++) . concat) $ points path >>= mapM convert . M.elems
    where timeTrack tlet = (tStamps tlet, [tlet])
          convert = liftM (map $ timeTrack . toTracklet) . randomPieces npieces . S.unstableSort

-- |(srcTracklet,destTracklet), i.e., order matters for track linking
type TlPair = (Tracklet,Tracklet)

data Info = Info { known :: [(Bool,TlPair)] 
                 , unknown :: [TlPair] 
                 } deriving (Show)

classify :: Info -> TlPair -> Info
classify info p@(t,u)
    | endTime t >= startTime u || sameID = updateKnown info (sameID, p)
    | frameDiff <= frameThreshold = updateUnknown info p
    | otherwise = info
    where sameID = tID t == tID u
          frameDiff = abs (frame (fst u) - frame (snd t))
                   
information :: FilePath -> IO Info
information path = do
  tmap <- tracklets path
  let build info ts =
          let info' = foldl (\i -> updateKnown i . (,) False) info $ pairs ts
              (_,laterTracklets) = M.split (tStamps $ head ts) tmap
              bar ts' newInfo t = foldl classify newInfo $ zip (repeat t) ts'
              foo i ts' = foldl (bar ts') i ts
          in M.foldl foo info' laterTracklets
      info = M.foldl build (Info [] []) tmap
  return info 

link :: [TlPair] -> Measure [Double]
link observed = do
  w0 <- unconditioned (normal 0 10)
  w1 <- unconditioned (normal 0 1e-5)
  w2 <- unconditioned (normal 0 10)
  let transition p = bern $ score [w0,w1,w2] p
  forM_ observed (\p -> conditioned $ transition p)
  return [w0,w1,w2]

score :: [Double] -> TlPair -> Double
score [w0,w1,w2] (tlet,tlet') = 
    let (t1,t2) = pairMap fromIntegral (endTime tlet , startTime tlet')
        tmin = (t2-t1) / 2
        (p1,p2) = (snd tlet, fst tlet')
        loc p = [worldX p, worldY p]
        d = zipWith (-) (loc p2) (loc p1)
        dist = l2Norm $ zipWith (-)
               (extrapolate (fst tlet') (-1 + tmin))
               (extrapolate (snd tlet) tmin)
        fdist = fromIntegral $ frame (fst tlet') - frame (snd tlet)
    in logit $ w0 + w1*dist + w2*fdist

-- logit $ w0 + (sum $ zipWith (*) [w1,w2] d)

matching :: FilePath -> IO [(EID,EID)]
matching path = do
  info <- information path >>= curate
  let unknowns = unknown info
      (conds,observed) = getConds info
  mix <- sample nsamples (link observed) $ conds
  let modeWeight = fst $ mode mix
      edgeWeights = map (score modeWeight) unknowns
  return $ hungarian unknowns edgeWeights

stitch :: [(EID,EID)] -> IO (M.Map EID [EID])
stitch eidPairs = do
  eqClasses <- V.mapM UF.fresh $ V.fromList [fromIntegral i | i <- [1..nIds]]
  let getElem i = eqClasses V.! (i-1)
  forM_ eidPairs (\(id1,id2) -> UF.union (getElem id1) (getElem id2))
  keys <- V.mapM UF.descriptor eqClasses
  return $ M.fromListWith (++) $ zip (V.toList keys) [[fromIntegral i] | i <- [1..nIds]]

output :: FilePath -> M.Map EID (S.Seq Point) -> M.Map EID [EID] -> IO ()
output path pts tracks = do
  let addTracklet tId eId ls
                = let t = F.toList.S.unstableSort.fromJust.M.lookup eId $ pts
                  in (map (Track . updateEID tId) t) ++ ls
      gatherTracklets tId = foldr (addTracklet tId) []
      addTrack tId eIds ls = trackHeader tId : (gatherTracklets tId eIds) ++ ls
      bytestring = encode $ M.foldrWithKey addTrack [] tracks
  B.writeFile path bytestring

main :: IO ()
main = do
  args <- getArgs
  case args of
    [inputFile, outputFile] -> do pts <- points inputFile
                                  matches <- putStrLn "Gathering info and matching..." >> matching inputFile
                                  tracks <- putStrLn "Stitching together tracklets..." >> stitch matches 
                                  putStr "Writing output... " >> output outputFile pts tracks >> putStrLn "done."
    _ -> do progName <- getProgName
            hPutStrLn stderr ("Usage: " ++ progName ++ " <inputFile> <outputFile>")
            hPutStrLn stderr ("Example: " ++ progName 
                              ++ " \\\n\
                                 \\t\tinput/computed-tracks-v1.csv \\\n\
                                 \\t\toutput/computed-tracks.csv")
            exitFailure
   
-------------------- Helpers

toPoint :: V.Vector (Maybe Double) -> Point
toPoint v = Point
            (truncate $ get 0)
            -- (get 1)
            (truncate $ get 2)
            (toInteger.truncate $ get 3)
            (get 4)
            (get 5)
            (get 6)
            (get 7)
            (get 8)
            (get 9)
            (get 10)
            (get 11)
            (get 12)
            (get 13)
            (get 14)
            (get 15)
    where get n = fromJust $ v V.! n

instance ToRecord Point where
    toRecord (Point e f t px py 
                    ulx uly lrx lry 
                    wx wy wz gcs vx vy) 
        = record $ 
          (toField e) : BNL.empty : (toField f) :
          (toField t) : map toField [px,py,ulx,uly,lrx,lry,wx,wy,wz,gcs,vx,vy]

instance ToRecord DataRow where
    toRecord (TrackHeader eId)
        = record $ map toField $ Just eId : replicate 15 Nothing
    toRecord (Track p) = toRecord p

valid :: V.Vector (Maybe Double) -> Bool
valid v = all isJust $ map (v V.!) $ 0:[2..15]

trackHeader :: EID -> DataRow
trackHeader eId = TrackHeader eId

updateEID :: EID -> Point -> Point
updateEID e p = p { eid = e }

toTracklet :: S.Seq Point -> Tracklet
toTracklet s 
    | S.null s = error "toTracklet : empty sequence of points"
    | otherwise = (start,end)
    where len = S.length s
          start = S.index s 0
          end = S.index s (len-1)

updateKnown :: Info -> (Bool,TlPair) -> Info
updateKnown (Info k u) obs = Info (obs:k) u

updateUnknown :: Info -> TlPair -> Info
updateUnknown (Info k u) p = Info k (p:u)

pairMap :: (a -> b) -> (a,a) -> (b,b)
pairMap f (x,y) = (f x, f y)

lineMap :: (a -> b) -> (a,a,a,a) -> (b,b,b,b)
lineMap f (w,x,y,z) = (f w, f x, f y, f z)

hungarian :: [TlPair] -> [Double] -> [(EID, EID)]
hungarian unknowns weights
    = let addId (t,u) s = Set.insert (tID t) $ Set.insert (tID u) s
          ids = VU.fromList.Set.toList $ foldr addId Set.empty unknowns
          getIx tlet = (+) 1 $ fromJust $ VU.elemIndex (tID tlet) ids
          boundary comp (a,b) (c,d) = (comp a c, comp b d)
          f ((t,u),w) (ls,(lb,ub))
              = let ix@(tix,uix) = (getIx t, getIx u)
                    bounds = (boundary min lb ix, boundary max ub ix)
                in ( ((tix,uix),1-w) : ls , bounds )
          (alist,(lb,ub)) = foldr f ( [] , ((nIds,nIds),(1,1)) ) $ zip unknowns weights
          bounds = let mi = min (fst lb) (snd lb)
                       ma = max (fst ub) (snd ub) 
                   in ((mi,mi),(ma,ma))
          arr = AU.accumArray (\o new -> new) 12 bounds alist
          (ixs,_) = hungarianMethodDouble arr
          getId ix = ids VU.! (ix - 1)
      in map (pairMap getId) ixs

plotTracks :: M.Map EID (S.Seq Point) -> M.Map EID [EID] -> IO ()
plotTracks pts clusters = do
  let m = M.filter (\l-> length l > 8) clusters
  randKey <- liftM (snd.fromJust) $ randomExtract $ S.fromList $ M.keys m
  putStrLn $ "void setup() { size(4000,8000); background(225); fill(255); noLoop();"
  forM_ (fromJust $ M.lookup randKey clusters) (plotTracklet pts)
  putStrLn "}"

plotTracklet :: M.Map EID (S.Seq Point) -> EID -> IO ()
plotTracklet pts eId = do
  let tracklet = S.unstableSort . fromJust . M.lookup eId $ pts
      (_ S.:< rest) = S.viewl tracklet
      line (p1,p2) = lineMap coordTransform (worldX p1, worldY p1, worldX p2, worldY p2)
      showLine l = "line" ++ show l ++ ";"
  putStrLn $ "//" ++ show eId
  F.forM_ (S.zip tracklet rest) (putStrLn.showLine.line)
  putStrLn ""

coordTransform :: Double -> Double
coordTransform p = flip (/) 10 $ fromIntegral $ truncate ((abs p)*10^6) `mod` 10^5

curate :: Info -> IO Info
curate pre@(Info k u)
    | flen > tlen = do ixs <- randomElems (S.fromList [0..flen-1]) tlen
                       return $ Info (t ++ subsample f ixs) u
    | otherwise = return pre
    where (t,f) = L.partition fst k
          (flen,tlen) = (length f, length t)
          ulen = length u
          subsample ls ixs | S.length ixs >= length ls = ls
                           | otherwise = map (ls !!) $ F.toList ixs

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
getConds (Info k _) = let (bs,ps) = unzip k in (map (Discrete . toDyn) bs, ps)

-------------------- Tests

fullSet, testSet1, testSet2 :: FilePath
  
fullSet = "../problems/tracklets/tracks/computed-tracks-v1.csv"
testSet1 = "../problems/tracklets/tracks/test.csv"
testSet2 = "../problems/tracklets/tracks/test2.csv"

linkTest :: IO ()
linkTest = do 
  info <- information fullSet >>= curate
  let (conds,observed) = getConds info
  sample_ 1000 (link observed) $ conds

infoTest :: IO ()
infoTest = do
  info <- information fullSet >>= curate
  let (k,u) = (known info, unknown info)
  print $ length $ filter fst k
  print $ length $ filter (not.fst) k
  print $ length u

stitchTest :: IO ()
stitchTest = do
  matching fullSet >>= stitch >>= print

plotTest :: IO ()
plotTest = do
  pts <- points fullSet
  matching fullSet >>= stitch >>= plotTracks pts

