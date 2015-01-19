{-# LANGUAGE DataKinds, GADTs, MultiParamTypeClasses,
             FlexibleInstances, StandaloneDeriving, 
             GeneralizedNewtypeDeriving, FlexibleContexts #-}

-- {-# OPTIONS_GHC -ftype-function-depth=400 #-}
-- {-# OPTIONS_GHC -fcontext-stack=400 #-}

-- | Relevant paper: 
-- Jose Guivant, Eduardo Nebot, and Stephan Baiker. Autonomous navigation and map 
-- building using laser range sensors in outdoor applications. 
-- Journal of Robotic Systems, 17(10):565–583, Oct. 2000.

module Slam where

import Prelude as P
import Control.Monad as CM
import Language.Hakaru.Syntax as H
import Language.Hakaru.Disintegrate
import qualified System.Random.MWC as MWC
import Language.Hakaru.Sample    
import Language.Hakaru.Vector as HV
import Control.Monad.Cont (runCont, cont)
import qualified Data.Sequence as S
import qualified Data.Foldable as F
import Control.Monad.Primitive (PrimState, PrimMonad)

-- Stuff for Data IO
import Text.Printf    
import System.Exit    
import System.Directory
import System.Environment
import System.FilePath
import Language.Hakaru.Util.Csv (decodeFileStream)
import Data.Csv
import qualified Control.Applicative as A
import qualified Data.Vector as V
import qualified Data.ByteString.Lazy as B
    
----------
-- Inputs
----------
-- 
-- Inputs per timestamp:
-------------------------
-- 1. v_e : speed (Either this or what the paper calls v_c)
-- 2. alpha: steering angle
-- 3. z_rad_i : distances to object i
-- 4. z_I_i : intensity from objects i
-- 5. z_beta_i : angle to object i
--
-- Starting input (starting state):
------------------------------------
-- 1. GPSLon, GPSLat
-- 2. initial angle (alpha) 
-- 3. dimensions of vehicle (L,h,a,b)
--
--
-----------
-- Outputs
-----------
-- 1. GPSLon, GPSLat
-- 2. phi : world angle
-- 3. (x_i, y_i) : world coords (lon, lat) of each object i in the map
                         
type One = I
type Two = D One
type Three = SD One
type Four = D Two
type Five = SD Two
type Six = D Three
type Seven = SD Three
type Eight = D Four
type Nine = SD Four
type Ten = D Five
type Eleven = SD Five
type ThreeSixtyOne = SD (D (D (SD (D Eleven))))             

range :: Int
range = 361

shortrange :: Int
shortrange = 11             
type Len = Eleven
    
type ZRad = H.Real  -- ^ Observed radial distance to a beacon
type ZInt = H.Real  -- ^ Observed light intensity (reflected) from a beacon
type GPS = H.Real
type Angle = H.Real -- ^ In radians
type Vel = H.Real    
type DelTime = H.Real
type DimL = H.Real
type DimH = H.Real
type DimA = H.Real
type DimB = H.Real
             
type State = ( (Repeat Len ZRad, Repeat Len ZInt)
             , (Angle, (GPS, GPS)) )

type Simulator repr = repr DimL -> repr DimH -> repr DimA -> repr DimB
                    -> repr [GPS] -> repr [GPS] -- ^ beacon lons, beacon lats
                    -> repr GPS -> repr GPS -> repr Angle -- ^ vehLon, vehLat, phi
                    -> repr Vel -> repr Angle -- ^ vel, alpha
                    -> repr DelTime           -- ^ timestamp
                    -> repr (Measure State)    

simulate :: (Mochastic repr) => Simulator repr
simulate dimL dimH dimA dimB
         blons blats
         old_lon old_lat old_phi
         old_ve old_alpha delT =

    let_' (old_ve / (1 - (tan old_alpha)*dimH/dimL)) $ \old_vc ->
    let_' (calcLon dimA dimB dimL old_lon delT old_vc old_phi old_alpha) $
              \calc_lon ->
    let_' (calcLat dimA dimB dimL old_lat delT old_vc old_phi old_alpha) $
              \calc_lat ->
    let_' (old_phi + delT*old_vc*(tan old_alpha) / dimL) $ \calc_phi ->
    
    normal calc_lon ((*) cVehicle . sqrt_ . unsafeProb $ delT) `bind` \noisy_lon ->
    normal calc_lat ((*) cVehicle . sqrt_ . unsafeProb $ delT) `bind` \noisy_lat ->
    normal calc_phi ((*) cVehicle . sqrt_ . unsafeProb $ delT) `bind` \noisy_phi ->

    let_' (map_ ((-) noisy_lon) blons) $ \lon_ds ->
    let_' (map_ ((-) noisy_lat) blats) $ \lat_ds ->
        
    let_' (map_ sqrt_ (zipWith_ (+) (map_ sqr lon_ds)
                                    (map_ sqr lat_ds))) $ \calc_zrads ->
    -- inverse-square for intensities 
    let_' (map_ (\r -> cIntensity / (pow_ r 2)) calc_zrads) $ \calc_zints ->
    let_' (map_ (\r -> atan r - calc_phi)  -- removed a "+ pi/2" term
                (zipWith_ (/) lat_ds lon_ds)) $ \calc_zbetas ->

    perturb (\l -> normal (fromProb l) cBeacon) calc_zrads `bind` \noisy_zrads ->
    perturb (\l -> normal (fromProb l) cBeacon) calc_zints `bind` \noisy_zints ->
    perturb (\l -> normal l cBeacon) calc_zbetas `bind` \noisy_zbetas ->

    extractMeasure (HV.pure (normal muZRads sigmaZRads)) `bind` \zrad_base ->
    let_' (laserAssigns zrad_base shortrange noisy_zrads noisy_zbetas) $ \zrad_reads ->

    extractMeasure (HV.pure (normal muZInts sigmaZInts)) `bind` \zint_base ->
    let_' (laserAssigns zint_base shortrange noisy_zints noisy_zbetas) $ \zint_reads ->
        
    dirac $ pair (pair zrad_reads zint_reads)
                 (pair noisy_phi (pair noisy_lon noisy_lat))

calcLon :: (Base repr) => repr DimA -> repr DimB -> repr DimL
        -> repr GPS                 -- ^ old_lon
        -> repr DelTime -> repr Vel -- ^ delT, old_vc
        -> repr Angle -> repr Angle -- ^ old_phi, old_alpha
        -> repr GPS
calcLon dimA dimB dimL old_lon delT old_vc old_phi old_alpha =
    old_lon + delT * (old_vc*(cos old_phi)
                      - (old_vc
                         * (dimA*(sin old_phi) + dimB*(cos old_phi))
                         * (tan old_alpha) / dimL))

calcLat :: (Base repr) => repr DimA -> repr DimB -> repr DimL
        -> repr GPS                 -- ^ old_lat
        -> repr DelTime -> repr Vel -- ^ delT, old_vc
        -> repr Angle -> repr Angle -- ^ old_phi, old_alpha
        -> repr GPS
calcLat dimA dimB dimL old_lat delT old_vc old_phi old_alpha =
    old_lat + delT * (old_vc*(sin old_phi)
                      - (old_vc
                         * (dimA*(cos old_phi) + dimB*(sin old_phi))
                         * (tan old_alpha) / dimL))
    
cVehicle :: (Base repr) => repr Prob
cVehicle = 0.42

cBeacon :: (Base repr) => repr Prob
cBeacon = 0.37

cIntensity :: (Base repr) => repr Prob
cIntensity = 19

muZRads :: (Base repr) => repr H.Real
muZRads = 40

sigmaZRads :: (Base repr) => repr Prob
sigmaZRads = 1

muZInts :: (Base repr) => repr H.Real
muZInts = 40

sigmaZInts :: (Base repr) => repr Prob
sigmaZInts = 1

sqr :: (Base repr) => repr H.Real -> repr Prob
sqr a = unsafeProb $ a * a  -- pow_ (unsafeProb a) 2

let_' :: (Mochastic repr)
         => repr a -> (repr a -> repr (Measure b)) -> repr (Measure b)
let_' = bind . dirac

toHList :: (Base repr) => [repr a] -> repr [a]
toHList [] = nil
toHList (a : as) = cons a (toHList as)

map_ :: (Base repr) => (repr a -> repr b) -> repr [a] -> repr [b]
map_ f ls = unlist ls nil k
    where k a as = cons (f a) (map_ f as)

zipWith_ :: (Base repr) => (repr a -> repr b -> repr c)
         -> repr [a] -> repr [b] -> repr [c]
zipWith_ f al bl = unlist al nil k
    where k  a as = unlist bl nil (k' a as)
          k' a as b bs = cons (f a b) (zipWith_ f as bs)

foldl_ :: (Base repr) => (repr b -> repr a -> repr b)
       -> repr b -> repr [a] -> repr b
foldl_ f acc ls = unlist ls acc k
    where k a as = foldl_ f (f acc a) as

sequence' :: (Mochastic repr) => repr [Measure a] -> repr (Measure [a])
sequence' ls = unlist ls (dirac nil) k
    where k ma mas = bind ma $ \a ->
                     bind (sequence' mas) $ \as ->
                     dirac (cons a as)                           
                 
withinLaser n b = and_ [ lessOrEq (convert (n-0.5)) tb2
                       , less tb2 (convert (n+0.5)) ]           
    where lessOrEq a b = or_ [less a b, equal a b]
          tb2 = tan (b/2)
          toRadian d = d*pi/180
          ratio = fromRational $ fromIntegral range / fromIntegral shortrange
          convert = tan . toRadian . ((/) 4) . ((*) ratio)

-- | Insert sensor readings (radial distance or intensity)
-- from a list containing one reading for each beacon (reads; length = n)
-- into the correct indices (i.e., angles derived from betas) within
-- a hakaru vector of "noisy" readings (base; length = (short)range)
laserAssigns :: (Base repr) => repr (Repeat Len H.Real) -> Int
             -> repr [H.Real] -> repr [H.Real]
             -> repr (Repeat Len H.Real)
laserAssigns base n reads betas =
    let combined = zipWith_ pair reads betas
        laserNum i = fromRational $ fromIntegral i - (fromIntegral (n-1) / 2)
        addBeacon rb (m,i) = unpair rb $ \r b ->
                             if_ (withinLaser (laserNum i) b) r m
        build pd rb = fromNestedPair pd $ \p -> toNestedPair
                      ((addBeacon rb) <$> ((,) <$> p <*> (iota 0)))
    in foldl_ build base combined

-- | Add random noise to a hakaru list of elements
perturb :: Mochastic repr => (repr a -> repr (Measure a1))
        -> repr [a] -> repr (Measure [a1])
perturb fn ls = let ls' = map_ fn ls
                in sequence' ls'

-- | Add random noise to a hakaru vector (nested tuple) of elements
perturbReads fn ls = let ls' = fn <$> ls
                     in extractMeasure ls'

-- | Conversion helper
-- from: repr (Vector (Measure a))
-- to:   repr (Measure (Vector a))
-- Vector means Language.Hakaru.Vector, i.e., nested tuple
extractMeasure ls' = let mls' = cont . bind <$> ls'
                         seq' = HV.sequence mls'
                         rseq = runCont seq'
                     in rseq (dirac . toNestedPair)

type Step = DimL -> DimH -> DimA -> DimB
          -> [GPS] -> [GPS]
          -> GPS -> GPS -> Angle
          -> Vel -> Angle
          -> DelTime
          -> Measure State

type Particle = Sample' IO ( GPS -> GPS -> Angle
                             -> Vel -> Angle
                             -> DelTime
                             -> Measure State )
                                    
generate :: FilePath -> FilePath -> Maybe FilePath -> IO ()
generate input output eval = do
  g <- MWC.createSystemRandom
  (Init l h a b phi ilt iln) <- initialVals input
  controls <- controlData input
  sensors <- sensorData input
  (lons, lats) <- genBeacons g eval
             
  let lamExp :: (Mochastic repr, Lambda repr) => repr Step
      lamExp = lam $ \dl -> lam $ \dh -> lam $ \da -> lam $ \db -> 
               lam $ \blons -> lam $ \blats ->
               lam $ \old_lon -> lam $ \old_lat -> lam $ \old_phi ->
               lam $ \old_ve -> lam $ \old_alpha -> lam $ \delT ->
               simulate dl dh da db blons blats
                        old_lon old_lat old_phi
                        old_ve old_alpha delT
                               
      particle :: Particle
      particle = (unSample lamExp) l h a b lons lats
                  
  gen output g sensors 0 controls 0 particle (PM iln ilt phi 0 0 0)

type Rand = MWC.Gen (PrimState IO)
      
genBeacons :: Rand -> Maybe FilePath
           -> IO ([Double],[Double]) -- ^ longitudes, latitudes
genBeacons _ Nothing         = return ([1,3],[2,4])
genBeacons g (Just evalPath) = do
  trueBeacons <- obstacles evalPath
  return (map lon trueBeacons , map lat trueBeacons)

data Params = PM { vlon :: Double
                 , vlat :: Double
                 , phi :: Double
                 , vel :: Double
                 , alpha :: Double
                 , tm :: Double }         

type Generator = V.Vector Sensor -> Int
               -> V.Vector Control -> Int
               -> Particle
               -> Params
               -> IO ()                  
    
gen :: FilePath -> Rand -> Generator
gen out g sensors si controls ci particle
    (PM old_vlon old_vlat old_phi old_ve old_alpha tprev)
    | si >= V.length sensors = putStrLn "Finished reading input_sensor"
    | otherwise = do
  let (Sensor tcurr snum) = sensors V.! si
  s <- fmap (\(Just (s,1)) -> s) $
       particle old_vlon old_vlat old_phi old_ve old_alpha (tcurr-tprev) 1 g
  let (czrads, czints) = (\(a,b) -> (toList a, toList b)) $ fst s
      (cphi, (cvlon,cvlat)) = snd s
      newprms = case snum of
                  1 -> do putStrLn "writing to simulated_slam_out_path"
                          plotPoint out cvlon cvlat
                          return (ci, old_ve, old_alpha)
                  2 -> do when (ci >= V.length controls) $
                               error "input_control has fewer data than\
                                     \it should according to input_sensor"
                          let (Control _ nv nalph) = controls V.! ci
                          return (ci+1, nv, nalph)
                  3 -> do putStrLn "writing to simulated_input_laser"
                          plotReads out czrads czints
                          return (ci, old_ve, old_alpha)
                  _ -> error "Invalid sensor ID (must be 1, 2 or 3)"
  newprms >>= \(nci,nve,nal) -> gen out g sensors (si+1) controls nci particle
                                (PM cvlon cvlat cphi nve nal tcurr)

plotPoint :: FilePath -> Double -> Double -> IO ()
plotPoint out lon lat = do
  dExist <- doesDirectoryExist out
  unless dExist $ createDirectory out
  let fp = out </> "slam_out_path.txt"
  appendFile fp $ show lon ++ "," ++ show lat ++ "\n"

plotReads :: FilePath -> [Double] -> [Double] -> IO ()
plotReads out rads ints = do
  dExist <- doesDirectoryExist out
  unless dExist $ createDirectory out
  let file = out </> "slam_simulated_laser.txt"
  go file (rads ++ ints)
    where go fp []     = appendFile fp "\n"
          go fp [l]    = appendFile fp ((show l) ++ "\n")
          go fp (l:ls) = appendFile fp ((show l) ++ ",") >> go fp ls

type Env = (DimL,
            (DimH,
             (DimA,
              (DimB,
               ([GPS], ([GPS],
                        (GPS, (GPS, (Angle,
                                     (Vel, (Angle, DelTime)))))))))))
    
evolve :: (Mochastic repr) => repr Env
       -> [ repr (Repeat Len ZRad, Repeat Len ZInt)
            -> repr (Measure (Angle, (GPS, GPS))) ]
evolve env =
    [ d env
      | d <- runDisintegrate $ \ e0  ->
             unpair e0  $ \l     e1  ->
             unpair e1  $ \h     e2  ->
             unpair e2  $ \a     e3  ->
             unpair e3  $ \b     e4  ->
             unpair e4  $ \blons e5  ->
             unpair e5  $ \blats e6  ->
             unpair e6  $ \vlon  e7  ->
             unpair e7  $ \vlat  e8  ->
             unpair e8  $ \phi   e9  ->
             unpair e9  $ \vel   e10 ->
             unpair e10 $ \alpha del ->
             simulate l h a b
                      blons blats
                      vlon vlat phi
                      vel alpha del ]                         

main :: IO ()
main = do
  args <- getArgs
  case args of
    [input, output]       -> generate input output Nothing
    [input, output, eval] -> generate input output (Just eval)
    _ -> usageExit
    
usageExit :: IO ()
usageExit = do
  pname <- getProgName
  putStrLn (usage pname) >> exitSuccess
      where usage pname = "Usage: " ++ pname ++ " input_dir output_dir [eval_dir]\n"

                          
--------------------------------------------------------------------------------
--                                DATA IO                                     --
--------------------------------------------------------------------------------


data Initial = Init { l :: Double
                    , h :: Double
                    , a :: Double
                    , b :: Double
                    , initPhi :: Double
                    , initLat :: Double
                    , initLon :: Double } deriving Show

instance FromRecord Initial where
    parseRecord v
        | V.length v == 7 = Init   A.<$>
                            v .! 0 A.<*>
                            v .! 1 A.<*>
                            v .! 2 A.<*>
                            v .! 3 A.<*>
                            v .! 4 A.<*>
                            v .! 5 A.<*>
                            v .! 6
        | otherwise = fail "wrong number of fields in input_properties"
    
noFileBye :: FilePath -> IO ()
noFileBye fp = putStrLn ("Could not find " ++ fp) >> exitFailure

initialVals :: FilePath -> IO Initial
initialVals inpath = do
  let input = inpath </> "input_properties.csv"
  doesFileExist input >>= flip unless (noFileBye input)
  bytestr <- B.readFile input
  case decode HasHeader bytestr of
    Left msg -> fail msg
    Right v -> if V.length v == 1
               then return $ v V.! 0
               else fail "wrong number of rows in input_properties"

data Laser = L { timestamp :: Double
               , zrads :: V.Vector Double
               , intensities :: V.Vector Double }

instance FromRecord Laser where
    parseRecord v
        | V.length v == 1 + 2*range
            = L A.<$> v .! 0
              A.<*> parseRecord (V.slice 1 range v)
              A.<*> parseRecord (V.slice (range+1) range v)
        | otherwise = fail "wrong number of fields in input_laser"

laserReadings :: FilePath -> IO (V.Vector Laser)
laserReadings inpath = do
  let input = inpath </> "input_laser.csv"
  doesFileExist input >>= flip unless (noFileBye input)
  fmap V.fromList $ decodeFileStream input                        

data Sensor = Sensor {sensetime :: Double, sensorID :: Int} deriving (Show)

instance FromRecord Sensor where
    parseRecord v
        | V.length v == 2 = Sensor A.<$> v .! 0 A.<*> v .! 1
        | otherwise = fail "wrong number of fields in input_sensor"

sensorData :: FilePath -> IO (V.Vector Sensor)
sensorData inpath = do
  let input = inpath </> "input_sensor.csv"
  doesFileExist input >>= flip unless (noFileBye input)
  fmap V.fromList $ decodeFileStream input

data Control = Control { contime :: Double
                       , velocity :: Double
                       , steering :: Double } deriving (Show)

instance FromRecord Control where
    parseRecord v
        | V.length v == 3 = Control A.<$> v .! 0 A.<*> v .! 1 A.<*> v .! 2
        | otherwise = fail "wrong number of fields in input_control"

controlData :: FilePath -> IO (V.Vector Control)
controlData inpath = do
  let input = inpath </> "input_control.csv"
  doesFileExist input >>= flip unless (noFileBye input)
  fmap V.fromList $ decodeFileStream input       

-- | True beacon positions (from eval_data/eval_obstacles.csv for each path type)
-- This is for simulation purposes only!
-- Not to be used during inference
data Obstacle = Obstacle {lat :: Double, lon :: Double}

instance FromRecord Obstacle where
    parseRecord v
        | V.length v == 2 = Obstacle A.<$> v .! 0 A.<*> v .! 1
        | otherwise = fail "wrong number of fields in eval_obstacles"

obstacles :: FilePath -> IO [Obstacle]
obstacles evalPath = do
  let evalObs = evalPath </> "eval_obstacles.csv"
  doesFileExist evalObs >>= flip unless (noFileBye evalObs)
  decodeFileStream evalObs


                   
--------------------------------------------------------------------------------
--                               MISC MINI-TESTS                              --
--------------------------------------------------------------------------------


testIO :: FilePath -> IO ()
testIO inpath = do
  -- initialVals "test" >>= print
  laserReads <- laserReadings inpath
  print . (V.slice 330 31) . zrads $ laserReads V.! 50
  V.mapM_ ((printf "%.6f\n") . timestamp) $ V.take 10 laserReads
  sensors <- sensorData inpath
  putStrLn "-------- Here are some sensors -----------"
  print $ V.slice 0 20 sensors
  controls <- controlData inpath
  putStrLn "-------- Here are some controls -----------"
  print $ V.slice 0 20 controls

testHV :: IO ()
testHV = do
  let myList :: Repeat Three (Sample IO (H.Real, H.Real))
      myList = (\(a,b) -> pair a b) <$> HV.fromList [(1,2), (3,4), (5,6)]
  print (unSample $ toNestedPair myList)
  -- print myList
  print (unSample (toNestedPair ((+) <$>
                                 fromList [1,2,3] <*>
                                 fromList [100,200,300])
                   :: Sample IO (Repeat Three H.Real)))
        
vecTest :: IO ()
vecTest = do
  let a :: Repeat ThreeSixtyOne Int
      a = iota 0
      b = toList a
  print b

testLaser :: IO ()
testLaser = do
  let base :: (Base repr) => repr (Repeat Eleven H.Real)
      base =  toNestedPair (HV.pure 10)
      reads :: (Base repr) => repr [H.Real]
      reads = cons 30 (cons 40 nil)
      betas :: (Base repr) => repr [H.Real]
      betas = cons 7 (cons 9 nil)
      result :: Sample IO (Repeat Eleven H.Real)
      result = laserAssigns base shortrange reads betas
  print (unSample result)
        
