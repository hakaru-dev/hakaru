{-# LANGUAGE DataKinds, GADTs, MultiParamTypeClasses,
             FlexibleInstances, StandaloneDeriving, 
             GeneralizedNewtypeDeriving, FlexibleContexts #-}

-- {-# OPTIONS_GHC -ftype-function-depth=400 #-}
-- {-# OPTIONS_GHC -fcontext-stack=400 #-}

-- | References:
--
-- [1] Jose Guivant, Eduardo Nebot, and Stephan Baiker. Autonomous navigation and map 
--     building using laser range sensors in outdoor applications. 
--     Journal of Robotic Systems, 17(10):565–583, Oct. 2000.

module Slam where

import Prelude as P
import Control.Monad as CM
import Language.Hakaru.Syntax as H
import Language.Hakaru.Disintegrate
import qualified System.Random.MWC as MWC
import Language.Hakaru.Sample
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

range :: Int
range = 361

type ZRad = H.Real  -- ^ Observed radial distance to a beacon
type ZInt = H.Real  -- ^ Observed light intensity (reflected) from a beacon
type GPS = H.Real
type Angle = H.Real -- ^ In radians
type Vel = H.Real    
type DelTime = H.Real

-- | Dimensions of the vehicle
-- L = distance between front and rear axles
-- H = distance between center of back left wheel and center of rear axle
-- a = distance between rear axle and front-based laser
-- b = width offset of the front-based laser
type Dims = Vector H.Real -- ^ <L,H,a,b>

dimL, dimH, dimA, dimB :: (Base repr) => repr Dims -> repr H.Real
dimL v = H.index v 0
dimH v = H.index v 1
dimA v = H.index v 2
dimB v = H.index v 3

type LaserReads = (Vector ZRad, Vector ZInt)

type Coords = (Angle, (GPS, GPS)) -- ^ phi (world angle), vehLon, vehLat

vPhi :: (Base repr) => repr Coords -> repr Angle
vPhi cds = unpair cds $ \p _ -> p

vLon, vLat :: (Base repr) => repr Coords -> repr GPS
vLon cds = unpair cds $ \_ ll -> unpair ll $ \lon _ -> lon
vLat cds = unpair cds $ \_ ll -> unpair ll $ \_ lat -> lat

type State = (LaserReads, Coords)

type Simulator repr = repr Dims
                    -> repr (Vector GPS) -- ^ beacon lons
                    -> repr (Vector GPS) -- ^ beacon lats
                    -> repr Coords
                    -> repr Vel -> repr Angle -- ^ vel, alpha
                    -> repr DelTime           -- ^ timestamp
                    -> repr (Measure State)

--------------------------------------------------------------------------------
--                                MODEL                                       --
--------------------------------------------------------------------------------
                       
simulate :: (Mochastic repr) => Simulator repr
simulate ds blons blats cds
         old_ve old_alpha delT =

    let_' (wheelToAxle old_ve old_alpha ds) $ \old_vc ->
    let_' (newPos true ds cds delT old_vc old_alpha) $ \calc_lon ->
    let_' (newPos false ds cds delT old_vc old_alpha) $ \calc_lat ->
    let_' (newPhi cds delT old_vc old_alpha ds) $ \calc_phi ->
    
    normal calc_lon ((*) cVehicle . sqrt_ . unsafeProb $ delT) `bind` \lon ->
    normal calc_lat ((*) cVehicle . sqrt_ . unsafeProb $ delT) `bind` \lat ->
    normal calc_phi ((*) cVehicle . sqrt_ . unsafeProb $ delT) `bind` \phi ->

    let_' (vmap ((-) lon) blons) $ \lon_ds ->
    let_' (vmap ((-) lat) blats) $ \lat_ds ->
        
    let_' (vmap sqrt_ (vZipWith (+) (vmap sqr lon_ds)
                                    (vmap sqr lat_ds))) $ \calc_zrads ->
    -- inverse-square for intensities 
    let_' (vmap (\r -> cIntensity / (pow_ r 2)) calc_zrads) $ \calc_zints ->
    -- removed a "+ pi/2" term: it is present as (i - (n-1)/2) in laserAssigns
    let_' (vmap (\r -> atan r - calc_phi)
                (vZipWith (/) lat_ds lon_ds)) $ \calc_zbetas ->

    normalNoise cBeacon (vmap fromProb calc_zrads) `bind` \zrads ->
    normalNoise cBeacon (vmap fromProb calc_zints) `bind` \zints ->        
    normalNoise cBeacon calc_zbetas `bind` \zbetas ->

    plate (vector 0 360 (const (normal muZRads sigmaZRads))) `bind` \baseR ->
    let_' (laserAssigns zrads zbetas baseR) $ \lasersR ->
        
    plate (vector 0 360 (const (normal muZInts sigmaZInts))) `bind` \baseI ->
    let_' (laserAssigns zints zbetas baseI) $ \lasersI ->
    
    dirac $ pair (pair lasersR lasersI) (pair phi (pair lon lat))

-- | Translate velocity
-- from back left wheel (where the vel encoder is present)
-- to the center of the rear axle
wheelToAxle :: (Base repr) => repr Vel -> repr Angle -> repr Dims -> repr Vel
wheelToAxle ve alpha ds = ve / (1 - (tan alpha)*(dimH ds)/(dimL ds))

-- | "True" means longitude, "False" means latitude
newPos :: (Base repr) => repr Bool
       -> repr Dims -> repr Coords
       -> repr DelTime -> repr Vel -- ^ delT, old_vc
       -> repr Angle -- ^ old_alpha
       -> repr GPS
newPos lb ds cds delT old_vc old_alpha =
    oldPos + delT * (old_vc*(fb oldPhi)
                     - (old_vc * mag * (tan old_alpha) / (dimL ds)))
    where oldPos = if_ lb (vLon cds) (vLat cds)
          oldPhi = vPhi cds
          fa p = if_ lb (sin p) (cos p)
          fb p = if_ lb (cos p) (sin p)
          mag = (dimA ds)*(fa oldPhi) + (dimB ds)*(fb oldPhi)

newPhi :: (Base repr) => repr Coords -> repr DelTime
       -> repr Vel -> repr Angle -> repr Angle -> repr Dims
newPhi cds delT vc alpha ds = (vPhi cds) + delT*vc*(tan alpha) / (dimL ds)
    
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
                           
withinLaser :: (Base repr) => repr Int -> repr H.Real -> repr Bool
withinLaser n b = and_ [ lessOrEq (convert (fromInt n - 0.5)) tb2
                       , less tb2 (convert (fromInt n + 0.5)) ]
    where lessOrEq a b = or_ [less a b, equal a b]
          tb2 = tan (b/2)
          toRadian d = d*pi/180
          convert = tan . toRadian . ((/) 4)

laserAssigns :: (Base repr) => repr (Vector H.Real) -> repr (Vector H.Real)
             -> repr (Vector H.Real) -- ^ length = range
             -> repr (Vector H.Real)
laserAssigns reads betas base =
    let combine r b = vector 0 1 (\i -> if_ (equal_ i 0) r b)
        combined = vZipWith combine reads betas
        addBeacon rb i m = if_ (withinLaser (i-180) (H.index rb 1))
                           (H.index rb 0) m
        build pd rb = mapWithIndex (addBeacon rb) pd
    in reduce build base combined

normalNoise :: (Mochastic repr) => repr Prob -> repr (Vector H.Real)
            -> repr (Measure (Vector H.Real))
normalNoise sd v = plate (vmap (`normal` sd) v)

--------------------------------------------------------------------------------
--                               SIMULATIONS                                  --
--------------------------------------------------------------------------------

type Rand = MWC.Gen (PrimState IO)

data Particle = PL { dims :: Vec Double  -- ^ l,h,a,b
                   , bLats :: Vec Double
                   , bLons :: Vec Double }

data Params = PM { sensors :: [Sensor]
                 , controls :: [Control]
                 , lasers :: [Laser]
                 , coords :: (Double,(Double,Double)) -- ^ phi, lon, lat
                 , vel :: Double
                 , alpha :: Double
                 , tm :: Double }    
    
type Generator = Particle -> Params -> IO ()

-- | Returns the pair (longitudes, latitudes)
genBeacons :: Rand -> Maybe FilePath -> IO (Vec Double, Vec Double)
genBeacons _ Nothing         = return ( Vec 0 1 (V.fromList [1,3])
                                      , Vec 0 1 (V.fromList [2,4]) )
genBeacons g (Just evalPath) = do
  trueBeacons <- obstacles evalPath
  let len = V.length trueBeacons
  return ( Vec 0 (len-1) (V.map lon trueBeacons)
         , Vec 0 (len-1) (V.map lat trueBeacons) )

updateParams :: Params -> (Double,(Double,Double)) -> Double -> Params
updateParams prms cds tcurr =
    prms { sensors = tail (sensors prms)
         , coords = cds
         , tm = tcurr }
                                
plotPoint :: FilePath -> (Double,(Double,Double)) -> IO ()
plotPoint out (_,(lon,lat)) = do
  dExist <- doesDirectoryExist out
  unless dExist $ createDirectory out
  let fp = out </> "slam_out_path.txt"
  appendFile fp $ show lon ++ "," ++ show lat ++ "\n"

makeDims :: V.Vector Double -> Vec Double
makeDims = Vec 0 3

------------------
--  UNCONDITIONED
------------------

generate :: FilePath -> FilePath -> Maybe FilePath -> IO ()
generate input output eval = do
  g <- MWC.createSystemRandom
  (Init ds phi ilt iln) <- initialVals input
  controls <- controlData input
  sensors <- sensorData input
  (lons, lats) <- genBeacons g eval
                  
  gen output g (PL (makeDims ds) lons lats)
               (PM sensors controls [] (iln,(ilt,phi)) 0 0 0)

gen :: FilePath -> Rand -> Generator
gen out g prtcl params = go params
    where go prms | null $ sensors prms = putStrLn "Finished reading input_sensor"
                  | otherwise = do
            let (Sensor tcurr snum) = head $ sensors prms
            case snum of
              1 -> do (_,coords) <- sampleState prtcl prms tcurr g
                      putStrLn "writing to simulated_slam_out_path"
                      plotPoint out coords
                      go $ updateParams prms coords tcurr
              2 -> do when (null $ controls prms) $
                           error "input_control has fewer data than\
                                 \it should according to input_sensor"
                      (_,coords) <- sampleState prtcl prms tcurr g
                      let prms' = updateParams prms coords tcurr
                          (Control _ nv nalph) = head $ controls prms
                      go $ prms' { controls = tail (controls prms)
                                 , vel = nv
                                 , alpha = nalph }
              3 -> do ((zr,zi), coords) <- sampleState prtcl prms tcurr g
                      putStrLn "writing to simulated_input_laser"
                      plotReads out (vec zr) (vec zi)
                      go $ updateParams prms coords tcurr
              _ -> error "Invalid sensor ID (must be 1, 2 or 3)"

type SimLaser = Dims -> Vector GPS -> Vector GPS
              -> Coords
              -> Vel -> Angle
              -> DelTime
              -> Measure State

simLasers :: (Mochastic repr, Lambda repr) => repr SimLaser
simLasers = lam $ \ds -> lam $ \blons -> lam $ \blats ->
            lam $ \cds -> lam $ \old_ve -> lam $ \old_alpha ->
            lam $ \delT -> simulate ds blons blats cds old_ve old_alpha delT
                              
sampleState :: Particle -> Params -> Double -> Rand
            -> IO ( (Vec Double, Vec Double)
                  , (Double, (Double, Double)) )
sampleState prtcl prms tcurr g =
    fmap (\(Just (s,1)) -> s) $
         (unSample $ simLasers) ds blons blats
         cds ve alpha (tcurr-tprev) 1 g
    where (PL ds blons blats) = prtcl
          (PM _ _ _ cds ve alpha tprev) = prms

plotReads :: FilePath -> V.Vector Double -> V.Vector Double -> IO ()
plotReads out rads ints = do
  dExist <- doesDirectoryExist out
  unless dExist $ createDirectory out
  let file = out </> "slam_simulated_laser.txt"
  go file (V.toList $ rads V.++ ints)
    where go fp []     = appendFile fp "\n"
          go fp [l]    = appendFile fp ((show l) ++ "\n")
          go fp (l:ls) = appendFile fp ((show l) ++ ",") >> go fp ls

----------------------------------
--  CONDITIONED ON LASER READINGS
----------------------------------

runner :: FilePath -> FilePath -> Maybe FilePath -> IO ()
runner input output eval = do
  g <- MWC.createSystemRandom
  (Init ds phi ilt iln) <- initialVals input
  controls <- controlData input
  sensors <- sensorData input
  lasers <- laserReadings input
  (lons, lats) <- genBeacons g eval

  runn output g (PL (makeDims ds) lons lats)
                (PM sensors controls lasers (iln,(ilt,phi)) 0 0 0)

runn :: FilePath -> Rand -> Generator
runn out g prtcl params = go params
    where go prms | null $ sensors prms = putStrLn "Finished reading input_sensor"
                  | otherwise = do
            let (Sensor tcurr snum) = head $ sensors prms
            case snum of
              1 -> do (_,coords) <- sampleState prtcl prms tcurr g
                      putStrLn "writing to slam_out_path"
                      plotPoint out coords
                      go $ updateParams prms coords tcurr
              2 -> do when (null $ controls prms) $
                           error "input_control has fewer data than\
                                 \it should according to input_sensor"
                      (_,coords) <- sampleState prtcl prms tcurr g
                      let prms' = updateParams prms coords tcurr
                          (Control _ nv nalph) = head $ controls prms
                      go $ prms' { controls = tail (controls prms)
                                 , vel = nv
                                 , alpha = nalph }
              3 -> do when (null $ lasers prms) $
                           error "input_laser has fewer data than\
                                 \it should according to input_sensor"
                      let (L _ zr zi) = head (lasers prms)
                          makeLasers l = Vec 0 360 (V.fromList l)
                          lreads = (makeLasers zr, makeLasers zi)
                      coords <- sampleCoords prtcl prms lreads tcurr g
                      let prms' = updateParams prms coords tcurr
                      go $ prms' { lasers = tail (lasers prms) }
              _ -> error "Invalid sensor ID (must be 1, 2 or 3)"

type Env = (Dims, (Vector GPS, (Vector GPS,
            (Coords, (Vel, (Angle, DelTime))))))

evolve :: (Mochastic repr) => repr Env
       -> [ repr LaserReads -> repr (Measure Coords) ]
evolve env =
    [ d env
      | d <- runDisintegrate $ \ e0  ->
             unpair e0  $ \ds    e1  ->
             unpair e1  $ \blons e2  ->
             unpair e2  $ \blats e3  ->
             unpair e3  $ \cds   e4  ->
             unpair e4  $ \vel   e5  ->
             unpair e5  $ \alpha del ->
             simulate ds blons blats
                      cds vel alpha del ]

readLasers :: (Mochastic repr, Lambda repr) =>
              repr (Env -> LaserReads -> Measure Coords)
readLasers = lam $ \env -> lam $ \lrs -> head (evolve env) lrs

sampleCoords prtcl prms lreads tcurr g =
    fmap (\(Just (s,1)) -> s) $
         (unSample $ readLasers)
         (ds,(blons,(blats,(cds,(ve,(alpha,tcurr-tprev))))))
         lreads 1 g
    where (PL ds blons blats) = prtcl
          (PM _ _ _ cds ve alpha tprev) = prms

--------------------------------------------------------------------------------
--                                MAIN                                        --
--------------------------------------------------------------------------------

main :: IO ()
main = do
  args <- getArgs
  case args of
    [input, output]       -> runner input output Nothing
    [input, output, eval] -> runner input output (Just eval)
    _ -> usageExit
    
usageExit :: IO ()
usageExit = do
  pname <- getProgName
  putStrLn (usage pname) >> exitSuccess
      where usage pname = "Usage: " ++ pname ++ " input_dir output_dir [eval_dir]\n"
                          
--------------------------------------------------------------------------------
--                                DATA IO                                     --
--------------------------------------------------------------------------------

data Initial = Init { dimensions :: V.Vector Double -- ^ l,h,a,b
                    , initPhi :: Double
                    , initLat :: Double
                    , initLon :: Double } deriving Show

instance FromRecord Initial where
    parseRecord v
        | V.length v == 7 = Init A.<$> parseRecord (V.slice 0 4 v)
                                 A.<*> v .! 4
                                 A.<*> v .! 5
                                 A.<*> v .! 6
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
               , zrads :: [Double]
               , intensities :: [Double] }

instance FromRecord Laser where
    parseRecord v
        | V.length v == 1 + 2*range
            = L A.<$> v .! 0
              A.<*> parseRecord (V.slice 1 range v)
              A.<*> parseRecord (V.slice (range+1) range v)
        | otherwise = fail "wrong number of fields in input_laser"

laserReadings :: FilePath -> IO [Laser]
laserReadings inpath = do
  let input = inpath </> "input_laser.csv"
  doesFileExist input >>= flip unless (noFileBye input)
  decodeFileStream input                        

data Sensor = Sensor {sensetime :: Double, sensorID :: Int} deriving (Show)

instance FromRecord Sensor where
    parseRecord v
        | V.length v == 2 = Sensor A.<$> v .! 0 A.<*> v .! 1
        | otherwise = fail "wrong number of fields in input_sensor"

sensorData :: FilePath -> IO [Sensor]
sensorData inpath = do
  let input = inpath </> "input_sensor.csv"
  doesFileExist input >>= flip unless (noFileBye input)
  decodeFileStream input

data Control = Control { contime :: Double
                       , velocity :: Double
                       , steering :: Double } deriving (Show)

instance FromRecord Control where
    parseRecord v
        | V.length v == 3 = Control A.<$> v .! 0 A.<*> v .! 1 A.<*> v .! 2
        | otherwise = fail "wrong number of fields in input_control"

controlData :: FilePath -> IO [Control]
controlData inpath = do
  let input = inpath </> "input_control.csv"
  doesFileExist input >>= flip unless (noFileBye input)
  decodeFileStream input       

-- | True beacon positions (from eval_data/eval_obstacles.csv for each path type)
-- This is for simulation purposes only!
-- Not to be used during inference
data Obstacle = Obstacle {lat :: Double, lon :: Double}

instance FromRecord Obstacle where
    parseRecord v
        | V.length v == 2 = Obstacle A.<$> v .! 0 A.<*> v .! 1
        | otherwise = fail "wrong number of fields in eval_obstacles"

obstacles :: FilePath -> IO (V.Vector Obstacle)
obstacles evalPath = do
  let evalObs = evalPath </> "eval_obstacles.csv"
  doesFileExist evalObs >>= flip unless (noFileBye evalObs)
  fmap V.fromList $ decodeFileStream evalObs
                   
--------------------------------------------------------------------------------
--                               MISC MINI-TESTS                              --
--------------------------------------------------------------------------------

testIO :: FilePath -> IO ()
testIO inpath = do
  -- initialVals "test" >>= print
  laserReads <- laserReadings inpath
  let laserVector = V.fromList laserReads
  print . (V.slice 330 31) . V.fromList . zrads $ laserVector V.! 50
  V.mapM_ ((printf "%.6f\n") . timestamp) $ V.take 10 laserVector
  sensors <- sensorData inpath
  putStrLn "-------- Here are some sensors -----------"
  print $ V.slice 0 20 (V.fromList sensors)
  controls <- controlData inpath
  putStrLn "-------- Here are some controls -----------"
  print $ V.slice 0 20 (V.fromList controls)
        
hakvec :: (Mochastic repr) => repr (Measure (Vector H.Real))
hakvec = plate $ vector 10 20 (const (normal 0 1))
