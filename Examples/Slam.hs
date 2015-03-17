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
           
type Steering = (Vel, Angle) -- ^ vel, alpha

vel :: (Base repr) => repr Steering -> repr Vel
vel steer = unpair steer $ \v _ -> v

alpha :: (Base repr) => repr Steering -> repr Angle
alpha steer = unpair steer $ \_ a -> a
    
type State = (LaserReads, Coords)

type Simulator repr = repr Dims
                    -> repr (Vector GPS) -- ^ beacon lons
                    -> repr (Vector GPS) -- ^ beacon lats
                    -> repr Coords -> repr Steering
                    -> repr DelTime      -- ^ timestamp
                    -> repr (Measure State)

--------------------------------------------------------------------------------
--                                MODEL                                       --
--------------------------------------------------------------------------------
                       
simulate :: (Mochastic repr) => Simulator repr
simulate ds blons blats cds steerE delT =

    let_' (wheelToAxle steerE ds) $ \vc ->
    let_' (pair vc (alpha steerE)) $ \steerC ->
        
    unpair (newPos ds cds steerC delT) $ \calc_lon calc_lat ->
    let_' (newPhi ds cds steerC delT) $ \calc_phi ->
    
    let_' (mapV ((-) calc_lon) blons) $ \lon_ds ->
    let_' (mapV ((-) calc_lat) blats) $ \lat_ds ->

    -- Equation 10 from [1]
    let_' (mapV sqrt_ (zipWithV (+) (mapV sqr lon_ds)
                                    (mapV sqr lat_ds))) $ \calc_zrads ->
    -- inverse-square for intensities 
    let_' (mapV (\r -> cIntensity / (pow_ r 2)) calc_zrads) $ \calc_zints ->

    -- Equation 10 from [1]    
    -- Note: removed a "+ pi/2" term: it is present as (i - 180) in laserAssigns
    let_' (mapV (\r -> atan r - calc_phi)
                (zipWithV (/) lat_ds lon_ds)) $ \calc_zbetas ->

    -- | Add some noise
    normal calc_lon ((*) cVehicle . sqrt_ . unsafeProb $ delT) `bind` \lon ->
    normal calc_lat ((*) cVehicle . sqrt_ . unsafeProb $ delT) `bind` \lat ->
    normal calc_phi ((*) cVehicle . sqrt_ . unsafeProb $ delT) `bind` \phi ->
        
    normalNoise cBeacon calc_zbetas `bind` \zbetas ->

    makeLasers (mapV fromProb calc_zrads) zbetas muZRads cBeacon `bind` \lasersR ->
    makeLasers (mapV fromProb calc_zints) zbetas muZInts cBeacon `bind` \lasersI ->
    
    dirac $ pair (pair lasersR lasersI) (pair phi (pair lon lat))

-- | Translate velocity from back left wheel (where the velocity
-- encoder is present) to the center of the rear axle
-- Equation 6 from [1]
wheelToAxle :: (Base repr) => repr Steering -> repr Dims -> repr Vel
wheelToAxle s ds = (vel s) / (1 - (tan (alpha s))*(dimH ds)/(dimL ds))

-- | Equation 7 (corrected) from [1]
newPos :: (Base repr) => repr Dims -> repr Coords
       -> repr Steering -> repr DelTime 
       -> repr (GPS,GPS)
newPos ds cds s delT = pair lonPos latPos
    where lonPos = (vLon cds) + delT*lonVel
          latPos = (vLat cds) + delT*latVel
                   
          lonVel = (vel s)*(cos phi) - axleToLaser lonMag
          latVel = (vel s)*(sin phi) + axleToLaser latMag

          phi = vPhi cds
          axleToLaser mag = (vel s) * mag * (tan (alpha s)) / (dimL ds)
          lonMag = (dimA ds)*(sin phi) + (dimB ds)*(cos phi)
          latMag = (dimA ds)*(cos phi) - (dimB ds)*(sin phi)

-- | Equation 7 (corrected) from [1]                   
newPhi :: (Base repr) => repr Dims -> repr Coords
       -> repr Steering -> repr DelTime -> repr Angle
newPhi ds cds s delT = (vPhi cds) + delT*(vel s)*(tan (alpha s)) / (dimL ds)
    
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

normalNoise :: (Mochastic repr) => repr Prob -> repr (Vector H.Real)
            -> repr (Measure (Vector H.Real))
normalNoise sd v = plate (mapV (`normal` sd) v)        
                           
-- | Make a vector of laser readings (length 361)
-- The vector contains values from "reads" at positions from "betas"
-- Normal noise is then added to the vector
makeLasers :: (Mochastic repr) => repr (Vector H.Real) 
             -> repr (Vector H.Real)
             -> repr H.Real -> repr Prob
             -> repr (Measure (Vector H.Real))
makeLasers reads betas mu sd =
    let base = vector 361 (const mu)
        combine r b = vector 361 (\i -> if_ (withinLaser (i-180) b) (r-mu) 0)
        combined = zipWithV combine reads betas
    in normalNoise sd (reduce (zipWithV (+)) base combined)

withinLaser :: (Base repr) => repr Int -> repr H.Real -> repr Bool
withinLaser n b = and_ [ lessOrEq (convert (fromInt n - 0.5)) tb2
                       , less tb2 (convert (fromInt n + 0.5)) ]
    where lessOrEq a b = or_ [less a b, equal a b]
          tb2 = tan (b/2)
          toRadian d = d*pi/180
          convert = tan . toRadian . ((/) 4)                           

--------------------------------------------------------------------------------
--                               SIMULATIONS                                  --
--------------------------------------------------------------------------------

type Rand = MWC.Gen (PrimState IO)

data Particle = PL { dims :: V.Vector Double  -- ^ l,h,a,b
                   , bLats :: V.Vector Double
                   , bLons :: V.Vector Double }

data Params = PM { sensors :: [Sensor]
                 , controls :: [Control]
                 , lasers :: [Laser]
                 , coords :: (Double,(Double,Double)) -- ^ phi, lon, lat
                 , steer :: (Double,Double)           -- ^ vel, alpha
                 , tm :: Double }    
    
type Generator = Particle -> Params -> IO ()

data Gen = Conditioned | Unconditioned deriving Eq

-- | Returns the pair (longitudes, latitudes)
genBeacons :: Rand -> Maybe FilePath -> IO (V.Vector Double, V.Vector Double)
genBeacons _ Nothing         = return ( V.fromList [1,3]
                                      , V.fromList [2,4] )
genBeacons g (Just evalPath) = do
  trueBeacons <- obstacles evalPath
  return ( V.map lon trueBeacons
         , V.map lat trueBeacons )

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

generate :: Gen -> FilePath -> FilePath -> Maybe FilePath -> IO ()
generate c input output eval = do
  g <- MWC.createSystemRandom
  Init ds phi ilt iln <- initialVals input
  controls <- controlData input
  sensors <- sensorData input
  lasers <- if c==Unconditioned then return [] else laserReadings input
  (lons, lats) <- genBeacons g eval
                  
  gen c output g (PL ds lons lats)
                 (PM sensors controls lasers (iln,(ilt,phi)) (0,0) 0)

gen :: Gen -> FilePath -> Rand -> Generator
gen c out g prtcl params = go params
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
                                 , steer = (nv, nalph) }
              3 -> case c of
                     Unconditioned -> 
                         do ((zr,zi), coords) <- sampleState prtcl prms tcurr g
                            putStrLn "writing to simulated_input_laser"
                            plotReads out zr zi
                            go $ updateParams prms coords tcurr
                     Conditioned ->
                         do when (null $ lasers prms) $
                                 error "input_laser has fewer data than\
                                       \it should according to input_sensor"
                            let L _ zr zi = head (lasers prms)
                                lreads = (V.fromList zr, V.fromList zi)
                            coords <- sampleCoords prtcl prms lreads tcurr g
                            let prms' = updateParams prms coords tcurr
                            go $ prms' { lasers = tail (lasers prms) }
              _ -> error "Invalid sensor ID (must be 1, 2 or 3)"

------------------
--  UNCONDITIONED
------------------                   

type SimLaser = Dims -> Vector GPS -> Vector GPS
              -> Coords -> Steering -> DelTime
              -> Measure State

simLasers :: (Mochastic repr, Lambda repr) => repr SimLaser
simLasers = lam $ \ds -> lam $ \blons -> lam $ \blats ->
            lam $ \cds -> lam $ \s -> lam $ \delT ->
            simulate ds blons blats cds s delT
                              
sampleState :: Particle -> Params -> Double -> Rand
            -> IO ( (V.Vector Double, V.Vector Double)
                  , (Double, (Double, Double)) )
sampleState prtcl prms tcurr g =
    fmap (\(Just (s,1)) -> s) $
         (unSample $ simLasers) ds blons blats cds s (tcurr-tprev) 1 g
    where (PL ds blons blats) = prtcl
          (PM _ _ _ cds s tprev) = prms

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

type Env = (Dims, (Vector GPS, (Vector GPS, (Coords, (Steering, DelTime)))))

evolve :: (Mochastic repr) => repr Env
       -> [ repr LaserReads -> repr (Measure Coords) ]
evolve env =
    [ d env
      | d <- runDisintegrate $ \ e0  ->
             unpair e0  $ \ds    e1  ->
             unpair e1  $ \blons e2  ->
             unpair e2  $ \blats e3  ->
             unpair e3  $ \cds   e4  ->
             unpair e4  $ \s   delT  ->
             simulate ds blons blats cds s delT ]

readLasers :: (Mochastic repr, Lambda repr) =>
              repr (Env -> LaserReads -> Measure Coords)
readLasers = lam $ \env -> lam $ \lrs -> head (evolve env) lrs

sampleCoords prtcl prms lreads tcurr g =
    fmap (\(Just (s,1)) -> s) $
         (unSample $ readLasers)
         (ds,(blons,(blats,(cds,(s,tcurr-tprev)))))
         lreads 1 g
    where (PL ds blons blats) = prtcl
          (PM _ _ _ cds s tprev) = prms

--------------------------------------------------------------------------------
--                                MAIN                                        --
--------------------------------------------------------------------------------

main :: IO ()
main = do
  args <- getArgs
  case args of
    [input, output]       -> generate Unconditioned input output Nothing
    [input, output, eval] -> generate Unconditioned input output (Just eval)
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
hakvec = plate $ vector 11 (const (normal 0 1))
