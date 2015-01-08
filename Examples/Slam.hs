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
          
type GPS = H.Real
type ZRad = H.Real -- The observed radial distance to a beacon
type Angle = H.Real -- Radians
type Vel = H.Real    
type DelTime = H.Real
type DimL = H.Real
type DimH = H.Real
type DimA = H.Real
type DimB = H.Real

-- simulate :: (Mochastic repr) => Simulator repr
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
    -- let_' (map (\r -> atan r - calc_phi)  -- removed a "+ pi/2" term
    --            ((/) A.<$> lat_ds A.<*> lon_ds)) $ \calc_zbetas ->

    -- let_' (map (\l -> normal (fromProb l) cBeacon) calc_zrads) $ \noisy_zrads ->

    -- let_' (map (\l -> normal (fromProb l) cBeacon) calc_zints) $ \noisy_zints ->

    -- let_' (map (\l -> normal l cBeacon) calc_zbetas) $ \noisy_zbetas ->

    -- perturbReads (\l -> normal (fromProb l) cBeacon) calc_zrads `bind` \noisy_zrads ->
    -- perturbReads (\l -> normal (fromProb l) cBeacon) calc_zints `bind` \noisy_zints ->
    -- perturbReads (\l -> normal l cBeacon) calc_zbetas `bind` \noisy_zbetas ->

    -- fromNestedPair noisy_zrads $ \zrad_reprs ->
    -- fromNestedPair noisy_zbetas $ \zbeta_reprs ->

    -- perturbReads (\(b,a) -> if (withinLaser a 50) then dirac 5 else normal 40 1)
    --              (HV.fromList $ replicate shortrange (False,6::Double))
    --              `bind` \take11 ->

    -- (extractMeasure $
    --  laserAssigns (normal muZRads sigmaZRads) zrad_reprs noisy_zbetas)
    -- `bind` \laser_zrads ->

    extractMeasure (HV.pure (normal muZRads sigmaZRads)) `bind` \zrad_measures ->
    -- fromNestedPair zrad_measures $ \base_zrads ->
    -- let_' (toNestedPair (laserAssigns base_zrads zrad_reprs zbeta_reprs)) $
    --       \laser_zrads -> 

    -- perturbReads (const $ normal 40 1) (HV.pure ()) `bind` \rpad ->
    perturbReads (const $ normal 400 1) (HV.pure ()) `bind` \ipad ->

    dirac $ pair (pair zrad_measures ipad)
                 (pair noisy_phi (pair noisy_lon noisy_lat))

testLaser :: IO ()
testLaser = do
  let base :: (Base repr) => Repeat Eleven (repr H.Real)
      base =  HV.pure 10 -- HV.fromList $ replicate shortrange (10::Double)
      reads :: (Base repr) => [repr H.Real]
      reads = [30,40]
      betas :: (Base repr) => [repr H.Real]
      betas = [7,9]
      result :: Repeat Eleven (Sample IO H.Real)
      result = laserAssigns base reads betas

      sim :: Sample IO (Measure (Repeat Eleven H.Real))
      sim = extractMeasure (HV.pure (normal 0 1)) `bind` \bs ->
            fromNestedPair bs $ \base_reprs ->
            -- dirac $ toNestedPair base_reprs
                
            perturbReads (\r -> normal r 2) (HV.fromList [30,40]) `bind` \rs ->
            fromNestedPair rs $ \read_reprs ->

            dirac $ toNestedPair ((+) <$> base_reprs <*> read_reprs)

            -- fromNestedPair rs $ \reads_reprs ->
                
            -- perturbReads (\r -> normal r 1) (HV.fromList [7,9]) `bind` \as ->
            -- fromNestedPair as $ \betas_reprs ->
                
            -- dirac $ toNestedPair (laserAssigns base_reprs reads_reprs betas_reprs)
  print (unSample $ toNestedPair result)

withinLaser n b = and_ [ lessOrEq (convert (n-0.5)) tb2
                       , less tb2 (convert (n+0.5)) ]           
    where lessOrEq a b = or_ [less a b, equal a b]
          tb2 = tan (b/2)
          toRadian d = d*pi/180
          convert = tan . toRadian . ((/) 4)

laserAssigns base reads betas =
    let combined = zip reads betas
        addBeacon (r,b) (m,i) = if_ (withinLaser (fromIntegral $ i-180) b) r m
        build pd (r,b) = map (addBeacon (r,b)) (zip pd [1::Int,2..])
    in fromList $ F.foldl' build (toList base) combined

-- testAssigns base reads betas =
--     let combined = zip reads betas
--         addBeacon (r,b) i m = if b > (fromIntegral (2*i))
--                               then r else m
--         build pd (r,b) = S.mapWithIndex (addBeacon (r,b)) pd
--     in fromSeq $ F.foldl' build (toSeq base) combined

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

pR fn ls = let ls' = map fn ls
           in CM.sequence ls'

perturbReads fn ls = let ls' = fn <$> ls
                     in extractMeasure ls'

extractMeasure ls' = let mls' = cont . bind <$> ls'
                         seq' = HV.sequence mls'
                         rseq = runCont seq'
                     in rseq (dirac . toNestedPair)

-- | Extending Vector so that we can convert to and from Sequences
-- class (Vector a as) => FromToSeq a as where
--     toSeq :: (a, as) -> S.Seq a
--     fromSeq :: S.Seq a -> (a, as)

-- instance FromToSeq a () where
--     toSeq (a, ())  = S.singleton a
--     fromSeq aseq   = let (a S.:< _) = S.viewl aseq
--                      in (a, ())

-- instance (FromToSeq a as) => FromToSeq a (a, as) where
--     toSeq (a, as)  = a S.<| (toSeq as)
--     fromSeq aseq   = let (a S.:< as) = S.viewl aseq
--                      in (a, fromSeq as)

shortrange :: Int
shortrange = 11

type Len = D Eleven

                 -- ^ (rads, intensities)
type StateHk = ( (Repeat Len H.Real, Repeat Len H.Real)
               , (Angle, (GPS, GPS)) )

type StateHs = ( (Repeat Len Double, Repeat Len Double)
               , (Double, (Double, Double)) )

type TestState n = Repeat n H.Real                              

type HsInputs n = Repeat n Double -> Repeat n Double -- ^ beacon lons, beacon lats
                -> Double -> Double -> Double -- ^ vehLon, vehLat, phi
                -> Double -> Double -> Double -- ^ vel, alpha, __timestamp__
                -> IO ()

data Params = PM { vlon :: Double
                 , vlat :: Double
                 , phi :: Double
                 , vel :: Double
                 , alpha :: Double
                 , tm :: Double }

type StepHk n = DimL -> DimH -> DimA -> DimB
              -> Repeat n GPS -> Repeat n GPS
              -> GPS -> GPS -> Angle
              -> Vel -> Angle -> DelTime
              -> Measure StateHk
                        
type Simulator repr = repr DimL -> repr DimH -> repr DimA -> repr DimB
                    -> [repr GPS] -> [repr GPS]
                    -> repr GPS -> repr GPS -> repr Angle
                    -> repr Vel -> repr Angle -> repr DelTime
                    -> repr (Measure StateHk)

type Generator = V.Vector Sensor -> Int
               -> V.Vector Control -> Int
               -> Particle
               -> Params
               -> IO ()
                  
type Particle = Sample' IO ( GPS -> GPS -> Angle
                             -> Vel -> Angle -> DelTime
                             -> Measure StateHk )

type Rand = MWC.Gen (PrimState IO)
    
gen :: PathType -> Rand -> Generator
gen pt g sensors si controls ci particle
    (PM old_vlon old_vlat old_phi old_ve old_alpha tprev)
    = do
  unless (si >= V.length sensors) $ do
  return ()
  let (Sensor tcurr snum) = sensors V.! si
  s <- fmap (\(Just (s,1)) -> s) $
       particle old_vlon old_vlat old_phi old_ve old_alpha (tcurr-tprev) 1 g
  let (cblons, cblats) = fst s
      (cphi, (cvlon,cvlat)) = snd s
      newprms = case snum of
                  1 -> do putStrLn "writing to simulated_slam_out_path"
                          plotPoint pt cvlon cvlat
                          return (ci, old_ve, old_alpha)
                  2 -> do when (ci >= V.length controls) $
                               error "input_control has fewer data than\
                                     \it should according to input_sensor"
                          let (Control _ nv nalph) = controls V.! ci
                          return (ci+1, nv, nalph)
                  3 -> do putStrLn "writing to simulated_input_laser"
                          return (ci, old_ve, old_alpha)
                  _ -> error "Invalid sensor ID (must be 1, 2 or 3)"
  newprms >>= \(nci,nve,nal) -> gen pt g sensors (si+1) controls nci particle
                                    (PM cvlon cvlat cphi nve nal tcurr)
                             
-- generate :: PathType -> IO ()
-- generate pt = do
--   g <- MWC.createSystemRandom
--   (Init l h a b phi ilt iln) <- initialVals pt
--   controls <- controlData pt
--   sensors <- sensorData pt
--   let lamExp1 :: (Mochastic repr, Lambda repr) => repr (StepHk One)
--       lamExp1 = lamExp ()
--       lamExp () = lam $ \dl -> lam $ \dh -> lam $ \da -> lam $ \db -> 
--                lam $ \bx -> lam $ \by ->
--                lam $ \old_lon -> lam $ \old_lat -> lam $ \old_phi ->
--                lam $ \old_ve -> lam $ \old_alpha -> lam $ \delT ->
--                fromNestedPair bx $ \blons ->
--                fromNestedPair by $ \blats ->
--                simulate dl dh da db blons blats
--                          old_lon old_lat old_phi
--                          old_ve old_alpha delT
--       particle1 :: Particle
--       particle1 = (unSample lamExp1) l h a b (1,()) (2,())
--       lamExp2 :: (Mochastic repr, Lambda repr) => repr (StepHk Two)
--       lamExp2 = lamExp ()
--   gen pt g sensors 0 controls 0 particle1 (PM iln ilt phi 0 0 0)

plotPoint :: PathType -> Double -> Double -> IO ()
plotPoint pt lon lat = do
  dExist <- doesDirectoryExist (outputDir pt)
  unless dExist $ createDirectory (outputDir pt)
  let fp = outputDir pt ++ pt ++ "_path.txt"
  appendFile fp $ show lon ++ "," ++ show lat ++ "\n"

-- pt :: PathType
-- pt = "4_circle"

main :: IO ()
main = usageExit -- do
  -- args <- getArgs
  -- case args of
  --   [] -> usageExit
  --   [ty] -> if not (elem ty ptypes)
  --           then usageExit
  --           else generate ty

ptypes :: [String]
ptypes = ["1_straight","2_bend","3_curvy","4_circle","5_eight","6_loop","7_random"]
    
usageExit :: IO ()
usageExit = do
  pname <- getProgName
  putStrLn (usage pname) >> exitSuccess
      where usage pname = "Usage : " ++ pname ++ " path_type\n"
                          ++ "path_type must be one of: \n"
                          ++ show ptypes
                             
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

-- | Unsure what environment to use; using unit env for now
-- evolve :: Mochastic repr => Beacons Disintegrate
--        -> Disintegrate GPS -> Disintegrate GPS -> Disintegrate Angle 
--        -> Disintegrate Vel -> Disintegrate Angle -> Disintegrate DelTime
--        -> [ repr (Angle,ZRad) -> repr (Measure (Angle,(GPS,GPS))) ]
-- evolve bxy old_lon old_lat old_phi old_ve old_alpha delT =
--     [ d unit
--       | d <- runDisintegrate $ \u ->
--              ununit u $
--              simulate_old bxy old_lon old_lat old_phi old_ve old_alpha delT ]    


-- tb = let p = S.fromList [1,1,1,1,1,1,1]
--          a = S.fromList [7,8]
--          i = S.fromList [4,6]
--      in builder a i p

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
                      
type PathType = String
    
automobileData :: FilePath
automobileData = "./data/automobile/"

-- | Implicit that PathType = FilePath = String
inputDir :: PathType -> FilePath
inputDir pathtype = automobileData ++ pathtype ++ "/input/"

outputDir :: PathType -> FilePath
outputDir pathtype = automobileData ++ pathtype ++ "/output/"

noFileBye :: FilePath -> IO ()
noFileBye fp = putStrLn ("Could not find " ++ fp) >> exitFailure

initialVals :: PathType -> IO Initial
initialVals ptype = do
  let input = inputDir ptype ++ "input_properties.csv"
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

range :: Int
range = 361

instance FromRecord Laser where
    parseRecord v
        | V.length v == 1 + 2*range
            = L A.<$> v .! 0
              A.<*> parseRecord (V.slice 1 range v)
              A.<*> parseRecord (V.slice (range+1) range v)
        | otherwise = fail "wrong number of fields in input_laser"

laserReadings :: PathType -> IO (V.Vector Laser)
laserReadings ptype = do
  let input = inputDir ptype ++ "input_laser.csv"
  doesFileExist input >>= flip unless (noFileBye input)
  fmap V.fromList $ decodeFileStream input                        

data Sensor = Sensor {sensetime :: Double, sensorID :: Int} deriving (Show)

instance FromRecord Sensor where
    parseRecord v
        | V.length v == 2 = Sensor A.<$> v .! 0 A.<*> v .! 1
        | otherwise = fail "wrong number of fields in input_sensor"

sensorData :: PathType -> IO (V.Vector Sensor)
sensorData ptype = do
  let input = inputDir ptype ++ "input_sensor.csv"
  doesFileExist input >>= flip unless (noFileBye input)
  fmap V.fromList $ decodeFileStream input

isMovement :: Int -> Bool
isMovement = (==) 2

data Control = Control { contime :: Double
                       , velocity :: Double
                       , steering :: Double } deriving (Show)

instance FromRecord Control where
    parseRecord v
        | V.length v == 3 = Control A.<$> v .! 0 A.<*> v .! 1 A.<*> v .! 2
        | otherwise = fail "wrong number of fields in input_control"

controlData :: PathType -> IO (V.Vector Control)
controlData ptype = do
  let input = inputDir ptype ++ "input_control.csv"
  doesFileExist input >>= flip unless (noFileBye input)
  fmap V.fromList $ decodeFileStream input
             
testIO :: PathType -> IO ()
testIO pt = do
  -- initialVals "test" >>= print
  laserReads <- laserReadings pt
  print . (V.slice 330 31) . zrads $ laserReads V.! 50
  V.mapM_ ((printf "%.6f\n") . timestamp) $ V.take 10 laserReads
  sensors <- sensorData pt 
  putStrLn "-------- Here are some sensors -----------"
  print $ V.slice 0 20 sensors
  controls <- controlData pt 
  putStrLn "-------- Here are some controls -----------"
  print $ V.slice 0 20 controls

