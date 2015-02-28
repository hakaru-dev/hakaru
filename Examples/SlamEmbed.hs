{-# LANGUAGE DataKinds, GADTs, MultiParamTypeClasses,
             FlexibleInstances, StandaloneDeriving, 
             GeneralizedNewtypeDeriving, FlexibleContexts, UndecidableInstances #-}

-- {-# OPTIONS_GHC -ftype-function-depth=400 #-}
-- {-# OPTIONS_GHC -fcontext-stack=400 #-}

{-# OPTIONS -ddump-splices -Wnot #-}

-- | References:
--
-- [1] Jose Guivant, Eduardo Nebot, and Stephan Baiker. Autonomous navigation and map 
--     building using laser range sensors in outdoor applications. 
--     Journal of Robotic Systems, 17(10):565-583, Oct. 2000.

module SlamEmbed where

import Prelude as P
import Control.Monad as CM
import Language.Hakaru.Syntax as H
import Language.Hakaru.Disintegrate hiding (Nil)
import Language.Hakaru.Embed 
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

embeddable [d| data LaserReads = LaserReads { lZRad :: Vector ZRad, lZInt :: Vector ZInt } |]

embeddable [d| data Coords = Coord { vPhi :: Angle, vehLon :: GPS, vehLat :: GPS } |] 
  -- ^ phi (world angle), vehLon, vehLat

embeddable [d| data Steering = Steering { vel :: Vel, alpha :: Angle } |]
  -- ^ vel, alpha

embeddable [d| data State = State { s_laserReads :: LaserReads, s_coords :: Coords } |] 

type Simulator repr = repr Dims
                    -> repr (Vector GPS) -- ^ beacon lons
                    -> repr (Vector GPS) -- ^ beacon lats
                    -> repr Coords -> repr Steering
                    -> repr DelTime      -- ^ timestamp
                    -> repr (Measure State)

--------------------------------------------------------------------------------
--                                MODEL                                       --
--------------------------------------------------------------------------------
                       
simulate :: (Embed repr, Mochastic repr) => Simulator repr
simulate ds blons blats cds steerE delT =

    let_' (wheelToAxle steerE ds) $ \vc ->
    let_' (steering vc (alpha steerE)) $ \steerC ->
        
    unpair (newPos ds cds steerC delT) $ \calc_lon calc_lat ->
    let_' (newPhi ds cds steerC delT) $ \calc_phi ->
    
    let_' (mapV ((-) calc_lon) blons) $ \lon_ds ->
    let_' (mapV ((-) calc_lat) blats) $ \lat_ds ->

    -- Equation 10 from [1]
    let_' (mapV sqrt_ (vZipWith (+) (mapV sqr lon_ds)
                                    (mapV sqr lat_ds))) $ \calc_zrads ->
    -- inverse-square for intensities 
    let_' (mapV (\r -> cIntensity / (pow_ r 2)) calc_zrads) $ \calc_zints ->

    -- Equation 10 from [1]    
    -- Note: removed a "+ pi/2" term: it is present as (i - 180) in laserAssigns
    let_' (mapV (\r -> atan r - calc_phi)
                (vZipWith (/) lat_ds lon_ds)) $ \calc_zbetas ->

    -- | Add some noise
    normal calc_lon ((*) cVehicle . sqrt_ . unsafeProb $ delT) `bind` \lon ->
    normal calc_lat ((*) cVehicle . sqrt_ . unsafeProb $ delT) `bind` \lat ->
    normal calc_phi ((*) cVehicle . sqrt_ . unsafeProb $ delT) `bind` \phi ->
        
    normalNoise cBeacon calc_zbetas `bind` \zbetas ->

    makeLasers (mapV fromProb calc_zrads) zbetas muZRads cBeacon `bind` \lasersR ->
    makeLasers (mapV fromProb calc_zints) zbetas muZInts cBeacon `bind` \lasersI ->
    
    -- dirac $ pair (pair lasersR lasersI) (pair phi (pair lon lat))
    dirac $ state (laserReads lasersR lasersI) (coord phi lon lat)

-- | Translate velocity from back left wheel (where the velocity
-- encoder is present) to the center of the rear axle
-- Equation 6 from [1]
wheelToAxle :: (Embed repr) => repr Steering -> repr Dims -> repr Vel
wheelToAxle s ds = (vel s) / (1 - (tan (alpha s))*(dimH ds)/(dimL ds))

-- | Equation 7 (corrected) from [1]
newPos :: (Embed repr) => repr Dims -> repr Coords
       -> repr Steering -> repr DelTime 
       -> repr (GPS,GPS)
newPos ds cds s delT = pair lonPos latPos

    where lonPos = (vehLon cds) + delT*lonVel
          latPos = (vehLat cds) + delT*latVel
                   
          lonVel = (vel s)*(cos phi) - axleToLaser lonMag
          latVel = (vel s)*(sin phi) + axleToLaser latMag

          phi = vPhi cds
          axleToLaser mag = (vel s) * mag * (tan (alpha s)) / (dimL ds)
          lonMag = (dimA ds)*(sin phi) + (dimB ds)*(cos phi)
          latMag = (dimA ds)*(cos phi) - (dimB ds)*(sin phi)

-- | Equation 7 (corrected) from [1]                   
newPhi :: (Embed repr) => repr Dims -> repr Coords
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
    let base = vector 0 360 (const mu)
        combine r b = vector 0 360 (\i -> if_ (withinLaser (i-180) b) (r-mu) 0)
        combined = zipWithV combine reads betas
    in normalNoise sd (reduce (zipWithV (+)) base combined)

withinLaser :: (Base repr) => repr Int -> repr H.Real -> repr Bool
withinLaser n b = and_ [ lessOrEq (convert (fromInt n - 0.5)) tb2
                       , less tb2 (convert (fromInt n + 0.5)) ]
    where lessOrEq a b = or_ [less a b, equal a b]
          tb2 = tan (b/2)
          toRadian d = d*pi/180
          convert = tan . toRadian . ((/) 4)          

-- This function seems to be missing 
vZipWith :: Base repr => (repr a -> repr b -> repr c) -> repr (Vector a) -> repr (Vector b) -> repr (Vector c)
vZipWith = undefined
