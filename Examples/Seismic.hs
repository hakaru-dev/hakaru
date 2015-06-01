{-# LANGUAGE RankNTypes, TypeOperators, ScopedTypeVariables, TypeFamilies, FlexibleContexts #-}
{-# OPTIONS -Wall -fno-warn-name-shadowing #-}
module Examples.Seismic where

import Prelude hiding (Real)
import Language.Hakaru.Syntax
import Language.Hakaru.Expect
import Language.Hakaru.Sample
--import Language.Hakaru.Simplify
import Language.Hakaru.Lazy

import System.Environment
import qualified Data.Map as M
import qualified Data.Number.LogFloat as LF

degrees, radians :: (Floating a) => a -> a
degrees r = r * 180 / pi
radians d = d * pi / 180

gz' :: (Base repr) => (repr Real, repr Real) ->
                      (repr Real, repr Real) -> repr Real
gz' (lon1,lat1) (lon2,lat2) = -- Section A.1
  degrees (atan (y/x) + if_ (less x 0) (if_ (less y 0) (-pi) pi) 0)
  where y = sin dlon
        x = cos rat1 * tan rat2 - sin rat1 * cos dlon
        rat1 = radians lat1
        rat2 = radians lat2
        dlon = radians (lon2 - lon1)

mod' :: (Mochastic repr) => repr Real -> repr Real -> repr (Measure Real)
mod' a b = counting `bind` \n ->
           let a' = a + b * fromInt n in
           if_ (and_ [not_ (less a' 0), less a' b])
               (dirac a')
               (superpose [])

dist :: (Base repr) => (repr Real, repr Real) ->
                       (repr Real, repr Real) -> repr Real
dist (lon1,lat1) (lon2,lat2) = -- Section A.3
  degrees (atan (y/x) + if_ (less x 0) pi 0)
  where y = sqrt ( (cos rat2 * sin dlon) ** 2
                 + (cos rat1 * sin rat2 - sin rat1 * cos rat2 * cos dlon) ** 2 )
        x = sin rat1 * sin rat2 + cos rat1 * cos rat2 * cos dlon
        rat1 = radians lat1
        rat2 = radians lat2
        dlon = radians (lon2 - lon1)

logistic :: (Base repr) => repr Real -> repr Prob
logistic x = recip (1 + exp_ (-x)) -- Section B.6

invertSlowness :: Floating a => a -> a
invertSlowness s = (s - 10.7) / (-0.046)

invertAzimuth :: Floating a => (a, a) -> a -> a -> (a, a)
invertAzimuth (lat, lon) dist azi = undefined

computeTravelTime :: Double -> Double
computeTravelTime = unSample (lam iT)

type Matrix3 a = (Vector3 a, Vector3 a, Vector3 a) -- row-major
type Vector3 a = (a, a, a)

determinant :: (Fractional a) => Matrix3 a -> a
determinant ((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) =
    a11*a22*a33 + a12*a23*a31 + a13*a21*a32
  - a13*a22*a31 - a12*a21*a33 - a11*a23*a32

inverse :: (Fractional a) => Matrix3 a -> Matrix3 a
inverse a@((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) =
  let f b11 b12 b21 b22 = (b11 * b22 - b12 * b21) / determinant a
  in ((f a22 a23 a32 a33, f a13 a12 a33 a32, f a12 a13 a22 a23),
      (f a23 a21 a33 a31, f a11 a13 a31 a33, f a13 a11 a23 a21),
      (f a21 a22 a31 a32, f a12 a11 a32 a31, f a11 a12 a21 a22))

vvSub :: (Fractional a) => Vector3 a -> Vector3 a -> Vector3 a
vvSub (a1,a2,a3) (b1,b2,b3) = (a1-b1, a2-b2, a3-b3)

vvMult :: (Fractional a) => Vector3 a -> Vector3 a -> a
vvMult (a1,a2,a3) (b1,b2,b3) = a1*b1 + a2*b2 + a3*b3

mvMult :: (Fractional a) => Matrix3 a -> Vector3 a -> Vector3 a
mvMult (a1,a2,a3) b = (vvMult a1 b, vvMult a2 b, vvMult a3 b)

normal3 :: (Mochastic repr) => Vector3 (repr Real) -> Matrix3 (repr Real) ->
           (Vector3 (repr Real) -> repr (Measure w)) -> repr (Measure w)
normal3 mean cov c = -- Section B.8
  lebesgue `bind` \x1 ->
  lebesgue `bind` \x2 ->
  lebesgue `bind` \x3 ->
  let x = (x1,x2,x3)
      y = vvSub x mean in
  weight (pow_ (pow_ (2 * pi_) 3 * unsafeProb (determinant cov)) (-1/2)
        * exp_ (- vvMult y (mvMult (inverse cov) y) / 2)) $
  c x

type Station = -- Sections 3 and 1.6
    ( Real -- longitude, in degrees between -180 and 180
  , ( Real -- latitude, in degrees between -90 and 90
  , ( Real -- $\mu _{d0}^k$
  , ( Real -- $\mu _{d1}^k$
  , ( Real -- $\mu _{d2}^k$
  , ( Prob -- $\theta _t^k$
  , ( Prob -- $\theta _z^k$
  , ( Prob -- $\theta _s^k$
  , ( Real -- $\mu _{a0}^k$
  , ( Real -- $\mu _{a1}^k$
  , ( Real -- $\mu _{a2}^k$
  , ( Prob -- $\sigma _a^k$
  , ( Prob -- $\lambda_f^k$
  , ( Real -- $\mu    _f^k$
  , ( Prob -- $\theta _f^k$
  )))))))))))))))

type Station' =
    ( Double -- longitude, in degrees between -180 and 180
  , ( Double -- latitude, in degrees between -90 and 90
  , ( Double -- $\mu _{d0}^k$
  , ( Double -- $\mu _{d1}^k$
  , ( Double -- $\mu _{d2}^k$
  , ( LF.LogFloat -- $\theta _t^k$
  , ( LF.LogFloat -- $\theta _z^k$
  , ( LF.LogFloat -- $\theta _s^k$
  , ( Double -- $\mu _{a0}^k$
  , ( Double -- $\mu _{a1}^k$
  , ( Double -- $\mu _{a2}^k$
  , ( LF.LogFloat -- $\sigma _a^k$
  , ( LF.LogFloat -- $\lambda_f^k$
  , ( Double -- $\mu    _f^k$
  , ( LF.LogFloat -- $\theta _f^k$
  )))))))))))))))

type Event = -- Sections 1.1 and 4.1
    ( Real -- longitude, in degrees between -180 and 180
  , ( Real -- latitude, in degrees between -90 and 90
  , ( Prob -- magnitude
  , ( Real -- time, in seconds
  ))))

type Event' =
    ( Double -- longitude, in degrees between -180 and 180
  , ( Double -- latitude, in degrees between -90 and 90
  , ( LF.LogFloat -- magnitude
  , ( Double -- time, in seconds
  ))))

type Detection = -- Sections 1.2 and 4.1
    ( Real -- time, in seconds
  , ( Real -- azimuth
  , ( Real -- slowness
  , ( Prob -- amplitude
  ))))

type Detection' =
    ( Double -- time, in seconds
  , ( Double -- azimuth
  , ( Double -- slowness
  , ( LF.LogFloat -- amplitude
  ))))

constT :: (Base repr) => repr Real
constT = 3600 -- Section 2

muMagnitude, thetaMagnitude, gammaMagnitude :: (Base repr) => repr Prob
muMagnitude    = 3.0 -- Section 2
thetaMagnitude = 4.0 -- Section 2
gammaMagnitude = 6.0 -- Section 2

gammaM :: Double
gammaM = unSample (fromProb gammaMagnitude)

station :: (Mochastic repr) => repr Real -> repr Real -> repr (Measure Station)
station longitude latitude = -- Section 2
  normal3 (-10.4, 3.26, -0.0499)
          ((13.43, -2.36, -0.0122),
           (-2.36, 0.452, 0.000112),
           (-0.0122, 0.000112, 0.000125)) $ \(mu_d0, mu_d1, mu_d2) ->
  invgamma 120 118 `bind` \theta_t ->
  invgamma 5.2 44 `bind` \theta_z ->
  invgamma 6.7 7.5 `bind` \theta_s ->
  normal3 (-7.3, 2.03, -0.00196)
          ((1.23, -0.227, -0.000175),
           (-0.227, 0.0461, 0.0000245),
           (-0.000175, 0.0000245, 0.000000302)) $ \(mu_a0, mu_a1, mu_a2) ->
  invgamma 21.1 12.6 `bind` \sigma_a2 ->
  gamma 2.1 0.0013 `bind` \lambda_f ->
  normal (-0.68) 0.68 `bind` \mu_f ->
  invgamma 23.5 12.45 `bind` \theta_f ->
  dirac (longitude `pair` latitude `pair`
         mu_d0 `pair` mu_d1 `pair` mu_d2 `pair`
         theta_t `pair` theta_z `pair` theta_s `pair`
         mu_a0 `pair` mu_a1 `pair` mu_a2 `pair` sqrt_ sigma_a2 `pair`
         lambda_f `pair` mu_f `pair` theta_f)

event :: (Mochastic repr) => repr (Measure Event)
event = -- Section 1.1, except the Poisson
  uniform 0 constT `bind` \time ->
  uniform (-180) 180 `bind` \longitude ->
  uniform (-1) 1 `bind` \sinLatitude ->
  exponential thetaMagnitude `bind` \m ->
  dirac (longitude `pair` degrees (asin sinLatitude)
                   `pair` m -- max_ muMagnitude (min_ gammaMagnitude m) -- commented out for density calculation
                   `pair` time)

iT :: (Base repr) => repr Real -> repr Real
iT delta = -0.023 * delta ** 2 + 10.7 * delta + 5

iS :: (Base repr) => repr Real -> repr Real
iS delta = -0.046 * delta + 10.7 -- Section 1.4

trueDetection :: (Mochastic repr) => repr Station -> repr Event ->
                 repr (Measure (Either
                                  ()        -- mis-detection
                                  Detection -- not mis-detection
                               ))
trueDetection s e = -- Sections 1.2--1.5
  unpair s $ \longitude s ->
  unpair s $ \latitude s ->
  unpair s $ \mu_d0 s ->
  unpair s $ \mu_d1 s ->
  unpair s $ \mu_d2 s ->
  unpair s $ \theta_t s ->
  unpair s $ \theta_z s ->
  unpair s $ \theta_s s ->
  unpair s $ \mu_a0 s ->
  unpair s $ \mu_a1 s ->
  unpair s $ \mu_a2 s ->
  unpair s $ \sigma_a s ->
  unpair s $ \_lambda_f s ->
  unpair s $ \_mu_f _theta_f ->
  let sl = (longitude, latitude) in
  unpair e $ \eventLongitude e ->
  unpair e $ \eventLatitude e ->
  unpair e $ \eventMagnitude eventTime ->
  let el = (eventLongitude, eventLatitude) in
  dirac (dist sl el) `bind` \distance ->
  bern (logistic ( mu_d0
                 + mu_d1 * fromProb eventMagnitude
                 + mu_d2 * distance )) `bind` \b ->
  if_ (not_ b) (dirac (inl unit)) $
  laplace (eventTime + iT distance) {- Section 2 says $\mu_t^k=0$ -}
          theta_t `bind` \time ->
  if_ (less constT time) (dirac (inl unit)) $
  laplace 0 {- Section 2 says $\mu_z^k=0$ -}
          theta_z `bind` \dazimuth ->
  mod' (gz' sl el + dazimuth) 360 `bind` \azimuth ->
  laplace (iS distance) {- Section 2 says $\mu_s^k=0$ -}
          theta_s `bind` \slowness ->
  normal ( mu_a0
         + mu_a1 * fromProb eventMagnitude
         + mu_a2 * distance )
         -- For the previous line, the LaTeX description says "iT distance"
         -- but the Python code suggests "iT" is a typo.
         sigma_a `bind` \logAmplitude ->
  dirac (inr (time `pair` azimuth `pair` slowness `pair` exp_ logAmplitude))

falseDetection :: (Mochastic repr) => repr Station -> repr (Measure Detection)
falseDetection s = -- Section 1.6, except the Poisson
  unpair s $ \_longitude s ->
  unpair s $ \_latitude s ->
  unpair s $ \_mu_d0 s ->
  unpair s $ \_mu_d1 s ->
  unpair s $ \_mu_d2 s ->
  unpair s $ \_theta_t s ->
  unpair s $ \_theta_z s ->
  unpair s $ \_theta_s s ->
  unpair s $ \_mu_a0 s ->
  unpair s $ \_mu_a1 s ->
  unpair s $ \_mu_a2 s ->
  unpair s $ \_sigma_a s ->
  unpair s $ \_lambda_f s ->
  unpair s $ \mu_f theta_f ->
  uniform 0 constT `bind` \time ->
  uniform 0 360 `bind` \azimuth ->
  uniform (iS 180) (iS 0) `bind` \slowness ->
  cauchy mu_f theta_f `bind` \logAmplitude ->
  dirac (time `pair` azimuth `pair` slowness `pair` exp_ logAmplitude)

{- The inference performed in:
   https://github.com/GaloisInc/ppaml-cp4/blob/master/problems/problem8/pysolve.py

   determines the best detections for each event. 

   Each detection is used to predict the location of an event
   through exact inference. The process is repeated several times
   with perturbations of the detection to obtain multiple candidates.

   These event candidates are then each associated with most likely detection
   from each station which detected it. The candidate who's most likely given
   the detections associated with it is added to an event list.

   The detections associated with this event are then removed and the process
   repeats until all detections have been removed, or 20 events are in the
   event list, whichever comes first.

   TODO: Add hakaru code for each of these steps
 
-}

laplacePerc q | q >= 0   && q <= 0.5 = log (2*q)
laplacePerc q | q >= 0.5 && q <= 1.0 = - log (2*(1-q))
laplacePerc _ = error "percentiles are between 0 and 1"

solveEpisode :: Base repr => [(repr Station, repr Detection)] -> [(repr Event, [repr Detection])]
solveEpisode = undefined

generateCandidates :: Base repr => repr Detection -> [repr Event]
generateCandidates = undefined

findBestDetections :: Event' ->
                     [(Station', Detection')] ->
                      M.Map Station' (Detection', Double) ->
                      [(Station', Detection')]
findBestDetections e ((s,d):rest) m =
    case M.lookup s m of
      Just (_, ll) -> let ll' = eventLL e s d in
                         if (ll' < ll)
                         then findBestDetections e rest m
                         else findBestDetections e rest (M.insert s (d, ll') m)
      Nothing -> findBestDetections e rest (M.insert s (d, (eventLL e s d)) m)
findBestDetections e [] m = map (\ (s, (d, _)) -> (s,d)) (M.assocs m)

eventLL :: Event' -> Station' -> Detection' -> Double
eventLL e s d = unSample (lam3 $ \e s d -> fromProb $ dens s (pair e (inr d))) e s d
   where dens :: Sample IO (Expect' Station) ->
                 Sample IO (Expect' (Event, Either () Detection)) ->
                 Sample IO Prob
         dens = head $ density (\s -> event `bindx` (trueDetection s))

densT :: (Lambda repr, Integrate repr, Mochastic repr) =>
         repr Station ->
         repr (Expect' Event) ->
         repr (Expect' Detection) ->
         repr Prob
densT s e d = (head $ density (\s -> event `bindx` (trueDetection s))) s (pair e (inr d))

station1 :: Base repr => repr Station
station1 = pair 133.9 (pair (-23.71)
           (pair (-5.7814139398408066) (pair 2.3145847470983005 (pair (-0.045404100548749146) (pair
           0.90090308789365892 (pair 10.375546736486864 (pair  0.96913103078757756  (pair
           (-8.6958852446415698) (pair 2.2868735296486626 (pair (-0.0013429424346670985) (pair
           0.70293926034604937 (pair 0.002315667198328261 (pair
           (-1.8351128031038666) 0.62370899995668161)))))))))))))

invertDetection :: Detection' -> Station' -> Double -> Double -> Event'
invertDetection d s slowPerb aziPerb =
    let (time, (azimuth, (slowness, amplitude))) = d in
    let (slat, (slon, (_,(_,(_,(_,(_,(_,
         (mu_a0, (mu_a1, (mu_a2, _))))))))))) = s in
    let dist = invertSlowness (slowness + slowPerb) in
    let (lat, lon) = invertAzimuth (slat, slon) dist (azimuth + aziPerb) in
    let ttime = computeTravelTime dist in
    let evtime = time - ttime in
    let evmag  = (LF.logFromLogFloat amplitude - mu_a0 - mu_a2*dist) / mu_a1 in
    let evmag' = if evmag' > gammaM then gammaM else evmag in
    (lat,(lon,(LF.logFloat evmag',evtime)))

readEpisodes :: FilePath -> [Station'] -> IO [(Station', Detection')]
readEpisodes f s = do
  content <- readFile f
  let linesOfFile = lines content
  return undefined

readStations = undefined
readPhysics  = undefined

main :: IO ()
main = do
  [stations, physics, episodes] <- getArgs
  --readPhysics physics
  --sta <- readStations stations
  --readEpisodes sta episodes
  return ()
