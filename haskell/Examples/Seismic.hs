{-# LANGUAGE TypeOperators, ScopedTypeVariables, TypeFamilies, FlexibleContexts, DataKinds #-}
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
import Data.List
import Data.Function (on)

degrees, radians :: (Floating a) => a -> a
degrees r = r * 180 / pi
radians d = d * pi / 180

gz' :: (Base repr)
    => (repr HReal, repr HReal)
    -> (repr HReal, repr HReal)
    -> repr HReal
gz' (lon1,lat1) (lon2,lat2) = -- Section A.1
  degrees (atan (y/x) + if_ (less x 0) (if_ (less y 0) (-pi) pi) 0)
  where y = sin dlon
        x = cos rat1 * tan rat2 - sin rat1 * cos dlon
        rat1 = radians lat1
        rat2 = radians lat2
        dlon = radians (lon2 - lon1)

mod' :: (Mochastic repr) => repr HReal -> repr HReal -> repr (HMeasure HReal)
mod' a b = counting `bind` \n ->
           let a' = a + b * fromInt n in
           if_ (and_ [not_ (less a' 0), less a' b])
               (dirac a')
               (superpose [])

dist :: (Base repr)
    => (repr HReal, repr HReal)
    -> (repr HReal, repr HReal)
    -> repr HReal
dist (lon1,lat1) (lon2,lat2) = -- Section A.3
  degrees (atan (y/x) + if_ (less x 0) pi 0)
  where y = sqrt ( (cos rat2 * sin dlon) ** 2
                 + (cos rat1 * sin rat2 - sin rat1 * cos rat2 * cos dlon) ** 2 )
        x = sin rat1 * sin rat2 + cos rat1 * cos rat2 * cos dlon
        rat1 = radians lat1
        rat2 = radians lat2
        dlon = radians (lon2 - lon1)

logistic :: (Base repr) => repr HReal -> repr HProb
logistic x = recip (1 + exp_ (-x)) -- Section B.6

invertSlowness :: Floating a => a -> a
invertSlowness s = (s - 10.7) / (-0.046)

invertAzimuth :: RealFloat a => (a, a) -> a -> a -> (a, a)
invertAzimuth (lat, lon) dist azi =
    let [lat1, lon1, dist1, azi1] = map radians [lat, lon, dist, azi] in
    let lat2 = asin (sin lat1 * cos dist1 +
                     cos lat1 * sin dist1 * cos azi1) in
    let lon2 = lon1 + atan2 (sin azi1 * sin dist1 * cos lat1) (cos dist1 - sin lat1 * sin lat2) in
    (degrees lat2, degrees lon2)

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

normal3
    :: (Mochastic repr)
    => Vector3 (repr HReal)
    -> Matrix3 (repr HReal)
    -> (Vector3 (repr HReal) -> repr (HMeasure w))
    -> repr (HMeasure w)
normal3 mean cov c = -- Section B.8
  lebesgue `bind` \x1 ->
  lebesgue `bind` \x2 ->
  lebesgue `bind` \x3 ->
  let x = (x1,x2,x3)
      y = vvSub x mean in
  weight (pow_ (pow_ (2 * pi_) 3 * unsafeProb (determinant cov)) (-1/2)
        * exp_ (- vvMult y (mvMult (inverse cov) y) / 2)) $
  c x

type HStation = -- Sections 3 and 1.6
    (HPair HReal -- longitude, in degrees between -180 and 180
    (HPair HReal -- latitude, in degrees between -90 and 90
    (HPair HReal -- $\mu _{d0}^k$
    (HPair HReal -- $\mu _{d1}^k$
    (HPair HReal -- $\mu _{d2}^k$
    (HPair HProb -- $\theta _t^k$
    (HPair HProb -- $\theta _z^k$
    (HPair HProb -- $\theta _s^k$
    (HPair HReal -- $\mu _{a0}^k$
    (HPair HReal -- $\mu _{a1}^k$
    (HPair HReal -- $\mu _{a2}^k$
    (HPair HProb -- $\sigma _a^k$
    (HPair HProb -- $\lambda_f^k$
    (HPair HReal -- $\mu    _f^k$
    (      HProb -- $\theta _f^k$
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

type HEvent = -- Sections 1.1 and 4.1
    (HPair HReal -- longitude, in degrees between -180 and 180
    (HPair HReal -- latitude, in degrees between -90 and 90
    (HPair HProb -- magnitude
    (      HReal -- time, in seconds
    ))))

type Event' =
    ( Double -- longitude, in degrees between -180 and 180
  , ( Double -- latitude, in degrees between -90 and 90
  , ( LF.LogFloat -- magnitude
  , ( Double -- time, in seconds
  ))))

type HDetection = -- Sections 1.2 and 4.1
    (HPair HReal -- time, in seconds
    (HPair HReal -- azimuth
    (HPair HReal -- slowness
    (      HProb -- amplitude
    ))))

type Detection' =
    ( Double -- time, in seconds
  , ( Double -- azimuth
  , ( Double -- slowness
  , ( LF.LogFloat -- amplitude
  ))))

type Episode' = [(Station', Detection')]

constT :: (Base repr) => repr HReal
constT = 3600 -- Section 2

muMagnitude, thetaMagnitude, gammaMagnitude :: (Base repr) => repr HProb
muMagnitude    = 3.0 -- Section 2
thetaMagnitude = 4.0 -- Section 2
gammaMagnitude = 6.0 -- Section 2

gammaM :: Double
gammaM = unSample (fromProb gammaMagnitude)

station :: (Mochastic repr) => repr HReal -> repr HReal -> repr (HMeasure HStation)
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

event :: (Mochastic repr) => repr (HMeasure HEvent)
event = -- Section 1.1, except the Poisson
  uniform 0 constT `bind` \time ->
  uniform (-180) 180 `bind` \longitude ->
  uniform (-1) 1 `bind` \sinLatitude ->
  exponential thetaMagnitude `bind` \m ->
  dirac (longitude `pair` degrees (asin sinLatitude)
                   `pair` m -- max_ muMagnitude (min_ gammaMagnitude m) -- commented out for density calculation
                   `pair` time)

iT :: (Base repr) => repr HReal -> repr HReal
iT delta = -0.023 * delta ** 2 + 10.7 * delta + 5

iS :: (Base repr) => repr HReal -> repr HReal
iS delta = -0.046 * delta + 10.7 -- Section 1.4

trueDetection
    :: (Mochastic repr)
    => repr HStation
    -> repr HEvent
    -> repr (HMeasure (HEither
        HUnit      -- mis-detection
        HDetection -- not mis-detection
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

falseDetection
    :: (Mochastic repr)
    => repr HStation
    -> repr (HMeasure HDetection)
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

laplacePerc :: (RealFloat a) => a -> a
laplacePerc q | q >= 0   && q <= 0.5 = log (2*q)
laplacePerc q | q >= 0.5 && q <= 1.0 = - log (2*(1-q))
laplacePerc _ = error "percentiles are between 0 and 1"

solveEpisode :: Episode' -> [(Event', [(Station', Detection')])]
solveEpisode sd@((s,d):_) =
    let events = generateCandidates s d in
    let (e,(sd',_)) = maximumBy (compare `on` (snd .snd))
                      (map (\e -> (e, findBestDetections e sd M.empty)) events) in
    (e,sd') : solveEpisode (sd \\ sd')

generateCandidates :: Station' -> Detection' -> [Event']
generateCandidates s@(_,(_,(_,(_,(_,(_,(theta_z,(theta_s, _))))))))
                   d  =
    map (\(azi,slow) -> invertDetection d s azi slow) (perbs [0.1, 0.2 .. 0.9])
  where perbs l = [(LF.fromLogFloat theta_z*(laplacePerc dazi),
                    LF.fromLogFloat theta_s*(laplacePerc dslow))  |
                   dazi <- l, dslow <- l]

findBestDetections
    :: Event'
    -> [(Station', Detection')]
    -> M.Map Station' (Detection', Double)
    -> ([(Station', Detection')], Double)
findBestDetections e ((s,d):rest) m =
    case M.lookup s m of
      Just (_, ll) -> let ll' = eventLL e s d in
                         if (ll' < ll)
                         then findBestDetections e rest m
                         else findBestDetections e rest (M.insert s (d, ll') m)
      Nothing -> findBestDetections e rest (M.insert s (d, (eventLL e s d)) m)
findBestDetections _ [] m = (map (\ (s, (d, _)) -> (s,d)) (M.assocs m),
                             sum $ map snd (M.elems m))

eventLL :: Event' -> Station' -> Detection' -> Double
eventLL e s d = unSample (lam3 $ \e s d -> fromProb $ dens s (pair e (inr d))) e s d
    where
    dens :: Sample IO (Expect' HStation)
        -> Sample IO (Expect' (HPair HEvent (HEither HUnit HDetection)))
        -> Sample IO HProb
    dens = head $ density (\s -> event `bindx` (trueDetection s))

densT
    :: (Lambda repr, Integrate repr, Mochastic repr)
    => repr HStation
    -> repr (Expect' HEvent)
    -> repr (Expect' HDetection)
    -> repr HProb
densT s e d = (head $ density (\s -> event `bindx` (trueDetection s))) s (pair e (inr d))

invertDetection :: Detection' -> Station' -> Double -> Double -> Event'
invertDetection d s aziPerb slowPerb =
    let (time, (azimuth, (slowness, amplitude))) = d in
    let (slat, (slon, (_,(_,(_,(_,(_,(_,
         (mu_a0, (mu_a1, (mu_a2, _))))))))))) = s in
    let dist = invertSlowness (slowness + slowPerb) in
    let (lat, lon) = invertAzimuth (slat, slon) dist (azimuth + aziPerb) in
    let ttime = computeTravelTime dist in
    let evtime = time - ttime in
    let evmag  = (LF.logFromLogFloat amplitude - mu_a0 - mu_a2*dist) / mu_a1 in
    let evmag' = if evmag > gammaM then gammaM else evmag in
    (lat,(lon,(LF.logFloat evmag',evtime)))

configMap :: [String] -> M.Map String [Double] -> M.Map String [Double]
configMap []     m = m
configMap (e:es) m = configMap es (updateMap $ split e '=')
   where updateMap ([key,vals]) | head (tail vals) == '[' =  M.insert key (read   vals :: [Double]) m
                                | otherwise =  M.insert key ([read vals] :: [Double]) m 

makeStation :: M.Map String [Double] -> (Int, [String]) -> Station'
makeStation m (id,[name,lat,lon]) = (read lat :: Double
                                  , (read lon :: Double
                                  , (m M.! "mu_d0 " !! id 
                                  , (m M.! "mu_d1 " !! id 
                                  , (m M.! "mu_d2 " !! id
                                  , (LF.logFloat $ m M.! "theta_t "  !! id
                                  , (LF.logFloat $ m M.! "theta_z "  !! id
                                  , (LF.logFloat $ m M.! "theta_s "  !! id
                                  , (m M.! "mu_a0 " !! id
                                  , (m M.! "mu_a1 " !! id
                                  , (m M.! "mu_a2 " !! id
                                  , (LF.logFloat $ m M.! "sigma_a "  !! id
                                  , (LF.logFloat $ m M.! "lambda_f " !! id
                                  , (m M.! "mu_f " !! id
                                  , (LF.logFloat $ m M.! "theta_f "  !! id
                                  )))))))))))))))

makeDetection :: [Station'] -> [String] -> (Station', Detection')
makeDetection stations [id,time,azi,slow,amp] =
    (station, (read time
            , (read azi
            , (read slow
            , (LF.logFloat $ (read amp :: Double))))))
    where station = stations !! read id

split :: Eq a => [a] -> a -> [[a]]
split s q = case break (== q) s of
              ([], _)  -> []
              (s', []) -> [s']
              (s', q:rest) -> s' : split rest q
             
readEpisodes :: FilePath -> [Station'] -> IO [Episode']
readEpisodes episodeFile stations = do
  content <- readFile episodeFile
  let linesOfFile = lines content
  let episodes = split linesOfFile ""
  return $ map (parseEpisode stations) (tail episodes)

parseEpisode :: [Station'] -> [String] -> Episode'
parseEpisode stations episode =
  let suffix = tail $ dropWhile (not . isPrefixOf "Detections:") episode in
  let episode' = takeWhile (not . isPrefixOf "Assocs") suffix in
  map (\s -> makeDetection stations (words s)) episode'

readStations :: FilePath -> IO [Station']
readStations paramsFile = do
  params  <- readFile paramsFile
  let [stations, physics] = split (lines params) ""
  let stations' = zip [0..] (map words stations)
  let paramMap  = configMap physics M.empty
  return $ map (makeStation paramMap) stations'

--
writeEpisode
    :: FilePath
    -> [Station']
    -> [(Event', [(Station', Detection')])]
    -> IO ()
writeEpisode f stations es = do
  writeFile f "Events:"
  mapM_ (\ ((lat,(lon,(mag,(time)))),_) ->
         let s = '\n' : (intercalate " " $ map show [lat, lon, LF.fromLogFloat mag, time]) in
         appendFile f s) es
  appendFile f "Detections:"
  appendFile f "Assocs:"

main :: IO ()
main = do
  [paramsFile, episodesFile, outFile] <- getArgs
  sta <- readStations paramsFile
  epi <- readEpisodes episodesFile sta
  mapM_ (writeEpisode outFile sta . solveEpisode) epi
