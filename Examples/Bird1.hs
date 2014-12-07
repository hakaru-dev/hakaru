{-# LANGUAGE Rank2Types, ScopedTypeVariables, DataKinds #-}

module Example.Bird1 where

-- Bird0 (one-bird model) in Hakaru 0.2

import Prelude hiding (Real)
import Language.Hakaru.Util.Csv
import Language.Hakaru.Syntax hiding (liftM)
import Language.Hakaru.Vector hiding (mapM)
import Language.Hakaru.Sample (unSample)
import Language.Hakaru.Disintegrate (runDisintegrate)
import System.Random.MWC (withSystemRandom)
import System.IO (stderr, hPutStrLn)
import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure)
import Data.Array.Unboxed
import Control.Monad (liftM, replicateM, replicateM_)

type Year    = Int
type Day     = Int
type Cell    = Int
type Feature = Int

nfeature :: Feature
nfeature = 4
type NFeature = S (S (S I))

nyear :: Year
nyear = 30
type NYear = S (S (S (S (S (S (S (S (S (S (
             S (S (S (S (S (S (S (S (S (S (
             S (S (S (S (S (S (S (S (S I))))))))))))))))))))))))))))

nday :: Day
nday = 20
type NDay = S (S (S (S (S (S (S (S (S (S (
            S (S (S (S (S (S (S (S (S I))))))))))))))))))

ncoord :: Cell
ncoord = 4

ncell :: Cell
ncell = ncoord * ncoord
type NCell = S (S (S (S (S (S (S (S (S (S (
             S (S (S (S (S I))))))))))))))

neighbors :: Cell -> [Cell]
neighbors cell
  = let (x,y) = divMod (cell - 1) ncoord
        square z = z * z
    in [ x' * ncoord + y' + 1
       | x' <- [max 0 (x-4) .. min (ncoord-1) (x+4)]
       , y' <- [max 0 (y-4) .. min (ncoord-1) (y+4)]
       , square (x'-x) + square (y'-y) < 18 {- 4.234 < sqrt 18 < 5 -} ]

readFeatures :: FilePath -> IO (UArray (Year, Day, Cell, Cell, Feature) Double)
readFeatures featuresFile = do
  rows <- decodeFileStream featuresFile
  return $ array ((1,1,1,1,1),(30,19,ncell,ncell,nfeature))
         $ concat [ [ ((year,day,from,to,i),fi) | (i,fi) <- zip [1..] fis ]
                  | year:::day:::from:::to:::fis <- rows ]

readObservations :: FilePath -> IO (UArray (Year, Day, Cell) Int)
readObservations observationsFile = do
  rows <- decodeFileStream observationsFile
  return $ array ((1,1,1),(30,20,ncell))
         $ [ ((year,day,cell), count)
           | year:::day:::counts <- rows
           , (cell,count) <- zip [1..] counts ]

readConds :: (Base repr) => FilePath ->
             IO (repr (Repeat NYear (Repeat NDay (Repeat NCell Int))))
readConds observationsFile = do
  observations <- readObservations observationsFile
  return undefined -- [ Discrete (toDyn o) | o <- elems observations ]

newtype M repr a =
  M { unM :: forall w. (a -> repr (Measure w)) -> repr (Measure w) }

instance Monad (M repr) where
  return a = M (\c -> c a)
  m >>= k  = M (\c -> unM m (\a -> unM (k a) c))

runM :: (Mochastic repr) => M repr (repr (Measure a)) -> repr (Measure a)
runM m = unM m id

lift :: (Mochastic repr) => repr (Measure a) -> M repr (repr a)
lift m = M (bind m)

birdYear :: forall repr. (Mochastic repr) =>
            (Day -> Cell -> Cell -> Feature -> Double) ->
            [repr Real] -> M repr (repr (Repeat NDay (Repeat NCell Int)))
birdYear features params = liftM (toNestedPair . fromList) (go 1 1) where
  go :: Day -> repr Cell -> M repr [repr (Repeat NCell Int)]
  go day from = do counts <- observe from
                   if day == nday then return [counts] else do
                     to <- transition day from
                     countss <- go (succ day) to
                     return (counts:countss)
  observe :: repr Cell -> M repr (repr (Repeat NCell Int))
  observe cell = liftM (toNestedPair . fromList)
               $ mapM (\c -> let nbird = if_ (cell `equal` fromIntegral c) 1 0
                             in lift (poisson nbird))
                      [1..ncell]
  transition :: Day -> repr Cell -> M repr (repr Cell)
  transition day from = lift (reflect from (\from -> categorical
    [ (exp_ score, fromIntegral to)
    | to <- neighbors from
    , let score = sum [ param * fromDouble (features day from to i)
                      | (i,param) <- zip [1..] params ] ]))
  reflect :: repr Cell -> (Cell -> repr a) -> repr a
  reflect cell f = loop 1 where
    loop c = if c == ncell then f c else
             if_ (cell `equal` fromIntegral c) (f c) (loop (succ c))
  fromDouble :: Double -> repr Real
  fromDouble = fromRational . toRational

bird :: (Mochastic repr) =>
        UArray (Year, Day, Cell, Cell, Feature) Double ->
        repr (Measure (Repeat NYear (Repeat NDay (Repeat NCell Int)),
                       Repeat NFeature Real))
bird features = runM $ do
  params <- replicateM nfeature (lift (normal 0 10))
  countsss <- mapM (\year -> let f day from to i =
                                   features ! (year, day, from, to, i)
                             in birdYear f params)
                   [1..nyear]
  return (dirac (pair (toNestedPair (fromList countsss))
                      (toNestedPair (fromList params))))

main :: IO ()
main = do
  args <- getArgs
  case args of
    [featuresFile, observationsFile, _outputFile] -> do
      features <- readFeatures featuresFile
      conds <- readConds observationsFile
      let d = runDisintegrate (\env -> bird features)
      let s = unSample (head d unit conds) 1
      withSystemRandom (\g -> replicateM_ 20 (s g >>= print))
    _ -> do
      progName <- getProgName
      hPutStrLn stderr ("Usage: " ++ progName ++ " \
        \<featuresFile> <observationsFile> <outputFile>")
      hPutStrLn stderr ("Example: " ++ progName ++ " \\\n\
        \\t\tinput/dataset1/onebird_features.csv \\\n\
        \\t\tinput/dataset1/onebird-observations.csv \\\n\
        \\t\toutput/dataset1/estimated-parameters.csv")
      exitFailure
