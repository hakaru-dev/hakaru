{-# LANGUAGE Rank2Types, DataKinds #-}
{-# OPTIONS -W #-}

module Main where

-- Bird0 (one-bird model) in Hakaru 0.2

import Prelude hiding (Real)
import Language.Hakaru.Util.Csv
import Language.Hakaru.Syntax hiding (liftM)
import Language.Hakaru.Vector hiding (mapM)
import Language.Hakaru.Sample (unSample)
import Language.Hakaru.Partial (runPartial, dynamic)
import Language.Hakaru.PrettyPrint (runPrettyPrint)
import System.Random.MWC (withSystemRandom)
import System.IO (stderr, hPutStrLn)
import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure)
import Data.Array.Unboxed
import Control.Monad (replicateM_)

type Year    = Int
type Day     = Int
type Cell    = Int
type Feature = Int

nfeature :: Feature
nfeature = 4
type NFeature = S (S (S I))

nyear :: Year
nyear = 30

nday :: Day
nday = 20

ncoord :: Cell
ncoord = 4

ncell :: Cell
ncell = ncoord * ncoord

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

birdYear :: (Mochastic repr) =>
            (Day -> Cell -> Cell -> Feature -> Double) ->
            (Day -> Cell -> Int) ->
            Repeat NFeature (repr Real) -> repr (Measure Cell)
birdYear features obs = go nday where
  go :: (Mochastic repr) =>
        Day -> Repeat NFeature (repr Real) -> repr (Measure Cell)
  go day@1 _      = observe 1 (obs day)
  go day   params = let params' = dynamic <$> params in runPartial $
                    go (day - 1) params' `bind` \from ->
                    transition params' (day - 1) from `bind` \to ->
                    observe to (obs day)
  observe :: (Mochastic repr) =>
             repr Cell -> (Cell -> Int) -> repr (Measure Cell)
  observe cell o = case [ c | c <- [1..ncell], o c > 0 ] of
                     []  -> dirac cell
                     [c] -> if_ (cell `equal` fromIntegral c)
                                (dirac cell)
                                (superpose [])
                     _   -> error "Birds observed in multiple cells at once!?"
  transition :: (Mochastic repr) => Repeat NFeature (repr Real) ->
                Day -> repr Cell -> repr (Measure Cell)
  transition params day from = reflect from (\f -> categorical
    [ (exp_ score, fromIntegral to)
    | to <- neighbors f
    , let score = sum $ toList
                $ (\i param -> param * fromDouble (features day f to i))
                  <$> iota 1 <*> params ])
  reflect :: (Mochastic repr) => repr Cell -> (Cell -> repr a) -> repr a
  reflect cell f = loop 1 where
    loop c = if c == ncell then f c else
             if_ (cell `equal` fromIntegral c) (f c) (loop (succ c))
  fromDouble :: (Base repr) => Double -> repr Real
  fromDouble = fromRational . toRational

birdYear' :: forall repr. (Mochastic repr) =>
             (Day -> Cell -> Cell -> Feature -> Double) ->
             (Day -> Cell -> Int) ->
             Repeat NFeature (repr Real) -> repr (Measure ())
birdYear' features obs params =
  runPartial (birdYear features obs (dynamic <$> params) `bind_` dirac unit)

bird :: (Mochastic repr) =>
        UArray (Year, Day, Cell, Cell, Feature) Double ->
        UArray (Year, Day, Cell) Int ->
        repr (Measure (Repeat NFeature Real))
bird features observations =
  normal 0 10 `bind` \p1 ->
  normal 0 10 `bind` \p2 ->
  normal 0 10 `bind` \p3 ->
  normal 0 10 `bind` \p4 ->
  let params = (p1, (p2, (p3, (p4, ()))))
      g k year = let f day from to i =
                       features ! (year, day, from, to, i)
                     o day cell =
                       observations ! (year, day, cell)
                 in birdYear f o params `bind_` k
  in foldl g (dirac (toNestedPair params)) [1{-..nyear-}]

main :: IO ()
main = do
  args <- getArgs
  case args of
    [featuresFile, observationsFile, _outputFile] -> do
      hPutStrLn stderr ("Reading " ++ featuresFile)
      features <- readFeatures featuresFile
      hPutStrLn stderr ("Reading " ++ observationsFile)
      observations <- readObservations observationsFile
      hPutStrLn stderr "Building model"
      let m = bird features observations
      --writeFile "/tmp/m" (show (runPrettyPrint m))
      let s = unSample m 1
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
