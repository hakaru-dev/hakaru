module BirdMH where

import InterpreterMH (Measure, Cond, mcmc,
                           unconditioned, conditioned,
                           normal, categorical, dirac)
import Visual (viz)
import Util.Csv
import Data.Dynamic (toDyn)
import Control.Monad (replicateM, forM_, foldM_)
import System.IO (stderr, hPutStrLn)
import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure)
import Data.Array.Unboxed

logToLogFloat = exp

type Year    = Int
type Day     = Int
type Cell    = Int
type Feature = Int

nfeature :: Feature
nfeature = 4

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

readObservations :: FilePath -> IO (UArray (Year, Day) Cell)
readObservations observationsFile = do
  rows <- decodeFileStream observationsFile
  return $ array ((1,1),(30,20))
         $ [ ((year,day),
              case [ cell | (cell,count) <- zip [1..] counts, count > (0::Int) ] of
                [cell] -> cell
                []     -> 0 {- unseen bird -} )
           | year:::day:::counts <- rows ]

readConds :: FilePath -> IO [Cond]
readConds observationsFile = do
  observations <- readObservations observationsFile
  return [ if o == 0 then Nothing else Just (toDyn o)
         | o <- elems observations ]

bird :: UArray (Year, Day, Cell, Cell, Feature) Double -> Measure [Double]
bird features = do
  params <- replicateM nfeature (unconditioned (normal 0 10))
  let transition year day from
        = conditioned
        $ categorical
        $ [ (to, logToLogFloat score)
          | to <- neighbors from
          , let score = sum [ param * (features ! (year, day, from, to, i))
                            | (i,param) <- zip [1..] params ] ]
  forM_ [1..30::Year] $ \year -> do
    start <- conditioned (dirac (1::Cell))
    foldM_ (\from day -> transition year day from)
           start
           [1..19::Day]
  return params

main :: IO ()
main = do
  args <- getArgs
  case args of
    [featuresFile, observationsFile, _outputFile] -> do
      features <- readFeatures featuresFile
      conds <- readConds observationsFile
      samples <- mcmc (bird features) conds
      -- mapM_ print samples
      viz 10000 ["f1","f2","f3","f4"] samples
    _ -> do
      progName <- getProgName
      hPutStrLn stderr ("Usage: " ++ progName ++ " \
        \<featuresFile> <observationsFile> <outputFile>")
      hPutStrLn stderr ("Example: " ++ progName ++ " \\\n\
        \\t\tinput/dataset1/onebird_features.csv \\\n\
        \\t\tinput/dataset1/onebird-observations.csv \\\n\
        \\t\toutput/dataset1/estimated-parameters.csv")
      exitFailure
