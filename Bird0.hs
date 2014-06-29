module Bird0 where

import InterpreterDynamic (Measure, sample_,
                           unconditioned, conditioned,
                           normal, categorical, poisson)
import Util.Csv
import Types (Cond(..))
import Data.Number.LogFloat (logToLogFloat)
import Data.Dynamic (toDyn)
import Control.Monad (replicateM, forM_, foldM_)
import System.IO (stderr, hPutStrLn)
import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure)
import Data.Array.Unboxed

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

readObservations :: FilePath -> IO (UArray (Year, Day, Cell) Int)
readObservations observationsFile = do
  rows <- decodeFileStream observationsFile
  return $ array ((1,1,1),(30,20,ncell))
         $ [ ((year,day,cell), count)
           | year:::day:::counts <- rows
           , (cell,count) <- zip [1..] counts ]

readConds :: FilePath -> IO [Cond]
readConds observationsFile = do
  observations <- readObservations observationsFile
  return [ Discrete (toDyn o) | o <- elems observations ]

bird :: UArray (Year, Day, Cell, Cell, Feature) Double -> Measure [Double]
bird features = do
  params <- replicateM nfeature (unconditioned (normal 0 10))
  let transition year day from
        = unconditioned
        $ categorical
        $ [ (to, logToLogFloat score)
          | to <- neighbors from
          , let score = sum [ param * (features ! (year, day, from, to, i))
                            | (i,param) <- zip [1..] params ] ]
      observe cell
        = forM_ [1..ncell] $ \c ->
            conditioned (poisson (if c == cell then 1 else 0)) :: Measure Int
  forM_ [1..30::Year] $ \year -> do
    let start = 1 :: Cell
    observe start
    foldM_ (\from day -> do to <- transition year day from
                            observe to
                            return to)
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
      sample_ 100 (bird features) conds
    _ -> do
      progName <- getProgName
      hPutStrLn stderr ("Usage: " ++ progName ++ " \
        \<featuresFile> <observationsFile> <outputFile>")
      hPutStrLn stderr ("Example: " ++ progName ++ " \\\n\
        \\t\tinput/dataset1/onebird_features.csv \\\n\
        \\t\tinput/dataset1/onebird-observations.csv \\\n\
        \\t\toutput/dataset1/estimated-parameters.csv")
      exitFailure
