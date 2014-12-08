{-# LANGUAGE Rank2Types, DataKinds #-}
{-# OPTIONS -W #-}

module Main (main) where

-- Bird0 (one-bird model) in Hakaru 0.2

import Prelude hiding (Real)
import Language.Hakaru.Util.Csv
import Language.Hakaru.Syntax hiding (liftM)
import Language.Hakaru.Vector hiding (mapM)
import Language.Hakaru.Sample (unSample)
import Language.Hakaru.Partial (Partial, runPartial, dynamic)
import Language.Hakaru.PrettyPrint (runPrettyPrint)
import System.Random.MWC (withSystemRandom)
import System.IO (stderr, hPutStrLn)
import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure)
import Data.Maybe (isNothing)
import Data.Number.LogFloat (LogFloat, logFromLogFloat)
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

span' :: Int -> (a -> Bool) -> [a] -> ([a], [a])
span' _ _ xs@[]      = (xs, xs)
span' n p xs@(x:xs')
  | n > 0 && p x     = let (ys,zs) = span' (n-1) p xs' in (x:ys,zs)
  | otherwise        = ([],xs)

partials :: (Mochastic repr) =>
            Partial repr Cell ->
            [(Partial repr Cell -> Partial repr (Measure Cell), Maybe Int)] ->
            repr (Measure ())
partials from l = case span' 4 (isNothing . snd) l of
  (_, []) -> dirac unit
  (unobserved, (observed, observation) : rest) ->
    let bunch = foldl1 (\t c from -> t from `bind` c)
                       (map fst unobserved ++ [observed])
                       from
    in case observation of
         Just o -> runPartial (bunch `bind` \to ->
                               if_ (to `equal` fromIntegral o)
                                   (dirac unit)
                                   (superpose []))
                   `bind_` partials (fromIntegral o) rest
         Nothing -> -- runPartial bunch `bind` \to ->
                    -- partials (dynamic to) rest
                    dirac unit

birdYear :: (Mochastic repr) =>
            (Day -> Cell -> Cell -> Feature -> Double) ->
            (Day -> Cell -> Int) ->
            Repeat NFeature (repr Real) -> repr (Measure ())
birdYear features obs params =
  partials 1
           [ ( if day > 1 then transition params' (day - 1) else dirac
             , observe (obs day) )
           | day <- [1..nday] ]
 where
  params' = dynamic <$> params
  observe :: (Cell -> Int) -> Maybe Int
  observe o = case [ c | c <- [1..ncell], o c > 0 ] of
                []  -> Nothing
                [c] -> Just c
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

bird :: (Mochastic repr) =>
        UArray (Year, Day, Cell, Cell, Feature) Double ->
        UArray (Year, Day, Cell) Int ->
        repr (Measure (Repeat NFeature Real))
bird features observations =
  mapC (\() c -> normal 0 10 `bind` c) (pure ()) $ \params ->
  let g year = let f day from to i =
                     features ! (year, day, from, to, i)
                   o day cell =
                     observations ! (year, day, cell)
               in birdYear f o params
  in foldr bind_ (dirac (toNestedPair params)) (map g [1..nyear])

pSample :: Maybe (Repeat NFeature Double, LogFloat) -> IO ()
pSample Nothing = return ()
pSample (Just (params, logProb)) =
  print (toList params, logFromLogFloat logProb :: Double)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [featuresFile, observationsFile, _outputFile] -> do
      hPutStrLn stderr ("Reading " ++ featuresFile)
      features <- readFeatures featuresFile
      hPutStrLn stderr ("Reading " ++ observationsFile)
      observations <- readObservations observationsFile
      hPutStrLn stderr "Sampling"
      let m = bird features observations
      -- writeFile "/tmp/m" (show (runPrettyPrint m))
      let s = unSample m 1
      withSystemRandom (\g -> replicateM_ 2000 (s g >>= pSample))
    _ -> do
      progName <- getProgName
      hPutStrLn stderr ("Usage: " ++ progName ++ " \
        \<featuresFile> <observationsFile> <outputFile>")
      hPutStrLn stderr ("Example: " ++ progName ++ " \\\n\
        \\t\tinput/dataset1/onebird_features.csv \\\n\
        \\t\tinput/dataset1/onebird-observations.csv \\\n\
        \\t\toutput/dataset1/estimated-parameters.csv")
      exitFailure
