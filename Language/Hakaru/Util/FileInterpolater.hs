-- TODO: [wrengr 2015.10.23] (a) remove this file entirely, or (b) move it somewhere more helpful. Also, if we keep it around, the module name should change to match the file name.

{-# LANGUAGE RankNTypes, NoMonomorphismRestriction #-}
{-# OPTIONS -W #-}

module Main where

import System.IO
import Text.ParserCombinators.Parsec
import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure)

data ControlMeas = CM { time1 :: Double, vel :: Double, steer :: Double }
data Sensor = S { time2 :: Double, lat :: Double, long :: Double, orient :: Double }
data Merged = M {cm :: ControlMeas, sens :: Sensor}

type Table1 = [ ControlMeas ]
type Table2 = [ Sensor ]
type MergedT = [ Merged ]

-- prev will be Nothing on startup
data Tracking a = Tr {prev :: Maybe a, curr :: a, rest :: [a]}

-- interpolate and merge 2 files
main :: IO ()
main = do
  args <- getArgs
  case args of
    [fileName1, fileName2] -> do
      handle1 <- openFile fileName1 ReadMode
      handle2 <- openFile fileName2 ReadMode
      contents1 <- hGetContents handle1
      contents2 <- hGetContents handle2
      let list1 = tail $ convertS (parseCSV contents1)
      let list2 = tail $ convertS (parseCSV contents2)
      let tableM = interpolation (constructTab1 list1) (constructTab2 list2)
      writeFile "output.csv" (unlines (convertTable tableM)) 
      putStrLn "Interpolated data written to output.csv"
    _ -> do
      progName <- getProgName
      hPutStrLn stderr ("Usage: " ++ progName ++ " <control filename> <gps filename>")
      hPutStrLn stderr ("Example: " ++ progName ++ " \"slam_control.csv\" \"slam_gps.csv\"")
      exitFailure      

-- parsec (CSV)
csvFile = endBy line eol
line = sepBy cell (char ',')
cell = many (noneOf ",\n")
eol = char '\n'

parseCSV :: String -> Either ParseError [[String]]
parseCSV input = parse csvFile "(unknown)" input

-- convert table to output format (CSV)
convertTable :: MergedT -> [String]
convertTable = map convertCSV

convertCSV :: Merged -> String
convertCSV m = show (time1 control) ++ "," ++ 
               show (vel control) ++ "," ++ 
               show (steer control) ++ "," ++ 
               show (lat sensors) ++ "," ++ 
               show (long sensors) ++ "," ++ 
               show (orient sensors)
    where control = cm m
          sensors = sens m

-- Perform Interpolation
interpolation :: Table1 -> Table2 -> MergedT
interpolation [] [] = []
interpolation [] _ = error "not enough data to interpolate"
interpolation _ [] = error "not enough data to interpolate"
interpolation (x1:xs) (y1:ys) =
  go (Tr Nothing x1 xs) (Tr Nothing y1 ys)

-- interpolation using current and previous tracking
go :: Tracking ControlMeas -> Tracking Sensor -> MergedT
go (Tr _ _ []) (Tr _ _ _) = []
go (Tr pr1 cur1 rst1) (Tr pr2 cur2 rst2) = 
  let t1 = time1 cur1
      t2 = time2 cur2 in
  case compare t1 t2 of
    LT -> M cur1 res : go (Tr (Just cur1) (head rst1) (tail rst1)) (Tr pr2 cur2 rst2)
          where
            S t2p latp longp orientp = maybe (S t1 0 0 0) id pr2
            S t2c latc longc orientc = cur2
            interp x y = ((x-y) / (t2c-t2p)) * (t1-t2p) + y
            res = S t1 (interp latc latp) (interp longc longp) (interp orientc orientp)
    EQ -> M cur1 cur2 : go (Tr (Just cur1) (head rst1) (tail rst1)) (Tr (Just cur2) (head rst2) (tail rst2))
    GT -> M res cur2 : if null rst2 then [] else go (Tr pr1 cur1 rst1) (Tr (Just cur2) (head rst2) (tail rst2))
          where
            CM t1p velp steerp = maybe (CM t2 0 0) id pr1
            CM t1c velc steerc = cur1
            interp x y = ((x-y) / (t1c-t1p)) * (t2-t1p) + y
            res = CM t2 (interp velc velp) (interp steerc steerp) 

-- helper functions
readD :: String -> Double
readD x = read x :: Double

convertS :: Either ParseError a -> a
convertS (Left _) = error "something went wrong in the parsing -- FIXME"
convertS (Right s) = s

constructTab1 :: [[String]] -> Table1
constructTab1 = map read3
  where 
    read3 :: [String] -> ControlMeas
    read3 (x : y : z : []) = CM (readD x) (readD y) (readD z)
    read3 _ = error "Table 1 should have exactly 3 entries per row"

constructTab2 :: [[String]] -> Table2
constructTab2 = map read4
  where
    read4 :: [String] -> Sensor
    read4 (x : y : z : w : []) = S (readD x) (readD y) (readD z) (readD w)
    read4 _ = error "Table 2 should have exactly 4 entries per row"
