{-# LANGUAGE NoMonomorphismRestriction #-}

module Main where

import Data.List
import Data.Dynamic
import System.Directory
import System.IO
import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure)
import Text.Parsec

import qualified Data.Map.Strict as M
import qualified Data.Number.LogFloat as LF

import Mixture (Prob, empty, point, Mixture(..), mnull)
import Types (Cond(..), CSampler)
import InterpreterDynamic
import Lambda (dbl)

-- particle filtering
onlineFiltering
    :: (Ord a, Show a)
    => (Mixture a -> Double -> Double -> Double -> Measure a)
    -> Mixture a
    -> [[Cond]]
    -> Int
    -> Double
    -> Double
    -> Double
    -> IO (Mixture a)
onlineFiltering _ prior [] _ _ _ _ = return prior
onlineFiltering prog prior (cond:conds) n x y t = do 
    let curTime = convertTime (head cond)
    let timeElapsed = curTime - t
    posterior <- sample n (prog prior x y timeElapsed) (tail cond)
    let mixtureList = M.toAscList (unMixture posterior)
    let outputList = foldl (\acc (k, v) -> [(k, LF.fromLogFloat(v)::Double)] ++ acc) [] mixtureList
    let (k, w) = head $ sortMix outputList
    let output = removeBrackets (if null mixtureList then "" else (show (curTime, k, w) ++ "\n"))
    appendFile "slam_out_data.csv" output
    onlineFiltering prog posterior conds n x y curTime

-- quad rotor model (kalman filter)
prog_quadCopter
    :: Mixture (Double, Double, Double, Double)
    -> Double
    -> Double
    -> Double
    -> Measure (Double, Double, Double, Double)
prog_quadCopter prevMix initX initY timeElapsed = do
    velocity <- conditioned (uniform (dbl 0) (dbl 5))
    steerAngle <- conditioned (uniform (dbl (-2)) (dbl 2))
    (x0, y0, dirX, dirY) <- if mnull prevMix then return (initX, initY, 0, 1)
    else unconditioned (categorical (M.toList(unMixture prevMix)))
    let orientX = dirX * cos (-1 * steerAngle) - dirY * sin (-1 * steerAngle)
    let orientY = dirY * cos (-1 * steerAngle) + dirX * sin (-1 * steerAngle)
    x1 <- unconditioned (normal (x0 + orientX * velocity*timeElapsed) (dbl 7))
    y1 <- unconditioned (normal (y0 + orientY * velocity*timeElapsed) (dbl 7))
    _ <- conditioned (normal (x1 :: Double) (dbl 1))
    _ <- conditioned (normal (y1 :: Double) (dbl 1))
    return (x1, y1, orientX, orientY)

-- helper functions
compareMix (_, v1) (_, v2) = if v1 < v2 then GT else LT

sortMix = sortBy compareMix

csvFile = endBy line eol
line = sepBy cell (char ',')
cell = many (noneOf ",\n")
eol = char '\n'

parseCSV :: String -> Either ParseError [[String]]
parseCSV input = parse csvFile "(unknown)" input

removeBrackets :: String -> String
removeBrackets st = [c | c <- st, c `notElem` ['(', ')']]

convertTime :: Cond -> Double
convertTime (Lebesgue t) =
    case fromDynamic t of
    Just t -> t
    Nothing -> error "Not conditioned data"
convertTime (Discrete t) =
    case fromDynamic t of
    Just t -> t
    Nothing -> error "Not conditioned data"
convertTime (Unconditioned) = 0.0

convertC :: Either ParseError [[String]] -> [[Cond]]
convertC (Left _) = [[]]
convertC (Right s) =
    map (map $ \x1 -> Lebesgue (toDyn (read x1 :: Double))) s

convertS :: Either ParseError [[String]] -> [[String]]
convertS (Left _) = [[]]
convertS (Right s) = s

convertD :: [[String]] -> [[Double]]
convertD str = map (\x0 -> map (\x1 -> read x1 :: Double) x0) str

convertTable :: [[String]] -> [String]
convertTable table =
    foldl (\acc x -> acc ++ [convertCSV x (head x)]) [] table 

convertCSV :: [String] -> String -> String
convertCSV list firstElement =
    foldl (\acc x ->
        if (x == firstElement)
        then acc ++ x  
        else acc ++ "," ++ x)
        "" list 

mergeGPS :: [Double] -> [Double] -> [[Double]] -> Int -> [[String]] -> [[String]]
mergeGPS _ _ _ 0 list = list 
mergeGPS time_g time_r results n list = 
    mergeGPS time_g time_r results (n - 1) $
    if (time_r !! n) `elem` time_g
    then [show (time_r !! n), show (results !! n !! 1), show (results !! n !! 2)] : list
    else list

-- main program
main :: IO ()
main = do 
    args <- getArgs
    writeFile "slam_out_landmarks.csv" ""
    case args of 
        [numParticles, x, y] -> do
            handle <- openFile "output.csv" ReadMode
            contents <- hGetContents handle
            let cond = convertS (parseCSV contents)
            print ((show (length cond)) ++ " row(s)")
            print ((show (length (head cond))) ++ " column(s)")
            let condInput = convertC (parseCSV contents)
            -- ignore orientation column
            let condInputFix = transpose (init (transpose condInput))
            exist <- doesFileExist "slam_out_data.csv"
            if exist then removeFile "slam_out_data.csv" else return ()
            output <- onlineFiltering prog_quadCopter empty condInputFix 
                  (read numParticles :: Int) 
	              (read x :: Double) (read y :: Double) 0.0		 
            putStrLn (show output)  	
        _ -> do
            progName <- getProgName
            hPutStrLn stderr ("Usage: " ++ progName ++ 
                " <number of particles> <initial latitude> <initial longitude>")
            hPutStrLn stderr ("Example: " ++ progName ++ " 30 0 -6")
            exitFailure
    gps_contents <- readFile "slam_gps.csv"
    let gps = tail (convertD (convertS (parseCSV gps_contents)))
    let gps_c = head (transpose gps) 
    results_contents <- readFile "slam_out_data.csv"
    let results = convertD (convertS (parseCSV results_contents))
    let results_c = head (transpose results)
    let slam_output = mergeGPS gps_c results_c results ((length results) - 1) [[]]
    writeFile "slam_out_path.csv" (show (head (head gps)) ++ "," ++
        show ((head gps) !! 1) ++ "," ++ show ((head gps) !! 2) ++ "\n")
    appendFile "slam_out_path.csv" (unlines (convertTable slam_output))
    putStrLn "Output written to slam_out_path.csv"

