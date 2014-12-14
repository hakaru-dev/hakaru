-- module Tests.TestSuite(main) where

import qualified Tests.RoundTrip as RT
import qualified Tests.Syntax as SY

import Test.HUnit

-- master test suite

allTests :: Test
allTests = test [
    RT.allTests,
    SY.allTests
    ]

main :: IO ()
main = do
    c <- runTestTT allTests
    putStrLn $ showCounts c
