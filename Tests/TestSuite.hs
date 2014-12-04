module Tests.TestSuite where

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
    runTestTT allTests
    putStrLn "done"
