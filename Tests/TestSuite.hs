-- module Tests.TestSuite(main) where

import System.Exit (exitFailure)

import qualified Tests.RoundTrip as RT
import qualified Tests.Syntax as SY
import qualified Tests.Vector as TV
import qualified Tests.Relationships as RE
import qualified Tests.Embed as E
import qualified Tests.Lazy as L

import Test.HUnit

-- master test suite

allTests :: Test
allTests = test
  [ RT.allTests
  , SY.allTests
  , RE.allTests
  , TV.allTests
  , E.allTests
  , L.important
  ]

main :: IO ()
main = do
    Counts _ _ e f <- runTestTT allTests
    if (e>0) || (f>0) then exitFailure else return ()
