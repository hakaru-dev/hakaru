-- module Tests.TestSuite(main) where

import System.Exit (exitFailure)

import qualified Tests.Parser       as P
import qualified Tests.TypeCheck    as TC
import qualified Tests.Simplify     as S
import qualified Tests.Disintegrate as D

import Test.HUnit

-- master test suite

allTests :: Test
allTests = test
  [ P.allTests
  , TC.allTests
  , S.allTests
  , D.allTests
  ]

main :: IO ()
main = do
    Counts _ _ e f <- runTestTT allTests
    if (e>0) || (f>0) then exitFailure else return ()
