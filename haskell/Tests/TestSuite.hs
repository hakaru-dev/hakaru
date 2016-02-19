-- module Tests.TestSuite(main) where

import System.Exit (exitFailure)

import qualified Tests.Parser       as P
import qualified Tests.TypeCheck    as TC
import qualified Tests.Simplify     as S
import qualified Tests.Disintegrate as D
import qualified Tests.Sample       as E

import Test.HUnit

-- master test suite

allTests :: Test
allTests = test
  [ TestLabel "Parser"       P.allTests
  , TestLabel "TypeCheck"    TC.allTests
  , TestLabel "Simplify"     S.allTests
  , TestLabel "Disintegrate" D.allTests
  , TestLabel "Evaluate"     E.allTests
  ]

main :: IO ()
main = do
    Counts _ _ e f <- runTestTT allTests
    if (e>0) || (f>0) then exitFailure else return ()
