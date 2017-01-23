-- module Tests.TestSuite(main) where

import System.Exit (exitFailure)
import System.Environment (lookupEnv)

import qualified Tests.ASTTransforms as TR
import qualified Tests.Parser        as P
import qualified Tests.TypeCheck     as TC
import qualified Tests.Simplify      as S
import qualified Tests.Disintegrate  as D
import qualified Tests.Sample        as E
import qualified Tests.RoundTrip     as RT

import Test.HUnit

-- master test suite

ignored :: Assertion
ignored = putStrLn "Warning: maple tests will be ignored"

simplifyTests :: Test -> Maybe String -> Test
simplifyTests t env =
  case env of
    Just _  -> t
    Nothing -> test ignored

allTests :: Maybe String -> Test
allTests env = test
  [ TestLabel "Parser"       P.allTests
  , TestLabel "TypeCheck"    TC.allTests
  , TestLabel "Simplify"     (simplifyTests S.allTests env)
  , TestLabel "Disintegrate" D.allTests
  , TestLabel "Evaluate"     E.allTests
  , TestLabel "RoundTrip"    (simplifyTests RT.allTests env)
  , TestLabel "ASTTransforms" TR.allTests
  ]

main :: IO ()
main  = do
    env <- lookupEnv "LOCAL_MAPLE"
    Counts _ _ e f <- runTestTT (allTests env)
    if (e>0) || (f>0) then exitFailure else return ()
