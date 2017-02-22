module Tests.TestSuiteTasty where

import System.Exit (exitFailure)
import System.Environment (lookupEnv)

import qualified Tests.Parser       as P
import qualified Tests.TypeCheck    as TC
import qualified Tests.Simplify     as S
import qualified Tests.Disintegrate as D
import qualified Tests.Sample       as E
import qualified Tests.RoundTrip    as RT

import Test.HUnit

--  Tasty 
import Test.Tasty               
import Test.Tasty.HUnit.Adapter     ( hUnitTestToTestTree    )
import Test.Tasty.Runners.Html      ( htmlRunner )
import Test.Tasty.Ingredients.Rerun ( rerunningTests )
import Test.Tasty.Ingredients.Basic ( consoleTestReporter, listingTests )

-- master test suite

ignored :: Assertion
ignored = putStrLn "Warning: maple tests will be ignored"

simplifyTests :: Test -> Maybe String -> Test
simplifyTests t env =
  case env of
    Just _  -> t
    Nothing -> test ignored

allTests :: Maybe String -> TestTree
allTests env = 
  testGroup "hakaru" $
  hUnitTestToTestTree $
  test
  [ TestLabel "Parser"       P.allTests
  , TestLabel "TypeCheck"    TC.allTests
  , TestLabel "Simplify"     (simplifyTests S.allTests env)
  , TestLabel "Disintegrate" D.allTests
  , TestLabel "Evaluate"     E.allTests
  , TestLabel "RoundTrip"    (simplifyTests RT.allTests env)
  ]

hakaruRecipe = 
  [ rerunningTests [ htmlRunner, consoleTestReporter ], listingTests ]

main = (allTests <$> lookupEnv "LOCAL_MAPLE") >>= defaultMainWithIngredients hakaruRecipe
