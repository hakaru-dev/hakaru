module Main(main, justRelationships) where

import System.Exit (exitFailure)
import System.Environment (lookupEnv)

import qualified Tests.ASTTransforms as TR
import qualified Tests.Parser        as P
import qualified Tests.Pretty        as Pr
import qualified Tests.TypeCheck     as TC
import qualified Tests.Simplify      as S
import qualified Tests.Disintegrate  as D
import qualified Tests.Sample        as E
import qualified Tests.RoundTrip     as RT
import qualified Tests.Relationships as REL

import Test.HUnit

-- master test suite

ignored :: Assertion
ignored = putStrLn "Warning: maple tests will be ignored"

simplifyTests :: Test -> Maybe String -> Test
simplifyTests t env =
  case env of
    Just _  -> t
    Nothing -> test ignored

allTests, relationshipsTests :: Maybe String -> Test
allTests env = test $
  [ TestLabel "Parser"       P.allTests
  , TestLabel "Pretty"       Pr.allTests
  , TestLabel "TypeCheck"    TC.allTests
  , TestLabel "Simplify"     (simplifyTests S.allTests env)
  , TestLabel "Disintegrate" D.allTests
  , TestLabel "Evaluate"     E.allTests
  , TestLabel "RoundTrip"    (simplifyTests RT.allTests env)
  , TestLabel "ASTTransforms" TR.allTests
  ]
relationshipsTests env =
  TestLabel "Relationships" (simplifyTests REL.allTests env)

main, justRelationships :: IO ()
main = mainWith allTests (fmap Just . runTestTT)

justRelationships = mainWith relationshipsTests (fmap Just . runTestTT)

mainWith :: (Maybe String -> Test) -> (Test -> IO (Maybe Counts)) -> IO ()
mainWith mkTests run = do
    env <- lookupEnv "LOCAL_MAPLE"
    run (mkTests env) >>=
      maybe (return ()) (\(Counts _ _ e f) -> if (e>0) || (f>0) then exitFailure else return ())
