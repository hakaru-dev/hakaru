{-# LANGUAGE Rank2Types #-}
{-# OPTIONS -Wall #-}

module Tests.TestTools where

import Language.Hakaru.Syntax (Mochastic, Integrate, Lambda)
import Language.Hakaru.Expect (Expect(unExpect))
import Language.Hakaru.Maple (Maple, runMaple)
import Language.Hakaru.Simplify (simplify, MapleableType)
import Language.Hakaru.Any (Any(unAny))
import Language.Hakaru.PrettyPrint (PrettyPrint, runPrettyPrint, leftMode)
import Text.PrettyPrint (Doc)
import Data.Maybe (isJust)
import Data.List
import Data.Typeable (Typeable)
import Data.Function (on)

import Test.HUnit

newtype Result = Result Doc
result :: PrettyPrint a -> Result
result = Result . runPrettyPrint
instance Eq Result where Result a == Result b = leftMode a == leftMode b
instance Show Result where
  showsPrec 0 (Result a) = showChar '\n' . showsPrec 0 a
  showsPrec _ (Result a) =                 showsPrec 0 a

-- assert that we get a result and that no error is thrown
assertResult :: [a] -> Assertion
assertResult s = assertBool "no result" $ not $ null s

assertJust :: Maybe a -> Assertion
assertJust = assertBool "expected Just but got Nothing" . isJust

type Testee a =
  forall repr. (Mochastic repr, Integrate repr, Lambda repr) => repr a

-- Assert that a given Hakaru program roundtrips (aka simplifies) without error
testS :: (MapleableType a, Typeable a) => Testee a -> IO ()
testS t = do
--    putStr "<<<<<"
--    print (result t)
    p <- simplify t
    let s = result (unAny p)
--    putStr ">>>>>"
--    print s
    assertResult (show s)

-- Assert that all the given Hakaru programs simplify to the given one
testSS :: (MapleableType a, Typeable a) => [Expect Maple a] -> Testee a -> IO ()
testSS ts t' =
    mapM_ (\t -> do p <- simplify t
                    (assertEqual "testSS" `on` result) t' (unAny p))
          (t' : ts)

testMaple :: Expect Maple a -> IO ()
testMaple t = assertResult $ runMaple (unExpect t) 0

testMapleEqual :: Expect Maple a -> Expect Maple a -> IO ()
testMapleEqual t1 t2 = do
    let r1 = rm t1
    let r2 = rm t2
    assertEqual "testMapleEqual: false" r1 r2
    where rm t = runMaple (unExpect t) 0

ignore :: a -> Assertion
ignore _ = assertFailure "ignored"  -- ignoring a test reports as a failure

-- Runs a single test from a list of tests given its index
runTestI :: Test -> Int -> IO Counts
runTestI (TestList ts) i = runTestTT $ ts !! i
runTestI (TestCase _) _ = error "expecting a TestList, but got a TestCase"
runTestI (TestLabel _ _) _ = error "expecting a TestList, but got a TestLabel"

hasLab :: String -> Test -> Bool
hasLab l (TestLabel lab _) = lab == l
hasLab _ _ = False

-- Runs a single test from a TestList given its label
runTestN :: Test -> String -> IO Counts
runTestN (TestList ts) l = 
  case find (hasLab l) ts of
    Just t -> runTestTT t
    Nothing -> error $ "no test with label " ++ l
runTestN (TestCase _) _ = error "expecting a TestList, but got a TestCase"
runTestN (TestLabel _ _) _ = error "expecting a TestList, but got a TestLabel"
