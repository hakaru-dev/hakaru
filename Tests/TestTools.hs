{-# LANGUAGE Rank2Types, ScopedTypeVariables, DeriveDataTypeable #-}
{-# OPTIONS -Wall #-}

module Tests.TestTools where

import Language.Hakaru.Syntax (Measure, Mochastic, Integrate, Lambda(lam), Order_)
import Language.Hakaru.Disintegrate (Disintegrate, Disintegration(Disintegration), disintegrations)
import Language.Hakaru.Expect (Expect(unExpect))
import Language.Hakaru.Maple (Maple, runMaple)
import Language.Hakaru.Simplify (simplify, Simplifiable, toMaple, SimplifyException(MapleException))
import Language.Hakaru.Any (Any(unAny))
import Language.Hakaru.PrettyPrint (PrettyPrint, runPrettyPrint, leftMode)
import Text.PrettyPrint (Doc)
import Data.Maybe (isJust)
import Data.List
import Data.Function (on)
import Data.Typeable (Typeable)
import Control.Exception

import Test.HUnit

newtype Result = Result Doc
result :: PrettyPrint a -> Result
result = Result . runPrettyPrint
instance Eq Result where Result a == Result b = leftMode a == leftMode b
instance Show Result where
  showsPrec 0 (Result a) = showChar '\n' . showsPrec 0 a
  showsPrec _ (Result a) =                 showsPrec 0 a

data TestException = TestSimplifyException String String String -- (hakaru, toMaple, fromMaple)
                     deriving Typeable
instance Exception TestException
instance Show TestException where
  show (TestSimplifyException prettyHakaru toM fromM) =
    "TestSimplifyException\n**Hakaru**\n" ++ prettyHakaru ++ "\n\n**To Maple**\n" ++ toM ++ "\n\n**From Maple**\n" ++ fromM

-- assert that we get a result and that no error is thrown
assertResult :: [a] -> Assertion
assertResult s = assertBool "no result" $ not $ null s

assertJust :: Maybe a -> Assertion
assertJust = assertBool "expected Just but got Nothing" . isJust

type Testee a =
  forall repr. (Mochastic repr, Integrate repr, Lambda repr) => repr a

-- Assert that a given Hakaru program roundtrips (aka simplifies) without error
testS :: (Simplifiable a) => Testee a -> Assertion
testS t = do
    p <- simplify t `catch` handleSimplify t
    let s = result (unAny p)
    assertResult (show s)

-- Assert that all the given Hakaru programs simplify to the given one
testSS :: (Simplifiable a) => [Expect Maple a] -> Testee a -> Assertion
testSS ts t' =
    mapM_ (\t -> do p <- simplify t --`catch` handleSimplify t
                    (assertEqual "testSS" `on` result) t' (unAny p))
          (t' : ts)

handleSimplify :: PrettyPrint a -> SimplifyException -> IO (Any a)
handleSimplify t (MapleException toMaple fromMaple) = 
  do let pp = show $ result t 
     throw $ TestSimplifyException pp toMaple fromMaple
handleSimplify _ e = throw e

testD :: (Simplifiable env, Simplifiable a, Simplifiable b, Order_ a) =>
         (Disintegrate env -> Disintegrate (Measure (a,b))) -> IO ()
testD f = do
    let ds = disintegrations f
    assertResult ds
    mapM_ (\(Disintegration d) -> testS (lam (\env -> lam (\a -> d env a)))) ds

toMapleD :: (Simplifiable env, Simplifiable a, Simplifiable b, Order_ a) =>
         (Disintegrate env -> Disintegrate (Measure (a,b))) -> IO ()
toMapleD f = do
    let ds = disintegrations f
    mapM_ (\(Disintegration d) -> (putStrLn.toMaple) 
                                  (lam (\env -> lam (\a -> d env a)))) ds

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
