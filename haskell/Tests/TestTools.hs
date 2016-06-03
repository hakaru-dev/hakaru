{-# LANGUAGE DeriveDataTypeable
           , DataKinds
           , FlexibleContexts #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Tests.TestTools where

import Language.Hakaru.Parser.Parser
import Language.Hakaru.Parser.SymbolResolve (resolveAST)
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.TypeCheck
import Language.Hakaru.Syntax.AST.Eq (alphaEq)
import Language.Hakaru.Pretty.Concrete
import Language.Hakaru.Simplify
import Language.Hakaru.Syntax.AST.Eq()

import Data.Maybe (isJust)
import Data.List
import qualified Data.Text as T
import Data.Typeable (Typeable)
import Control.Exception
import Control.Monad

import Test.HUnit

data TestException = TestSimplifyException String SomeException
    deriving Typeable
instance Exception TestException
instance Show TestException where
    show (TestSimplifyException prettyHakaru e) =
        show e ++ "\nwhile simplifying Hakaru:\n" ++ prettyHakaru

-- assert that we get a result and that no error is thrown
assertResult :: [a] -> Assertion
assertResult s = assertBool "no result" $ not $ null s

assertJust :: Maybe a -> Assertion
assertJust = assertBool "expected Just but got Nothing" . isJust

handleException :: String -> SomeException -> IO a
handleException t e = throw (TestSimplifyException t e)

testS
    :: (ABT Term abt)
    => String
    -> abt '[] a
    -> Assertion
testS p x = do
    _ <- simplify x `catch` handleException (p ++ ": simplify failed")
    return ()

testStriv 
    :: TrivialABT Term '[] a
    -> Assertion
testStriv = testS ""

-- Assert that all the given Hakaru programs simplify to the given one
testSS 
    :: (ABT Term abt)
    => String
    -> [(abt '[] a)] 
    -> abt '[] a 
    -> Assertion
testSS nm ts t' = 
     mapM_ (\t -> do p <- simplify t 
                     assertAlphaEq nm p t')
           (t':ts)

testSStriv 
    :: [(TrivialABT Term '[] a)] 
    -> TrivialABT Term '[] a 
    -> Assertion
testSStriv = testSS ""

assertAlphaEq ::
    (ABT Term abt) 
    => String
    -> abt '[] a
    -> abt '[] a
    -> Assertion
assertAlphaEq preface a b =
   unless (alphaEq a b) (assertFailure msg)
 where msg = concat [ p
                    , "expected:\n"
                    , show (pretty b)
                    , "\nbut got:\n"
                    , show (pretty a)
                    ]
       p = if null preface then "" else preface ++ "\n"

testWithConcrete ::
    (ABT Term abt)
    => T.Text
    -> TypeCheckMode
    -> (TypedAST abt -> Assertion)
    -> Assertion
testWithConcrete s mode k =
    case parseHakaru s of
      Left  err  -> assertFailure (show err)
      Right past ->
          let m = inferType (resolveAST past) in
          case runTCM m mode of
            Left err   -> assertFailure err
            Right tast -> k tast

testWithConcrete'
    :: T.Text
    -> TypeCheckMode
    -> (TypedAST (TrivialABT Term) -> Assertion)
    -> Assertion
testWithConcrete' = testWithConcrete

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
