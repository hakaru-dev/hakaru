{-# LANGUAGE DeriveDataTypeable
           , DataKinds
           , RankNTypes
           , GADTs
           , PolyKinds
           , ScopedTypeVariables
           , FlexibleContexts #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Tests.TestTools where

import Language.Hakaru.Types.Sing
import Language.Hakaru.Parser.Parser (parseHakaru)
import Language.Hakaru.Parser.SymbolResolve (resolveAST)
import Language.Hakaru.Command (parseAndInferWithMode)
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.TypeCheck
import Language.Hakaru.Syntax.AST.Eq (alphaEq)
import Language.Hakaru.Syntax.IClasses (TypeEq(..), jmEq1)
import Language.Hakaru.Pretty.Concrete
import Language.Hakaru.Simplify
import Language.Hakaru.Syntax.AST.Eq()
import Text.PrettyPrint (Doc)

import Data.Maybe (isJust)
import Data.List
import qualified Data.Text    as T
import qualified Data.Text.Utf8 as IO
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
   unless (alphaEq a b) (assertFailure $ mismatchMessage pretty preface a b)

mismatchMessage :: forall (k :: q -> *) . (forall a . k a -> Doc) -> String -> forall a b . k a -> k b -> String 
mismatchMessage k preface a b = msg 
 where msg = concat [ p
                    , "expected:\n"
                    , show (k b)
                    , "\nbut got:\n"
                    , show (k a)
                    ]
       p = if null preface then "" else preface ++ "\n"

testWithConcrete ::
    (ABT Term abt)
    => T.Text
    -> TypeCheckMode
    -> (forall a. Sing a -> abt '[] a -> Assertion)
    -> Assertion
testWithConcrete s mode k =
  either (assertFailure . T.unpack) (\(TypedAST typ ast) -> k typ ast) $
  parseAndInferWithMode s mode

-- Like testWithConcrete, but for many programs 
testWithConcreteMany 
  :: forall abt. (ABT Term abt) 
  => T.Text 
  -> [T.Text]
  -> TypeCheckMode 
  -> (forall a . Sing a -> [abt '[] a] ->  abt '[] a -> Assertion) 
  -> Assertion 
testWithConcreteMany t ts mode k = 
  case ts of 
    []       -> testWithConcrete t mode $ \ty ast -> k ty [] ast 
    (t0:ts') -> 
      testWithConcrete t0 mode $ \ty0 (ast0 :: abt '[] x0) -> 
      testWithConcreteMany t ts' mode $ \ty1 asts (ast1 :: abt '[] x1) -> 
        case jmEq1 ty0 ty1 of 
          Just Refl -> k ty0 (ast0:asts) ast1 
          Nothing   -> assertFailure $ concat
                         [ "Files don't have same type (" 
                         , T.unpack t0, " :: ", show ty0, ", "
                         , T.unpack t , " :: ", show ty1 ]

testWithConcrete'
    :: T.Text
    -> TypeCheckMode
    -> (forall a. Sing a -> TrivialABT Term '[] a -> Assertion)
    -> Assertion
testWithConcrete' = testWithConcrete

testWithConcreteMany'
  :: T.Text 
  -> [T.Text] 
  -> TypeCheckMode 
  -> (forall a . Sing a 
        -> [TrivialABT Term '[] a] 
        -> TrivialABT Term '[] a 
        -> Assertion) 
  -> Assertion 
testWithConcreteMany' = testWithConcreteMany

-- Like testSStriv but for many concrete files
testConcreteFilesMany
    :: [FilePath] 
    -> FilePath
    -> Assertion
testConcreteFilesMany fs f = 
  mapM IO.readFile (f:fs) >>= \(t:ts) -> 
  testWithConcreteMany' t ts LaxMode $ \_ -> testSStriv

-- Like testSStriv but for two concrete files
testConcreteFiles
    :: FilePath
    -> FilePath
    -> Assertion
testConcreteFiles f1 f2 = testConcreteFilesMany [f1] f2 

-- Like testStriv but for a concrete file. 
testConcreteFile :: FilePath -> Assertion
testConcreteFile f = IO.readFile f >>= \t -> testWithConcrete' t LaxMode $ \_ -> testStriv

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
