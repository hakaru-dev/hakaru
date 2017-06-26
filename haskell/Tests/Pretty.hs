{-# LANGUAGE OverloadedStrings
           , DataKinds
           , GADTs
           , TypeOperators 
           , FlexibleContexts #-}

module Tests.Pretty where

import           Language.Hakaru.Command (parseAndInfer)
import           Language.Hakaru.Pretty.Concrete
import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.Prelude
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Types.Sing
import           Language.Hakaru.Types.DataKind
import qualified Language.Hakaru.Parser.AST as U
import qualified Language.Hakaru.Syntax.AST as T
import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Types.Sing


import           Tests.TestTools 
import           Data.Text
import           Text.PrettyPrint
import           Test.HUnit
import           Text.Parsec.Error
import           Control.Monad.Trans.State.Strict (evalState)

import           Prelude ((.), ($), asTypeOf, String, FilePath, Show(..), (++), Bool(..), concat 
                         ,Either(..), Maybe(..))
import qualified Prelude 

allTests :: Test
allTests = test
    [ "basic let"  ~: testPretty letTest 
    , "nested let" ~: testPretty letTest2
    , "basic fn"   ~: testPretty defTest 
    , "nested fn"  ~: testPretty defTest2
    , "fn in case" ~: testPretty' caseFn  
    , "fn literal in case" ~: testPretty' caseFn2 
    , "hof"        ~: testPretty' hof
    ]

letTest = unlines ["x = 2"
                  ,"y = 3"
                  ,"x"
                  ]

letTest2 = unlines ["x = y = 2"
                   ,"    y"
                   ,"x"
                   ]

defTest = unlines ["foo = fn x nat:"
                  ,"  x + 2"
                  ,"foo(3)"
                  ]

defTest2 = unlines ["foo = fn x nat: fn y nat:"
                   ,"  x + y"
                   ,"foo(2,3)"
                   ]

caseFn :: (ABT T.Term abt) => abt '[] 'HProb
caseFn = 
  pair (lam $ \x -> x) (lam $ \x -> x)
     `unpair` \a b -> (a `app` prob_ 1) + (b `app` prob_ 2)

caseFn2 :: (ABT T.Term abt, b ~ HProb) => abt '[] (b :-> (b :-> (b :-> b)))
caseFn2 = 
    lam $ \x0 ->
    let_ (lam $ \x1 ->
        (lam $ \x2 ->
         (pair (lam $ \x -> x) (prob_ 12)) `unpair` \x4 x5 -> x4 `app` (x0 + x1 + x2 + x5))) $ \x -> x 

hof :: (ABT T.Term abt, a ~ HProb) => abt '[] (a :-> a :-> a :-> (a :-> (a :-> HPair a ((a :-> a) :-> a))) :-> a)
hof = 
  lam $ \x0 -> lam $ \x1 -> lam $ \x3 -> lam $ \x4 -> (
     x4 `app` x0
        `app` x1 `unpair` \x2 x3 ->
        x3 `app` (lam $ \_ -> prob_ 1))

-- Tests things are parsed and prettyprinted nearly the same
testPretty :: Text -> Assertion 
testPretty t =
  case parseAndInfer t of 
    Left err                -> assertFailure ("Program failed to parse\n" ++ unpack err)
    Right (TypedAST ty ast) -> 
      case parseAndInfer $ pack $ show $ pretty ast of 
        Left err                  -> assertFailure ("Pretty printed program failed to parse\n" ++ unpack err)
        Right (TypedAST ty' ast') -> 
          Prelude.maybe 
              (assertFailure $ mismatchMessage (prettyType 10) "Pretty printed programs has different type!" ty ty')
              (\Refl -> assertAlphaEq "" ast ast') 
              (jmEq1 ty ty')

testPretty' :: TrivialABT T.Term '[] a -> Assertion 
testPretty' = testPretty . pack . show . pretty 
