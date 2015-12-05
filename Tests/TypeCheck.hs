{-# LANGUAGE GADTs
           , OverloadedStrings
           , DataKinds
           , FlexibleContexts
           #-}

module Tests.TypeCheck where

import Prelude hiding (unlines)

import qualified Language.Hakaru.Parser.AST as U
import qualified Language.Hakaru.Syntax.AST as T

import Language.Hakaru.Syntax.AST.Eq

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.HClasses
import Language.Hakaru.Syntax.Nat
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.TypeCheck
import Language.Hakaru.PrettyPrint

import Data.Text
import Data.Sequence
import Test.HUnit

five :: U.AST a
five =  U.NaryOp_ U.Sum'
        [ U.Literal_ $ Some1 $ T.LInt 2
        , U.Literal_ $ Some1 $ T.LInt 3
        ]

fiveT :: TrivialABT T.AST '[] 'HInt
fiveT = syn (T.NaryOp_ (T.Sum HSemiring_Int) $ fromList
             [ syn $ T.Literal_ $ T.LInt 2
             , syn $ T.Literal_ $ T.LInt 3
             ])

normal01 :: U.AST a
normal01 = U.MeasureOp_ (U.SealedOp T.Normal)
           [ U.Literal_ $ Some1 $ T.LReal 0
           , U.Literal_ $ Some1 $ T.LProb 1
           ]

normal01T :: TrivialABT T.AST '[] ('HMeasure 'HReal)
normal01T = syn (T.MeasureOp_ T.Normal
                 T.:$ (syn $ T.Literal_ $ T.LReal 0)
                 T.:* (syn $ T.Literal_ $ T.LProb 1)
                 T.:* T.End)

xname :: U.Name
xname =  U.Name (unsafeNat 0) "x"

normalb :: U.AST a
normalb = U.MBind_ xname
           normal01
           (U.MeasureOp_ (U.SealedOp T.Normal)
                 [ U.Var_ xname
                 , U.Literal_ $ Some1 $ T.LProb 1
                 ])


inferType' :: U.AST a -> TypeCheckMonad (TypedAST (TrivialABT T.AST))
inferType' = inferType

testTC :: U.AST a -> TrivialABT T.AST '[] b -> Assertion
testTC uast tast =
       case runTCM (inferType' uast) StrictMode of
             Left err                 -> assertFailure (show tast)
             Right (TypedAST typ ast) ->
                  case jmEq1 ast tast of
                    Just Refl -> assertEqual "" ast tast
                    Nothing   -> assertFailure (show ast ++
                                                " does not have same type as " ++
                                                show tast
                                               )

allTests :: Test
allTests = test
   [ testTC five fiveT
   , testTC normal01 normal01T
   ]
