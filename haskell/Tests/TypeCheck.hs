{-# LANGUAGE GADTs
           , OverloadedStrings
           , DataKinds
           , FlexibleContexts
           #-}

module Tests.TypeCheck where

import Prelude hiding (unlines)

import qualified Language.Hakaru.Parser.AST as U
import qualified Language.Hakaru.Syntax.AST as T

import Language.Hakaru.Syntax.AST.Eq()

import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.TypeCheck
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing

import Data.Number.Nat

import Data.Sequence
import Data.Text
import Test.HUnit
import Tests.TestTools

five :: Text
five = "2 + 3"

fiveU :: U.AST
fiveU =
    U.NaryOp_ U.Sum'
        [ U.Literal_ $ Some1 $ T.LNat 2
        , U.Literal_ $ Some1 $ T.LNat 3
        ]

fiveT :: TrivialABT T.Term '[] 'HNat
fiveT =
    syn . T.NaryOp_ (T.Sum HSemiring_Nat) $ fromList
        [ syn $ T.Literal_ $ T.LNat 2
        , syn $ T.Literal_ $ T.LNat 3
        ]

normal01 :: U.AST
normal01 =
    U.MeasureOp_ (U.SealedOp T.Normal)
        [ U.Literal_ $ Some1 $ T.LReal 0
        , U.Literal_ $ Some1 $ T.LProb 1
        ]

normal01T :: TrivialABT T.Term '[] ('HMeasure 'HReal)
normal01T =
    syn (T.MeasureOp_ T.Normal
        T.:$ (syn $ T.Literal_ $ T.LReal 0)
        T.:* (syn $ T.Literal_ $ T.LProb 1)
        T.:* T.End)

xname :: U.Name
xname =  U.Name (unsafeNat 0) "x"

normalb :: U.AST
normalb =
    U.MBind_ xname
        normal01
        (U.MeasureOp_ (U.SealedOp T.Normal)
            [ U.Var_ xname
            , U.Literal_ $ Some1 $ T.LProb 1
            ])


inferType' :: U.AST -> TypeCheckMonad (TypedAST (TrivialABT T.Term))
inferType' = inferType

testTC :: Sing b -> U.AST -> TrivialABT T.Term '[] b -> Assertion
testTC typ uast tast =
    case runTCM (inferType' uast) StrictMode of
    Left _err                 -> assertFailure (show tast)
    Right (TypedAST _typ ast) ->
        case jmEq1 _typ typ of
        Just Refl -> assertEqual "" tast ast
        Nothing   -> assertFailure
            (show ast ++ " does not have same type as " ++ show tast)

testConcreteTC :: Sing b -> Text -> TrivialABT T.Term '[] b -> Assertion
testConcreteTC typ s ast =
    testWithConcrete' s StrictMode
         (\(TypedAST _typ tast) ->
              case jmEq1 _typ typ of
                Just Refl -> assertEqual "" tast ast
                Nothing   -> assertFailure
                  (show ast ++ " does not have same type as " ++ show tast))


allTests :: Test
allTests = test
    [ testTC SNat fiveU fiveT
    , testTC (SMeasure SReal) normal01 normal01T
    , testConcreteTC SNat five fiveT
    ]
