{-# LANGUAGE OverloadedStrings, DataKinds #-}

module Tests.TypeCheck where

import Prelude hiding (unlines)

import qualified Language.Hakaru.Parser.AST as U
import qualified Language.Hakaru.Syntax.AST as T

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.HClasses
import Language.Hakaru.Syntax.Nat
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.TypeCheck
import Language.Hakaru.PrettyPrint

import Data.Text
import Test.HUnit

five :: U.AST a
five =  U.NaryOp_ (Some1 $ T.Sum HSemiring_Int)
        [ U.Value_ $ Some1 $ T.VInt 2
        , U.Value_ $ Some1 $ T.VInt 3
        ]

normal01 :: U.AST a
normal01 = U.MeasureOp_ (U.SealedOp T.Normal)
           [ U.Value_ $ Some1 $ T.VReal 0
           , U.Value_ $ Some1 $ T.VProb 1
           ]

inferType' :: U.AST a -> TypeCheckMonad (TypedAST TrivialABT)
inferType' = inferType

testTC :: U.AST a -> String
testTC a = case runTCM (inferType' a) of
             Left err -> err
             Right (TypedAST typ ast) -> show (typ, pretty ast)
