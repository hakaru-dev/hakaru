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
five =  U.NaryOp_ U.Sum'
        [ U.Literal_ $ Some1 $ T.LInt 2
        , U.Literal_ $ Some1 $ T.LInt 3
        ]

normal01 :: U.AST a
normal01 = U.MeasureOp_ (U.SealedOp T.Normal)
           [ U.Literal_ $ Some1 $ T.LReal 0
           , U.Literal_ $ Some1 $ T.LProb 1
           ]

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

testTC :: U.AST a -> String
testTC a = case runTCM (inferType' a) StrictMode of
             Left err -> err
             Right (TypedAST typ ast) -> show (typ, pretty ast)
