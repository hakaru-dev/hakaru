{-# LANGUAGE OverloadedStrings, DataKinds, GADTs #-}

module Tests.Hakaru where

import qualified Language.Hakaru.Parser.AST as U
import Language.Hakaru.Parser.Parser
import Language.Hakaru.Parser.SymbolResolve


import qualified Language.Hakaru.Syntax.AST as T
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.HClasses
import Language.Hakaru.Syntax.Nat
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.TypeCheck
import Language.Hakaru.PrettyPrint
import Language.Hakaru.Sample

import Prelude hiding (unlines)
import Data.Text
import Text.PrettyPrint
import qualified System.Random.MWC as MWC

five, normal01, normalb :: Text

five = "2 + 3"
normal01 = "normal(-0.0,1.0)"

normalb  = unlines [ "x <~ normal(-2.0,1.0)"
                   , "normal(x, 1.0)"
                   ]

pToa :: U.AST' Text -> U.AST a
pToa = makeAST . normAST . (symbolResolution primTable)

inferType' :: U.AST a -> TypeCheckMonad (TypedAST TrivialABT)
inferType' = inferType

testTC :: U.AST a -> String
testTC a = case runTCM (inferType' a) of
             Left err -> err
             Right (TypedAST typ ast) -> show (typ, pretty ast)

testHakaru :: Text -> MWC.GenIO ->
              IO (String, String, (Maybe (Sample IO 'HReal)))
testHakaru a g = case parseHakaru a of
                 Left err -> error (show err)
                 Right past ->
                     let m = inferType' (pToa past) in
                     case runTCM m of
                       Left err -> error err
                       Right (TypedAST typ@(SMeasure SReal) ast) -> do
                           Just (s, _) <- unS (runSample ast) 1 g
                           return (show typ, show $ pretty ast, Just s)
