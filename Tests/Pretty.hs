{-# LANGUAGE OverloadedStrings, DataKinds #-}

module Tests.Pretty where

import           Language.Hakaru.Parser.Parser
import qualified Language.Hakaru.Parser.AST as U
import           Language.Hakaru.Parser.SymbolResolve
import           Language.Hakaru.Parser.Pretty

import           Language.Hakaru.Syntax.ABT
import qualified Language.Hakaru.Syntax.AST as T
import           Language.Hakaru.Syntax.TypeCheck

import Data.Text
import Text.PrettyPrint
import Test.HUnit
import Text.Parsec.Error
import Control.Monad.Trans.State.Strict (evalState)

pToa :: U.AST' Text -> U.AST a
pToa ast = makeAST $ normAST $ evalState (symbolResolution primTable ast) 0

inferType' :: U.AST a -> TypeCheckMonad (TypedAST (TrivialABT T.AST))
inferType' = inferType

-- Tests things are parsed and prettyprinted nearly the same
testPretty :: Text -> Doc
testPretty t =
    case parseHakaru t of
      Left  err  -> error (show err)
      Right past ->
          let m = inferType' (pToa past) in
          case runTCM m LaxMode of
            Left  err  -> error (show err)
            Right (TypedAST _ ast) -> pretty ast
          
