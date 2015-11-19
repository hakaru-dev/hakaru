{-# LANGUAGE OverloadedStrings, DataKinds #-}

module Tests.Pretty where

import           Language.Hakaru.Parser.Parser
import qualified Language.Hakaru.Parser.AST as U
import           Language.Hakaru.Parser.SymbolResolve
import           Language.Hakaru.PrettyConcrete

import           Language.Hakaru.Syntax.ABT
import qualified Language.Hakaru.Syntax.AST as T
import           Language.Hakaru.Syntax.TypeCheck

import Prelude hiding (unlines)

import Data.Text
import Text.PrettyPrint
import Test.HUnit
import Text.Parsec.Error
import Control.Monad.Trans.State.Strict (evalState)

letTest = unlines ["x = 2"
                  ,"y = 3"
                  ,"x"
                  ]

letTest2 = unlines ["x = y = 2"
                   ,"    y"
                   ,"x"
                   ]

defTest = unlines ["def foo(x nat) nat:"
                  ,"  x + 2"
                  ,"foo(3)"
                  ]

defTest2 = unlines ["def foo(x nat, y nat) nat:"
                   ,"  x + y"
                   ,"foo(2,3)"
                   ]

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
          
