module Language.Hakaru.CodeGen.HOAS.Statement
  ( ifS
  , guardS
  , exitS
  , printS
  ) where

import Language.C.Syntax.AST
import Language.C.Data.Node

import Language.Hakaru.CodeGen.HOAS.Expression

node :: NodeInfo
node = undefNode

ifS :: CExpr -> CStat -> CStat -> CStat
ifS e thn els = CIf e thn (Just els) node

guardS :: CExpr -> CStat -> CStat
guardS e thn = CIf e thn Nothing node

exitS :: CStat
exitS = CReturn (Just $ intConstE 0) node

printS :: String -> CStat
printS s = CExpr (Just $ printE s) node
