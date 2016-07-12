{-# LANGUAGE DataKinds,
             FlexibleContexts,
             GADTs,
             KindSignatures #-}

----------------------------------------------------------------
--                                                    2016.07.01
-- |
-- Module      :  Language.Hakaru.CodeGen.Expression
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  zsulliva@indiana.edu
-- Stability   :  experimental
-- Portability :  GHC-only
--
--   HOAS provides a higher order abstract syntax for building
-- C ASTs
--
----------------------------------------------------------------

module Language.Hakaru.CodeGen.HOAS.Expression
  ( -- math.h functions
    log1p
  , exp1m

  , constExpr
  , intConstE
  , floatConstE
  , (^>)
  , (^<)

  , varE
  , unaryE
  , printE
  , toCUnitOp
  , binaryOp
  ) where

import Language.Hakaru.Syntax.AST
import Language.Hakaru.Types.HClasses

import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Syntax.Constants
import Language.C.Syntax.AST

node :: NodeInfo
node = undefNode

constExpr :: CConstant NodeInfo -> CExpr
constExpr = CConst

stringE :: String -> CExpr
stringE x = constExpr $ CStrConst (cString x) node


unaryE :: String -> CExpr -> CExpr
unaryE s x = CCall (CVar (builtinIdent s) node) [x] node

printE :: String -> CExpr
printE s = unaryE "printf" (stringE s)

log1p,exp1m :: CExpr -> CExpr
log1p = unaryE "log1p"
exp1m = unaryE "exp1m"

varE :: Ident -> CExpr
varE x = CVar x node

(^<) :: CExpr -> CExpr -> CExpr
a ^< b = CBinary CLeOp a b node

(^>) :: CExpr -> CExpr -> CExpr
a ^> b = CBinary CGrOp a b node

intConstE :: Integer -> CExpr
intConstE x = constExpr $ CIntConst (cInteger x) node

floatConstE :: Float -> CExpr
floatConstE x = constExpr $ CFloatConst (cFloat x) node

toCUnitOp :: NaryOp a -> CConstant NodeInfo
toCUnitOp And                   = CIntConst (cInteger 1) node
toCUnitOp (Sum HSemiring_Nat)   = CIntConst (cInteger 0) node
toCUnitOp (Sum HSemiring_Int)   = CIntConst (cInteger 0) node
toCUnitOp (Sum HSemiring_Prob)  = CFloatConst (cFloat 0) node
toCUnitOp (Sum HSemiring_Real)  = CFloatConst (cFloat 0) node
toCUnitOp (Prod HSemiring_Nat)  = CIntConst (cInteger 1) node
toCUnitOp (Prod HSemiring_Int)  = CIntConst (cInteger 1) node
toCUnitOp (Prod HSemiring_Prob) = CFloatConst (cFloat 1) node
toCUnitOp (Prod HSemiring_Real) = CFloatConst (cFloat 1) node
toCUnitOp x = error $ "TODO: unitOp {" ++ show x ++ "}"

binaryOp :: NaryOp a -> CExpr -> CExpr -> CExpr
binaryOp (Sum HSemiring_Prob)  a b = log1p (CBinary CAddOp
                                                    (exp1m a)
                                                    (exp1m b)
                                                    node)
binaryOp (Prod HSemiring_Prob) a b = CBinary CMulOp a b node
binaryOp _                     a b = CBinary CAddOp a b node
