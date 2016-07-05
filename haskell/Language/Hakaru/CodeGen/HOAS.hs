{-# LANGUAGE DataKinds,
             GADTs,
             KindSignatures #-}

----------------------------------------------------------------
--                                                    2016.07.01
-- |
-- Module      :  Language.Hakaru.CodeGen.HOAS
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

module Language.Hakaru.CodeGen.HOAS
  ( typeDeclaration
  , toCUnitOp
  , constStat
  , var_c
  , sumStat
  , binaryOp ) where

import Language.Hakaru.Syntax.AST
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Types.Sing

import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Syntax.Constants
import Language.C.Syntax.AST

import qualified Data.Foldable as F

node :: NodeInfo
node = undefNode

constStat :: CConstant NodeInfo -> CStat
constStat x = CExpr (Just $ CConst x) node

sumStat :: F.Foldable m => m CStat -> CStat
sumStat stmts = CExpr (Just (CStatExpr (CCompound [] stmts' node) node)) node
  where stmts' = F.foldr ((:).CBlockStmt) [] stmts

typeDeclaration :: Sing (a :: Hakaru) -> Ident -> CDecl
typeDeclaration typ ident =
  CDecl [CTypeSpec (toCType typ)]
        [(Just $ CDeclr (Just ident) [] Nothing [] node,Nothing,Nothing)]
        node

toCType :: Sing (a :: Hakaru) -> CTypeSpecifier NodeInfo
toCType SInt         = CIntType undefNode
toCType SNat         = CIntType undefNode
toCType SProb        = CDoubleType undefNode
toCType SReal        = CDoubleType undefNode
toCType (SMeasure x) = toCType x
toCType x            = error $ "TODO: toCType: " ++ show x


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
toCUnitOp _ = error "TODO: unitOp"
-- -- toCU- unitOp (Max  HOrd_Prob)      = VProb 0
-- -- toCU- unitOp (Max  HOrd_Real)      = VReal LF.negativeInfinity
-- -- toCU- unitOp (Min  HOrd_Prob)      = VProb (LF.logFloat LF.infinity)
-- -- toCU- unitOp (Min  HOrd_Real)      = VReal LF.infinity

binaryOp :: NaryOp a -> CExpr -> CExpr -> CExpr
binaryOp (Sum HSemiring_Prob)  a b = log_c (CBinary CAddOp
                                                    (exp_c a)
                                                    (exp_c b)
                                                    node)
binaryOp (Prod HSemiring_Prob) a b = CBinary CMulOp a b node
binaryOp _                     a b = CBinary CAddOp a b node

log_c :: CExpr -> CExpr
log_c x = (CCall (CVar (builtinIdent "log") node)
                 [x]
                 node)

exp_c :: CExpr -> CExpr
exp_c x = (CCall (CVar (builtinIdent "exp") node)
                 [x]
                 node)

var_c :: Ident -> CExpr
var_c x = CVar x node
