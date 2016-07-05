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
  ( assign
  , typeDeclaration
  , toCUnitOp
  , constStat
  , callIdent
  , sumStat
  , binaryOp ) where

import Language.Hakaru.CodeGen.CodeGenMonad
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

assign :: Ident -> CStat -> CStat
assign var cstat =
  CExpr (Just (CAssign CAssignOp
                       (CVar var node)
                       (CStatExpr (CCompound [] [CBlockStmt cstat] node) node)
                       node))
        node

callIdent :: Ident -> CStat
callIdent ident = CExpr (Just (CVar ident node)) node

constStat :: CConstant NodeInfo -> CStat
constStat x = CExpr (Just $ CConst x) node

sumStat :: Foldable m => m CStat -> CStat
sumStat stmts = CExpr (Just (CStatExpr (CCompound [] stmts' node) node)) node
  where stmts' = F.foldr ((:).CBlockStmt) [] stmts

typeDeclaration :: Sing (a :: Hakaru) -> Ident -> CDecl
typeDeclaration typ ident =
  CDecl [CTypeSpec (toCType typ)]
        [(Just $ CDeclr (Just ident) [] Nothing [] node,Nothing,Nothing)]
        node

toCType :: Sing (a :: Hakaru) -> CTypeSpecifier NodeInfo
toCType SInt       = CIntType undefNode
toCType SNat       = CIntType undefNode
toCType SProb      = CDoubleType undefNode
toCType SReal      = CDoubleType undefNode
toCType _          = error "TODO: toCType"

toCNaryOpType :: NaryOp a -> CBinaryOp
toCNaryOpType And                   = CAndOp
toCNaryOpType (Sum _)               = CAddOp
toCNaryOpType (Prod HSemiring_Prob) = CAddOp   -- product of exp is addition
toCNaryOpType (Prod _)              = CMulOp
-- toCNaryOpType (Min _)  = undefined
-- toCNaryOpType (Max _)  = undefined
toCNaryOpType _ = error "TODO: flattenOp"


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

binaryOp :: NaryOp a -> Ident -> CExpr -> CExpr
binaryOp op a b = CBinary CAddOp (CVar a node) b node
