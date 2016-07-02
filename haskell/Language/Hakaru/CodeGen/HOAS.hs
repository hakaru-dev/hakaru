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
  ( typeDeclaration ) where

import Language.Hakaru.Syntax.AST
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.HClasses       
import Language.Hakaru.Types.Sing

import Language.C.Data.Ident
import Language.C.Data.Node       
import Language.C.Syntax.AST

node = undefNode       

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
toCNaryOpType And = CAndOp
toCNaryOpType (Sum _)               = CAddOp
toCNaryOpType (Prod HSemiring_Prob) = CAddOp   -- product of exp is addition
toCNaryOpType (Prod _)              = CMulOp
-- toCNaryOpType (Min _)  = undefined
-- toCNaryOpType (Max _)  = undefined
toCNaryOpType _ = error "TODO: flattenOp"

-- toCUnitOp :: NaryOp a -> CConstant NodeInfo
-- toCUnitOp And                   = CIntConst (cInteger 1) node
-- toCUnitOp (Sum HSemiring_Nat)   = CIntConst (cInteger 0) node
-- toCUnitOp (Sum HSemiring_Int)   = CIntConst (cInteger 0) node
-- -- toCU- unitOp (Sum HSemiring_Prob)  = VProb 0
-- -- toCU- unitOp (Sum HSemiring_Real)  = VReal 0
-- toCUnitOp (Prod HSemiring_Nat)  = CIntConst (cInteger 1) node
-- toCUnitOp (Prod HSemiring_Int)  = CIntConst (cInteger 1) node
-- toCUnitOp _ = error "TODO: unitOp"
-- -- toCU- unitOp (Prod HSemiring_Prob) = VProb 1
-- -- toCU- unitOp (Prod HSemiring_Real) = VReal 1
-- -- toCU- unitOp (Max  HOrd_Prob)      = VProb 0
-- -- toCU- unitOp (Max  HOrd_Real)      = VReal LF.negativeInfinity
-- -- toCU- unitOp (Min  HOrd_Prob)      = VProb (LF.logFloat LF.infinity)
-- -- toCU- unitOp (Min  HOrd_Real)      = VReal LF.infinity
