{-# LANGUAGE DataKinds,
             FlexibleContexts,
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
  ( -- tools for building C types
    typeDeclaration
  , arrayDeclaration
  , structDeclaration

  , toCUnitOp
  , constStat
  , cvar
  , sumStat
  , binaryOp
  ) where

import Language.Hakaru.Syntax.ABT       
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum       
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

cvar :: Ident -> CExpr
cvar x = CVar x node

----------------------------------------------------------------
-- | buildType function do the work of describing how the Hakaru
-- type will be stored in memory. Arrays needed their own
-- declaration function for their arity
buildType :: Sing (a :: Hakaru) -> CTypeSpec
buildType SInt             = CIntType undefNode
buildType SNat             = CIntType undefNode
buildType SProb            = CDoubleType undefNode
buildType SReal            = CDoubleType undefNode
buildType (SMeasure x)     = buildType x
buildType (SData con func) = buildData con func
buildType (SArray x)       = buildType x
buildType x = error $ "TODO: buildCType: " ++ show x

buildData :: Sing (a :: HakaruCon)
         -> Sing (b :: [[HakaruFun]])
         -> CTypeSpec
buildData (STyCon s)   = \funk -> CSUType (undefined s funk) node
buildData (STyApp a b) = \funk -> undefined a b funk


typeDeclaration :: Sing (a :: Hakaru) -> Ident -> CDecl
typeDeclaration typ ident =
  CDecl [CTypeSpec $ buildType typ]
        [(Just $ CDeclr (Just ident) [] Nothing [] node,Nothing,Nothing)]
        node

arrayDeclaration :: Sing (a :: Hakaru)
                 -> CExpr -- ^ cexpr representing arity (could lead to bugs?)
                 -> Ident
                 -> CDecl
arrayDeclaration typ n ident =
  CDecl [CTypeSpec $ buildType typ]
        [( Just $ CDeclr (Just ident)
                         [CArrDeclr [] (CArrSize False n) node]
                         Nothing
                         []
                         node
         , Nothing
         , Nothing)]
        node

structDeclaration :: (ABT Term abt)
                  => DatumCode (Code t) (abt '[]) (HData' t)
                  -> Ident
                  -> CDecl
structDeclaration dcode ident =
  case dcode of
    (Inr _) -> struct
    (Inl _) -> struct
  where struct = CDecl [CTypeSpec $ CSUType (CStruct CStructTag Nothing (Just []) [] node) node]
                       [( Just $ CDeclr (Just ident)
                                        []
                                        Nothing
                                        []
                                        node
                        , Nothing
                        , Nothing)]
                       node

        
