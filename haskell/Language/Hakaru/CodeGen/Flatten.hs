{-# LANGUAGE DataKinds,
             ExistentialQuantification,
             FlexibleContexts,
             FlexibleInstances,
             GADTs,
             KindSignatures #-}

----------------------------------------------------------------
--                                                    2016.06.23
-- |
-- Module      :  Language.Hakaru.CodeGen.Flatten
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  zsulliva@indiana.edu
-- Stability   :  experimental
-- Portability :  GHC-only
--
--   Flatten takes Hakaru ABTs and C vars and returns a CStatement
-- assigning the var to the flattened ABT.
--
----------------------------------------------------------------


module Language.Hakaru.CodeGen.Flatten
  (flattenABT)
  where

import Language.Hakaru.CodeGen.CodeGenMonad
import Language.Hakaru.CodeGen.HOAS
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Types.Sing

import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Syntax.AST
import Language.C.Syntax.Constants

import           Data.Number.Natural
import           Data.Ratio
import qualified Data.Sequence      as S
import qualified Data.Foldable      as F
import qualified Data.Traversable   as T

node :: NodeInfo
node = undefNode

measureIdent :: Ident
measureIdent = builtinIdent "measure"

flattenABT :: ABT Term abt
           => abt '[] a
           -> CodeGen CExpr
flattenABT abt = caseVarSyn abt flattenVar flattenTerm


flattenLit :: Literal a -> CodeGen CExpr
flattenLit lit =
  case lit of
    (LNat x)  -> return $ CConst $ CIntConst (cInteger $ fromIntegral x) node
    (LInt x)  -> return $ CConst $ CIntConst (cInteger $ fromIntegral x) node
    (LReal x) -> return $ CConst $ CFloatConst (cFloat $ fromRational x) node
    (LProb x) -> let rat = fromNonNegativeRational x
                     x'  = (fromIntegral $ numerator rat)
                         / (fromIntegral $ denominator rat)
                 in do ident <- genIdent
                       declare $ typeDeclaration SProb ident
                       assign ident (CCall (CVar (builtinIdent "log") node)
                                           [CConst (CFloatConst (cFloat x') node)]
                                           node)
                       return $ CVar ident node


flattenVar :: Variable (a :: Hakaru) -> CodeGen CExpr
flattenVar v = do ident <- lookupIdent v
                  return $ CVar ident node

flattenTerm :: ABT Term abt => Term abt a -> CodeGen CExpr
flattenTerm (NaryOp_ t s)  = flattenNAryOp t s
flattenTerm (Literal_ x)   = flattenLit x
flattenTerm (Empty_ _)     = error "TODO: flattenTerm Empty"
flattenTerm (Datum_ d)     = flattenDatum d
flattenTerm (Case_ _ _)    = error "TODO: flattenTerm Case"
flattenTerm (Array_ _ _)   = error "TODO: flattenTerm Array"
flattenTerm (x :$ ys)      = flattenSCon x ys
flattenTerm (Reject_ _)    = error "TODO: flattenTerm Reject"
flattenTerm (Superpose_ _) = error "TODO: flattenTerm Superpose"


----------------------------------------------------------------
flattenNAryOp :: ABT Term abt
              => NaryOp a
              -> S.Seq (abt '[] a)
              -> CodeGen CExpr
flattenNAryOp op args =
  let typ = opType op in
  do ids <- T.forM args
                   (\abt -> do expr <- flattenABT abt
                               case expr of
                                 (CVar i _) -> return i
                                 _          -> do ident <- genIdent
                                                  declare $ typeDeclaration typ ident
                                                  assign ident expr
                                                  return ident)
     let expr = F.foldr (binaryOp op)
                        (var_c (S.index ids 0))
                        (fmap var_c (S.drop 1 ids))
     return expr

opType :: forall (a :: Hakaru). NaryOp a -> Sing a
-- opType And                   = SNat
opType (Sum HSemiring_Nat)   = SNat
opType (Sum HSemiring_Int)   = SInt
opType (Sum HSemiring_Prob)  = SProb
opType (Sum HSemiring_Real)  = SReal
opType (Prod HSemiring_Nat)  = SNat
opType (Prod HSemiring_Int)  = SInt
opType (Prod HSemiring_Prob) = SProb
opType (Prod HSemiring_Real) = SReal
opType x = error $ "TODO: opType " ++ show x
----------------------------------------------------------------



flattenSCon :: (ABT Term abt)
            => SCon args a
            -> SArgs abt args
            -> CodeGen CExpr
flattenSCon Let_            =
  \(expr :* body :* End) ->
    do expr' <- flattenABT expr
       caseBind body $ \v@(Variable _ _ typ) body'->
         do ident <- createIdent v
            declare $ typeDeclaration typ ident
            assign ident expr'
            flattenABT body'
flattenSCon (MeasureOp_  m) = \es -> flattenMeasureOp m es
flattenSCon Dirac           =
  \(e :* End) ->
    do e' <- flattenABT e
       assign measureIdent e'
       return e'
flattenSCon MBind           =
  \(e1 :* e2 :* End) ->
    do e1' <- flattenABT e1
       caseBind e2 $ \v@(Variable _ _ typ) e2'->
         do ident <- createIdent v
            declare $ typeDeclaration typ ident
            assign ident e1'
            assign measureIdent e1'
            flattenABT e2'
flattenSCon _               = \_ -> error "TODO: flattenSCon"
----------------------------------------------------------------

flattenMeasureOp :: ( ABT Term abt
                    , typs ~ UnLCs args
                    , args ~ LCs typs)
                 => MeasureOp typs a
                 -> SArgs abt args
                 -> CodeGen CExpr
flattenMeasureOp = error $ "TODO: flattenMeasureOp"
----------------------------------------------------------------

flattenDatum :: (ABT Term abt)
             => Datum (abt '[]) (HData' a)
             -> CodeGen CExpr
flattenDatum d = do i <- genIdent
                    return $ var_c i
     --error $ "TODO: flattenDatum"
