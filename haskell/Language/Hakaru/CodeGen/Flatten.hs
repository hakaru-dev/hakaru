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


module Language.Hakaru.CodeGen.Flatten where

import Language.Hakaru.CodeGen.CodeGenMonad
import Language.Hakaru.CodeGen.HOAS
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Types.Sing

import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Syntax.AST
import Language.C.Syntax.Constants

import Control.Monad

import           Data.Number.Natural
import           Data.Ratio
import           Data.Sequence (Seq, (|>))
import qualified Data.Foldable      as F
import qualified Data.Traversable   as T

node :: NodeInfo
node = undefNode

flattenABT :: ABT Term abt
           => Sing (a :: Hakaru)
           -> abt '[] a
           -> CodeGen CStat
flattenABT typ abt = caseVarSyn abt flattenVar flattenTerm


flattenLit :: Literal a -> CodeGen CStat
flattenLit lit =
  case lit of
    (LNat x)  -> return $ constStat $ CIntConst (cInteger $ fromIntegral x) node
    (LInt x)  -> return $ constStat $ CIntConst (cInteger $ fromIntegral x) node
    (LReal x) -> return $ constStat $ CFloatConst (cFloat $ fromRational x) node
    (LProb x) -> let rat = fromNonNegativeRational x
                     x'  = (fromIntegral $ numerator rat)
                         / (fromIntegral $ denominator rat)
                 in do ident' <- genIdent
                       declare $ typeDeclaration SProb ident'
                       let astat = assign ident' (CExpr (Just (CCall (CVar (builtinIdent "log") node)
                                                                     [CConst (CFloatConst (cFloat x') node)]
                                                                     node))
                                                        node)
                       return $ sumStat [astat,callIdent ident']


flattenVar :: Variable (a :: Hakaru) -> CodeGen CStat
flattenVar = undefined

flattenTerm :: ABT Term abt => Term abt a -> CodeGen CStat
flattenTerm (NaryOp_ t s)  = flattenNAryOp t s
flattenTerm (Literal_ x)   = flattenLit x
flattenTerm (Empty_ x)     = error "TODO: flattenTerm Empty"
flattenTerm (Datum_ x)     = error "TODO: flattenTerm Datum"
flattenTerm (Case_ x y)    = error "TODO: flattenTerm Case"
flattenTerm (Array_ x y)   = error "TODO: flattenTerm Array"
flattenTerm (x :$ y)       = error "TODO: flattenTerm :$"
flattenTerm (Reject_ x)    = error "TODO: flattenTerm Reject"
flattenTerm (Superpose_ x) = error "TODO: flattenTerm Superpose"

flattenNAryOp :: ABT Term abt
              => NaryOp a
              -> Seq (abt '[] a)
              -> CodeGen CStat
flattenNAryOp op args =
  let typ = opType op in
  do fids <- T.forM args
                   (\abt -> do id' <- genIdent
                               declare $ typeDeclaration typ id'
                               stmt <- flattenABT typ abt
                               let stmt' = assign id' stmt
                               return (id',stmt'))
     let stmt = CExpr (Just $ F.foldr (\(a,_) b -> binaryOp op a b)
                                      (CConst $ toCUnitOp op)
                                      fids)
                      node
     let stmts = fmap snd fids
     return $ sumStat (stmts |> stmt)

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
