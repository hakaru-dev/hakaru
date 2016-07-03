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
import Language.C.Data.Position
import Language.C.Syntax.AST
import Language.C.Syntax.Constants

import           Data.Number.Nat (fromNat)
import           Data.Number.Natural
import           Data.Ratio
import           Data.Sequence (Seq)
import qualified Data.Foldable      as F

node = undefNode

flattenABT :: ABT Term abt
           => Sing (a :: Hakaru)
           -> abt '[] a
           -> CodeGen CStat
flattenABT typ abt = do ident <- getIdent
                        declare (typeDeclaration typ ident)
                        cstat <- caseVarSyn abt flattenVar flattenTerm
                        assign ident cstat

flattenLit :: Literal a -> CodeGen CStat
flattenLit lit =
  case lit of
    (LNat x)  -> return $ constExpr $ CIntConst (cInteger $ fromIntegral x)
    (LInt x)  -> return $ constExpr $ CIntConst (cInteger $ fromIntegral x)
    (LReal x) -> return $ constExpr $ CFloatConst (cFloat $ fromRational x)
    (LProb x) -> let rat = fromNonNegativeRational x
                     x'  = (fromIntegral $ numerator rat)
                         / (fromIntegral $ denominator rat)
                 in do ident' <- genIdent
                       declare $ typeDeclaration undefined ident'
                       return (CExpr (Just (CCall (CVar (builtinIdent "log") node)
                                                  [CConst (CFloatConst (cFloat x') node)]
                                                  node))
                                     node)
  where constExpr x = CExpr (Just $ CConst $ x node) node

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
              -> Seq (abt '[] b)
              -> CodeGen CStat
flattenNAryOp (Prod HSemiring_Prob) seq = undefined
flattenNAryOp (Sum  HSemiring_Prob) seq = undefined
flattenNAryOp op                    seq = undefined
