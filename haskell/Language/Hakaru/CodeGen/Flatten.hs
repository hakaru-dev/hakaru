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
import Language.Hakaru.Types.Sing

import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Syntax.AST
import Language.C.Syntax.Constants

import Control.Monad

import           Data.Number.Natural
import           Data.Ratio
import           Data.Sequence (Seq)
import qualified Data.Foldable      as F
import qualified Data.Traversable   as T       

node :: NodeInfo
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
    (LNat x)  -> return $ constStat $ CIntConst (cInteger $ fromIntegral x) node
    (LInt x)  -> return $ constStat $ CIntConst (cInteger $ fromIntegral x) node
    (LReal x) -> return $ constStat $ CFloatConst (cFloat $ fromRational x) node
    (LProb x) -> let rat = fromNonNegativeRational x
                     x'  = (fromIntegral $ numerator rat)
                         / (fromIntegral $ denominator rat)
                 in do ident' <- genIdent
                       declare $ typeDeclaration undefined ident'
                       return (CExpr (Just (CCall (CVar (builtinIdent "log") node)
                                                  [CConst (CFloatConst (cFloat x') node)]
                                                  node))
                                     node)

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
flattenNAryOp op args =
  do ids <- T.forM args
                   (\abt -> do id' <- genIdent
                               declare $ typeDeclaration undefined id'
                               getIdent)
     F.foldr f unit ids
  where unit  = return $ constStat $ toCUnitOp op
        f a b = do ident <- genIdent
                   b'    <- b
                   declare $ typeDeclaration undefined ident
                   assign ident $ (cBinaryOp op) a b'
