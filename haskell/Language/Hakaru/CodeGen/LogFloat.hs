----------------------------------------------------------------
--                                                    2016.07.11
-- |
-- Module      :  Language.Hakaru.CodeGen.LogFloat
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  zsulliva@indiana.edu
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- An implementation of wren's logFloat library in the CodeGenMonad
--
----------------------------------------------------------------

module Language.Hakaru.CodeGen.LogFloat
  ( logFloat
  , infinity )
  where

import Language.Hakaru.CodeGen.CodeGenMonad
import Language.Hakaru.CodeGen.HOAS.Expression
import Language.Hakaru.CodeGen.HOAS.Statement
import Language.C.Syntax.AST

import Prelude hiding (isNaN)

logFloat :: CExpr -> CodeGen CExpr
logFloat expr = do guardNonNegative expr
                   return $ log1p expr


lfplus,lfprod,lfsub,lfdiv
  :: CExpr -> CExpr -> CodeGen CExpr
a `lfplus` b = undefined
a `lfprod` b = undefined
a `lfsub` b  = undefined
a `lfdiv` b  = undefined
----------------------------------------------------------------

guardNonNegative :: CExpr -> CodeGen ()
guardNonNegative x =
  putStat $ guardS ((intConstE 0 ^> x) ^|| isNaN x) exitS


guardIsANumber :: CExpr -> CodeGen ()
guardIsANumber x = putStat $ guardS (isNaN x) exitS

----------------------------------------------------------------

isFinite,isNaN :: CExpr -> CExpr
isFinite = unaryE "isfinite"
isNaN    = unaryE "isnan"

infinity :: CodeGen CExpr
infinity = do ident <- genIdent
              assign ident $ (floatConstE 1) ^/ (floatConstE 0)
              return (varE ident)

