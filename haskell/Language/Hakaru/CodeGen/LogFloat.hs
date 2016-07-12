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
  ( logFloat )
  where

import Language.Hakaru.CodeGen.CodeGenMonad
import Language.Hakaru.CodeGen.HOAS.Expression
import Language.Hakaru.CodeGen.HOAS.Statement
import Language.C.Syntax.AST

logFloat :: CExpr -> CodeGen CExpr
logFloat expr = do guardNonNegative expr
                   return $ log1p expr

----------------------------------------------------------------

guardNonNegative :: CExpr -> CodeGen ()
guardNonNegative x = putStat $ guardS (intConstE 0 ^> x) exitS


guardIsANumber :: CExpr -> CodeGen ()
guardIsANumber x = putStat $ guardS (unaryE "isnan" x) exitS
