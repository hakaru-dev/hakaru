{-# LANGUAGE DataKinds,
             FlexibleContexts,
             GADTs,
             KindSignatures #-}

----------------------------------------------------------------
--                                                    2016.07.01
-- |
-- Module      :  Language.Hakaru.CodeGen.HOAS.Expression
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

module Language.Hakaru.CodeGen.HOAS.Expression
  ( -- math.h functions
    log1p
  , log
  , expm1
  , exp
  , sqrt

  -- memory operations
  , malloc
  , free

  , rand
  , sizeof

  , castE
  , condE

  , (^>)
  , (^<)
  , (^==)
  , (^||)
  , (^&&)
  , (^*)
  , (^/)
  , (^-)
  , (^+)

  , postInc

  , varE
  , memberE
  , (^!)

  , indirectE
  , addressE

  , stringE
  , stringVarE
  , nullaryE
  , unaryE
  , callFuncE
  , binaryOp
  , assignE
  ) where

import Language.Hakaru.Syntax.AST
import Language.Hakaru.Types.HClasses
import Language.Hakaru.CodeGen.AST

import Prelude hiding (log,exp,sqrt)

stringE :: String -> CExpr
stringE x = CConstant $ CStringConst x

unaryE :: String -> CExpr -> CExpr
unaryE s x = CCall (CVar (Ident s)) [x]

nullaryE :: String -> CExpr
nullaryE s = CCall (CVar (Ident s)) []

callFuncE :: CExpr -> [CExpr] -> CExpr
callFuncE nameE argsEs = CCall nameE argsEs

rand :: CExpr
rand = nullaryE "rand"

log1p,log,expm1,exp,sqrt,malloc,free,postInc
  :: CExpr -> CExpr
log1p   = unaryE "log1p"
log     = unaryE "log"
expm1   = unaryE "expm1"
exp     = unaryE "exp"
sqrt    = unaryE "sqrt"
malloc  = unaryE "malloc"
free    = unaryE "free"
postInc = \expr -> CUnary CPostIncOp expr

sizeof :: CDecl -> CExpr
sizeof d = CSizeofType d

stringVarE :: String -> CExpr
stringVarE s = CVar (Ident s)

varE :: Ident -> CExpr
varE x = CVar x

(^<),(^>),(^==),(^||),(^&&),(^*),(^/),(^-),(^+)
  :: CExpr -> CExpr -> CExpr
a ^< b  = CBinary CLeOp a b
a ^> b  = CBinary CGrOp a b
a ^== b = CBinary CEqOp a b
a ^|| b = CBinary CLorOp a b
a ^&& b = CBinary CAndOp a b
a ^* b  = CBinary CMulOp a b
a ^/ b  = CBinary CDivOp a b
a ^- b  = CBinary CSubOp a b
a ^+ b  = CBinary CAddOp a b

intE :: Integer -> CExpr
intE = CConstant $ CIntConst

floatE :: Float -> CExpr
floatE = CConstant $ CFloatConst

binaryOp :: NaryOp a -> CExpr -> CExpr -> CExpr
binaryOp (Sum HSemiring_Prob)  a b = CBinary CAddOp (exp a) (exp b)
binaryOp (Prod HSemiring_Prob) a b = CBinary CAddOp a b
binaryOp (Sum _)               a b = CBinary CAddOp a b
binaryOp (Prod _)              a b = CBinary CMulOp a b
-- vvv Operations on bools, keeping in mind that in Hakaru-C: 0 is true and 1 is false
binaryOp And                   a b = CUnary CNegOp (CBinary CEqOp  a b) -- still wrong
binaryOp Or                    a b = CBinary CAndOp a b                 -- still wrong
binaryOp Xor                   a b = CBinary CLorOp a b                 -- still wrong
binaryOp x _ _ = error $ "TODO: binaryOp " ++ show x


castE :: CDecl -> CExpr -> CExpr
castE d e = CCast d e

condE :: CExpr -> CExpr -> CExpr -> CExpr
condE cond thn els = CCond cond thn els

memberE :: CExpr -> Ident -> CExpr
memberE var ident = CMember var ident False

-- for assigning to pointers
indirectE :: CExpr -> CExpr
indirectE var = CUnary CIndOp var

-- for getting addresses of vars
addressE :: CExpr -> CExpr
addressE var = CUnary CAdrOp var

-- infix memberE
(^!) :: CExpr -> Ident -> CExpr
(^!) = memberE

assignE :: CExpr -> CExpr -> CExpr
assignE var expr = CAssign CAssignOp var expr
