{-# LANGUAGE DataKinds,
             FlexibleContexts,
             GADTs #-}

module HKC.Flatten where

import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Types.HClasses

import Language.C.Data.Node
import Language.C.Data.Position
import Language.C.Syntax.AST
import Language.C.Syntax.Constants

flatten :: ABT Term abt => abt xs a -> CStat
flatten e =
  let n = undefNode in
  case viewABT e of
    (Syn x)     -> flattenSyn x
    (Var x)     -> undefined
    (Bind x v)  -> undefined

flattenSyn :: Term abt a -> CStat
flattenSyn (NaryOp_ x y)  = nAryOp_c    x y
flattenSyn (Literal_ x)   = literal_c   x
flattenSyn (Empty_ x)     = empty_c     x
flattenSyn (Datum_ x)     = datum_c     x
flattenSyn (Case_ x y)    = case_c      x y
flattenSyn (Array_ x y)   = array_c     x y
flattenSyn (x :$ y)       = cons_c      x y
flattenSyn (Reject_ x)    = reject_c    x
flattenSyn (Superpose_ x) = superpose_c x

nAryOp_c :: a -> b -> CStat
nAryOp_c = undefined

empty_c :: a -> CStat
empty_c = undefined

datum_c :: a -> CStat
datum_c = undefined

case_c :: a -> b -> CStat
case_c = undefined

array_c :: a -> b -> CStat
array_c = undefined

cons_c :: a -> b -> CStat
cons_c = undefined

superpose_c :: a -> CStat
superpose_c = undefined

reject_c :: a -> CStat
reject_c = undefined

-- | Types of literals are 'HNat, 'HInt, 'HProb, 'HReal
literal_c :: Literal a -> CStat
literal_c (LNat x)  = CExpr (Just (CConst (CIntConst (cInteger $ fromIntegral x) undefNode))) undefNode
literal_c (LInt x)  = CExpr (Just (CConst (CIntConst (cInteger $ fromIntegral x) undefNode))) undefNode
-- literal (LProb x) = CExpr (Just (CConst (CIntConst (cInteger $ fromIntegral x) undefNode))) undefNode
-- literal (LReal x) = CExpr (Just (CConst (CIntConst (cInteger $ fromIntegral x) undefNode))) undefNode
