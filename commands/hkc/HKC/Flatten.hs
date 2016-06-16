{-# LANGUAGE DataKinds,
             FlexibleContexts,
             FlexibleInstances,
             GADTs #-}

module HKC.Flatten where

import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Types.HClasses

import Language.C.Data.Node
import Language.C.Data.Position
import Language.C.Syntax.AST
import Language.C.Syntax.Constants

import Data.List.NonEmpty

class Flattenable a where
  flatten :: a -> NonEmpty CStat

instance ABT Term abt => Flattenable (abt xs a) where
  flatten e = case viewABT e of
                (Syn x)    -> flatten x
                (Var x)    -> undefined
                (Bind x v) -> undefined

instance Flattenable (Term abt a) where
  flatten (NaryOp_ x y)  = return $ nAryOp_c    x y
  flatten (Literal_ x)   = return $ literal_c   x
  flatten (Empty_ x)     = return $ empty_c     x
  flatten (Datum_ x)     = return $ datum_c     x
  flatten (Case_ x y)    = return $ case_c      x y
  flatten (Array_ x y)   = return $ array_c     x y
  flatten (x :$ y)       = return $ cons_c      x y
  flatten (Reject_ x)    = return $ reject_c    x
  flatten (Superpose_ x) = return $ superpose_c x

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
