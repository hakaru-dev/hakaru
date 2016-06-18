{-# LANGUAGE DataKinds,
             FlexibleContexts,
             FlexibleInstances,
             GADTs #-}

module Language.Hakaru.CodeGen.Flatten where

import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Types.HClasses

import Language.C.Data.Node
import Language.C.Data.Position
import Language.C.Syntax.AST
import Language.C.Syntax.Constants

import Data.List.NonEmpty
import Data.Number.Natural
import Data.Ratio
import Data.Sequence (Seq)

flattenABT :: ABT Term abt
           => abt xs a
           -> NonEmpty CStat
flattenABT = \e -> case viewABT e of
               (Syn x)    -> flattenTerm x
               (Var x)    -> undefined
               (Bind x y) -> undefined

flattenTerm :: ABT Term abt
            => Term abt a
            -> NonEmpty CStat
flattenTerm (NaryOp_ t s)  = return $ nAryOp_c t s
flattenTerm (Literal_ x)   = return $ literal_c   x
flattenTerm (Empty_ x)     = return $ empty_c     x
flattenTerm (Datum_ x)     = return $ datum_c     x
flattenTerm (Case_ x y)    = return $ case_c      x y
flattenTerm (Array_ x y)   = return $ array_c     x y
flattenTerm (x :$ y)       = return $ cons_c      x y
flattenTerm (Reject_ x)    = return $ reject_c    x
flattenTerm (Superpose_ x) = return $ superpose_c x


flattenSCon :: ABT Term abt
            => SCon args a
            -> SArgs abt args
            -> NonEmpty CStat
flattenSCon Lam_            = undefined
flattenSCon App_            = undefined
flattenSCon Let_            = undefined
flattenSCon (CoerceTo_ t)   = undefined
flattenSCon (UnsafeFrom_ t) = undefined
flattenSCon (PrimOp_ t)     = undefined
flattenSCon (ArrayOp_ t)    = undefined
flattenSCon (MeasureOp_ t)  = undefined
flattenSCon Dirac           = undefined
flattenSCon MBind           = undefined
flattenSCon Plate           = undefined
flattenSCon Chain           = undefined
flattenSCon Integrate       = undefined
flattenSCon Summate         = undefined
flattenSCon Expect          = undefined
flattenSCon Observe         = undefined

-- instance Flattenable (Variable x) where
--   flatten = undefined


nAryOp_c :: NaryOp a -> Seq b -> CStat
nAryOp_c And      = undefined
nAryOp_c Or       = undefined
nAryOp_c Xor      = undefined
nAryOp_c Iff      = undefined
nAryOp_c (Min o)  = undefined
nAryOp_c (Max o)  = undefined
nAryOp_c (Sum _)  = undefined --fmap flatten
nAryOp_c (Prod s) = undefined


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
literal_c = let n = undefNode in
  \lit -> case lit of
            (LNat x)  -> CExpr (Just (CConst (CIntConst (cInteger $ fromIntegral x) n))) n
            (LInt x)  -> CExpr (Just (CConst (CIntConst (cInteger $ fromIntegral x) n))) n
            (LProb x) -> let rat = fromNonNegativeRational x
                             x'  = (fromIntegral $ numerator rat) / (fromIntegral $ denominator rat)
                         in CExpr (Just (CConst (CFloatConst (cFloat x') n))) n -- losing precision
            (LReal x) -> CExpr (Just (CConst (CFloatConst (cFloat $ fromRational x) n))) n

-- literal (LProb x) = CExpr (Just (CConst (CIntConst (cInteger $ fromIntegral x) undefNode))) undefNode
-- literal (LReal x) = CExpr (Just (CConst (CIntConst (cInteger $ fromIntegral x) undefNode))) undefNode
