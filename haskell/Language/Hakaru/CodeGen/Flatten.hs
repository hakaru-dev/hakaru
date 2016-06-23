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

import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Types.DataKind

import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Data.Position
import Language.C.Syntax.AST
import Language.C.Syntax.Constants

import           Data.Number.Nat (fromNat)
import           Data.Number.Natural
import           Data.Ratio
import           Data.Sequence (Seq)
import qualified Data.IntMap        as IM
import qualified Data.Foldable      as F

node = undefNode

-- | flattenABT takes a Hakaru ABT and a C Var, and returns a
--   C Statement that assigns a flattened ABT to the var
flattenABT :: ABT Term abt
           => Ident
           -> abt '[] a
           -> (CStat, Ident)
flattenABT var expr =
   (CExpr (Just $ CAssign CAssignOp
                          (CVar var node)
                          (CStatExpr (CCompound [] [CBlockStmt (caseVarSyn expr flattenVar flattenTerm)] node)
                                     node)
                          node)
          node, var)

flattenVar :: Variable (a :: Hakaru) -> CStat
flattenVar = error "TODO: flattenVar"

flattenTerm :: ABT Term abt
            => Term abt a
            -> CStat
flattenTerm (NaryOp_ t s)  = flattenNAryOp t s
flattenTerm (Literal_ x)   = flattenLiteral x
flattenTerm (Empty_ x)     = empty_c     x
flattenTerm (Datum_ x)     = datum_c     x
flattenTerm (Case_ x y)    = case_c      x y
flattenTerm (Array_ x y)   = array_c     x y
flattenTerm (x :$ y)       = cons_c      x y
flattenTerm (Reject_ x)    = reject_c    x
flattenTerm (Superpose_ x) = superpose_c x


flattenNAryOp :: ABT Term abt
              => NaryOp a
              -> Seq (abt '[] b)
              -> CStat
flattenNAryOp op args = 
  let flattenedArgs = F.foldr (\a c -> flattenABT (builtinIdent "foo") a : c) [] args
      flattenedOp   = F.foldr (\x y -> CBinary (flattenOp op) x y node)
                              (CConst (unitOp op))
                              (fmap (\a -> CVar (snd a) node) flattenedArgs)
  in  CCompound [] (fmap CBlockStmt (fmap fst flattenedArgs ++ [CExpr (Just flattenedOp) node])) node


flattenOp :: NaryOp a -> CBinaryOp
flattenOp (Sum HSemiring_Nat) = CAddOp
flattenOp (Sum HSemiring_Int) = CAddOp
flattenOp _ = error "TODO: flattenOp"

unitOp   :: NaryOp a -> CConstant NodeInfo
unitOp    (Sum HSemiring_Nat) = CIntConst (cInteger 0) node
unitOp    (Sum HSemiring_Int) = CIntConst (cInteger 0) node

-- identityElement And                   = VDatum dTrue
-- identityElement (Sum HSemiring_Nat)   = VNat  0
-- identityElement (Sum HSemiring_Int)   = VInt  0
-- identityElement (Sum HSemiring_Prob)  = VProb 0
-- identityElement (Sum HSemiring_Real)  = VReal 0
-- identityElement (Prod HSemiring_Nat)  = VNat  1
-- identityElement (Prod HSemiring_Int)  = VInt  1
-- identityElement (Prod HSemiring_Prob) = VProb 1
-- identityElement (Prod HSemiring_Real) = VReal 1
-- identityElement (Max  HOrd_Prob)      = VProb 0
-- identityElement (Max  HOrd_Real)      = VReal LF.negativeInfinity
-- identityElement (Min  HOrd_Prob)      = VProb (LF.logFloat LF.infinity)
-- identityElement (Min  HOrd_Real)      = VReal LF.infinity

flattenLiteral :: Literal a -> CStat
flattenLiteral = let n           = undefNode
                     constExpr x = CExpr (Just $ CConst $ x n) n in
  \lit -> case lit of
            (LNat x)  -> constExpr $ CIntConst (cInteger $ fromIntegral x)
            (LInt x)  -> constExpr $ CIntConst (cInteger $ fromIntegral x)
            (LProb x) -> let rat = fromNonNegativeRational x
                             x'  = (fromIntegral $ numerator rat) / (fromIntegral $ denominator rat)
                         in constExpr $ CFloatConst (cFloat x') -- losing precision
            (LReal x) -> constExpr $ CFloatConst (cFloat $ fromRational x)


empty_c :: a -> CStat
empty_c = error "TODO: empty_c"

datum_c :: a -> CStat
datum_c = error "TODO: datum_c"

case_c :: a -> b -> CStat
case_c = error "TODO: case_c"

array_c :: a -> b -> CStat
array_c = error "TODO: array_c"

cons_c :: a -> b -> CStat
cons_c = error "TODO: cons_c"

superpose_c :: a -> CStat
superpose_c = error "TODO: superpose_c"

reject_c :: a -> CStat
reject_c = error "TODO: reject_c"

flattenSCon :: ABT Term abt
            => SCon args a
            -> SArgs abt args
            -> CStat
flattenSCon Lam_            = \(x :* End)           -> error "TODO: flattenSCon: Lam_"
flattenSCon App_            = \(x :* y :* End)      -> error "TODO: flattenSCon: App_"
flattenSCon Let_            = \(x :* y :* End)      -> error "TODO: flattenSCon: Let_"
flattenSCon (CoerceTo_ t)   = \(x :* End)           -> error "TODO: flattenSCon: (CoerceTo_ t)"
flattenSCon (UnsafeFrom_ t) = \(x :* End)           -> error "TODO: flattenSCon: (UnsafeFrom_ t)"
flattenSCon (PrimOp_ t)     = flattenPrimOp t
flattenSCon (ArrayOp_ t)    = flattenArrayOp t
flattenSCon (MeasureOp_ t)  = flattenMeasureOp t
flattenSCon Dirac           = \(x :* End)           -> error "TODO: flattenSCon: Dirac"
flattenSCon MBind           = \(x :* y :* End)      -> error "TODO: flattenSCon: MBind"
flattenSCon Plate           = \(x :* y :* End)      -> error "TODO: flattenSCon: Plate"
flattenSCon Chain           = \(x :* y :* z :* End) -> error "TODO: flattenSCon: Chain"
flattenSCon Integrate       = error "TODO: flattenSCon: Integrate"
flattenSCon Summate         = error "TODO: flattenSCon: Summate"
flattenSCon Expect          = error "TODO: flattenSCon: Expect"
flattenSCon Observe         = error "TODO: flattenSCon: Observe"

flattenPrimOp :: ( ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
              => PrimOp typs a
              -> SArgs abt args
              -> CStat
flattenPrimOp Not         (x :* End)      = error "TODO: flattenPrimOp Not"
flattenPrimOp Pi          End             = error "TODO: flattenPrimOp Pi"
flattenPrimOp Cos         (x :* End)      = error "TODO: flattenPrimOp Cos"
flattenPrimOp Sin         (x :* End)      = error "TODO: flattenPrimOp Sin"
flattenPrimOp RealPow     (x :* y :* End) = error "TODO: flattenPrimOp RealPow"
flattenPrimOp Exp         (x :* End)      = error "TODO: flattenPrimOp Exp"
flattenPrimOp Infinity    End             = error "TODO: flattenPrimOp Infinity"
flattenPrimOp (Equal _)   (x :* y :* End) = error "TODO: flattenPrimOp (Equal _)"
flattenPrimOp (Less _)    (x :* y :* End) = error "TODO: flattenPrimOp (Less _)"
flattenPrimOp (NatPow _)  (x :* y :* End) = error "TODO: flattenPrimOp (NatPow _)"
flattenPrimOp (Negate _)  (x :* End)      = error "TODO: flattenPrimOp (Negate _)"
flattenPrimOp (Recip _)   (x :* End)      = error "TODO: flattenPrimOp (Recip _)"
flattenPrimOp (NatRoot _) (x :* y :* End) = error "TODO: flattenPrimOp (NatRoot _)"
flattenPrimOp _ _ = error "TODO: flattenPrimOp"

flattenArrayOp :: ( ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
               => ArrayOp typs a
               -> SArgs abt args
               -> CStat
flattenArrayOp (Index _)  (x :* y :* End)      = error "TODO: flattenArrayOp (Index _)"
flattenArrayOp (Size _)   (x :* End)           = error "TODO: flattenArrayOp (Size _)"
flattenArrayOp (Reduce _) (x :* y :* z :* End) = error "TODO: flattenArrayOp (Reduce _)"


flattenMeasureOp :: ( ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
                 => MeasureOp typs a
                 -> SArgs abt args
                 -> CStat
flattenMeasureOp Lebesgue    End             = error "TODO: flattenMeasureOp Lebesgue"
flattenMeasureOp Counting    End             = error "TODO: flattenMeasureOp Counting"
flattenMeasureOp Categorical (x :* End)      = error "TODO: flattenMeasureOp Categorical"
flattenMeasureOp Uniform     (x :* y :* End) = error "TODO: flattenMeasureOp Uniform"
flattenMeasureOp Normal      (x :* y :* End) = error "TODO: flattenMeasureOp Normal"
flattenMeasureOp Poisson     (x :* End)      = error "TODO: flattenMeasureOp Poisson"
flattenMeasureOp Gamma       (x :* y :* End) = error "TODO: flattenMeasureOp Gamma"
flattenMeasureOp Beta        (x :* y :* End) = error "TODO: flattenMeasureOp Beta"
