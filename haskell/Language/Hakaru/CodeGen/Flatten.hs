{-# LANGUAGE DataKinds,
             ExistentialQuantification,
             FlexibleContexts,
             FlexibleInstances,
             GADTs,
             KindSignatures #-}

module Language.Hakaru.CodeGen.Flatten where

import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Types.DataKind

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


flattenABT :: ABT Term abt
           => abt '[] a
           -> CStat
flattenABT e = caseVarSyn e
                          flattenVar
                          flattenTerm

flattenVar :: Variable (a :: Hakaru) -> CStat
flattenVar = undefined

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
              => NaryOp a -> Seq (abt '[] b) -> CStat
flattenNAryOp op args = undefined
                        -- F.foldr $ \x y -> CExpr $ Just $ CBinary (flattenOp op) x y undefNode undefNode
                        --         $ CConst (unitOp op)
                        --         $ fmap undefined args

flattenOp :: NaryOp a -> CBinaryOp
flattenOp (Sum HSemiring_Nat) = CAddOp
flattenOp (Sum HSemiring_Int) = CAddOp
flattenOp _ = undefined

unitOp   :: NaryOp a -> CConstant NodeInfo
unitOp    (Sum HSemiring_Nat) = CIntConst (cInteger 0) undefNode
unitOp    (Sum HSemiring_Int) = CIntConst (cInteger 0) undefNode

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
empty_c = undefined -- CExpr Nothing undefNode

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

flattenSCon :: ABT Term abt
            => SCon args a
            -> SArgs abt args
            -> CStat
flattenSCon Lam_            = \(x :* End)           -> undefined
flattenSCon App_            = \(x :* y :* End)      -> undefined
flattenSCon Let_            = \(x :* y :* End)      -> undefined
flattenSCon (CoerceTo_ t)   = \(x :* End)           -> undefined
flattenSCon (UnsafeFrom_ t) = \(x :* End)           -> undefined
flattenSCon (PrimOp_ t)     = flattenPrimOp t
flattenSCon (ArrayOp_ t)    = flattenArrayOp t
flattenSCon (MeasureOp_ t)  = flattenMeasureOp t
flattenSCon Dirac           = \(x :* End)           -> undefined
flattenSCon MBind           = \(x :* y :* End)      -> undefined
flattenSCon Plate           = \(x :* y :* End)      -> undefined
flattenSCon Chain           = \(x :* y :* z :* End) -> undefined
flattenSCon Integrate       = undefined
flattenSCon Summate         = undefined
flattenSCon Expect          = undefined
flattenSCon Observe         = undefined

flattenPrimOp :: ( ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
              => PrimOp typs a
              -> SArgs abt args
              -> CStat
flattenPrimOp Not         (x :* End)      = undefined
flattenPrimOp Pi          End             = undefined
flattenPrimOp Cos         (x :* End)      = undefined
flattenPrimOp Sin         (x :* End)      = undefined
flattenPrimOp RealPow     (x :* y :* End) = undefined
flattenPrimOp Exp         (x :* End)      = undefined
flattenPrimOp Infinity    End             = undefined
flattenPrimOp (Equal _)   (x :* y :* End) = undefined
flattenPrimOp (Less _)    (x :* y :* End) = undefined
flattenPrimOp (NatPow _)  (x :* y :* End) = undefined
flattenPrimOp (Negate _)  (x :* End)      = undefined
flattenPrimOp (Recip _)   (x :* End)      = undefined
flattenPrimOp (NatRoot _) (x :* y :* End) = undefined
flattenPrimOp _ _ = undefined


flattenArrayOp :: ( ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
               => ArrayOp typs a
               -> SArgs abt args
               -> CStat
flattenArrayOp (Index _)  (x :* y :* End)      = undefined
flattenArrayOp (Size _)   (x :* End)           = undefined
flattenArrayOp (Reduce _) (x :* y :* z :* End) = undefined


flattenMeasureOp :: ( ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
                 => MeasureOp typs a
                 -> SArgs abt args
                 -> CStat
flattenMeasureOp Lebesgue    End             = undefined
flattenMeasureOp Counting    End             = undefined
flattenMeasureOp Categorical (x :* End)      = undefined
flattenMeasureOp Uniform     (x :* y :* End) = undefined
flattenMeasureOp Normal      (x :* y :* End) = undefined
flattenMeasureOp Poisson     (x :* End)      = undefined
flattenMeasureOp Gamma       (x :* y :* End) = undefined
flattenMeasureOp Beta        (x :* y :* End) = undefined
