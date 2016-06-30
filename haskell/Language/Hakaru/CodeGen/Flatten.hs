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
import qualified Data.IntMap        as IM
import qualified Data.Foldable      as F

node = undefNode
names = [ [letter] ++ show number
        | letter <- ['a'..'z']
        , number <- [1..]]

-- | flattenABT takes a Hakaru ABT and a C Var, and returns a
--   C Statement that assigns a flattened ABT to the var
flattenABT :: ABT Term abt
           => Ident
           -> Sing (a :: Hakaru)
           -> abt '[] a
           -> ([CDecl],CStat)
flattenABT var typ expr = (topDec ++ decs,topAssign)
  where topDec        = [CDecl [CTypeSpec (toCType typ)]
                         [(Just $ CDeclr (Just var) [] Nothing [] node,Nothing,Nothing)]
                         node]
        (decs,assign) = caseVarSyn expr flattenVar flattenTerm
        topAssign     = CExpr (Just
                              $ CAssign CAssignOp
                                        (CVar var node)
                                        (CStatExpr (CCompound [] [CBlockStmt assign] node)
                                        node)
                              node)
                              node


flattenVar :: Variable (a :: Hakaru) -> ([CDecl],CStat)
flattenVar = error "TODO: flattenVar"

flattenTerm :: ABT Term abt
            => Term abt a
            -> ([CDecl],CStat)
flattenTerm (NaryOp_ t s)  = flattenNAryOp t s
flattenTerm (Literal_ x)   = flattenLiteral x
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
              -> ([CDecl],CStat)
flattenNAryOp op args = undefined
  --                       (decs, CCompound []
  --                                        (fmap CBlockStmt (fmap fst args' ++ [CExpr (Just flattenedOp) node]))
  --                                        node)
  -- where namedArgs    = zip names F.toList args
  --       (decs,args') = F.foldr (\a c -> flattenABT (builtinIdent (fst a)) undefined (snd b) : c)
  --                              []
  --                              namedArgs
  --       nArgOp'   = F.foldr (\x y -> CBinary (flattenOp op) x y node)
  --                           (CConst (unitOp op))
  --                           (fmap (\a -> CVar a node) args')




flattenOp :: NaryOp a -> CBinaryOp
flattenOp And                   = CAndOp
flattenOp (Sum _)               = CAddOp
flattenOp (Prod HSemiring_Prob) = CAddOp   -- product of exp is addition
flattenOp (Prod _)              = CMulOp
-- flattenOp (Min _)  = undefined
-- flattenOp (Max _)  = undefined
flattenOp _ = error "TODO: flattenOp"

unitOp :: NaryOp a -> CConstant NodeInfo
unitOp And                   = CIntConst (cInteger 1) node
unitOp (Sum HSemiring_Nat)   = CIntConst (cInteger 0) node
unitOp (Sum HSemiring_Int)   = CIntConst (cInteger 0) node
-- unitOp (Sum HSemiring_Prob)  = VProb 0
-- unitOp (Sum HSemiring_Real)  = VReal 0
unitOp (Prod HSemiring_Nat)  = CIntConst (cInteger 1) node
unitOp (Prod HSemiring_Int)  = CIntConst (cInteger 1) node
unitOp _ = error "TODO: unitOp"
-- unitOp (Prod HSemiring_Prob) = VProb 1
-- unitOp (Prod HSemiring_Real) = VReal 1
-- unitOp (Max  HOrd_Prob)      = VProb 0
-- unitOp (Max  HOrd_Real)      = VReal LF.negativeInfinity
-- unitOp (Min  HOrd_Prob)      = VProb (LF.logFloat LF.infinity)
-- unitOp (Min  HOrd_Real)      = VReal LF.infinity

flattenLiteral :: Literal a -> ([CDecl],CStat)
flattenLiteral = let constExpr x = CExpr (Just $ CConst $ x node) node in
  \lit -> case lit of
            (LNat x)  -> ([],constExpr $ CIntConst (cInteger $ fromIntegral x))
            (LInt x)  -> ([],constExpr $ CIntConst (cInteger $ fromIntegral x))
            (LProb x) -> let rat = fromNonNegativeRational x
                             x'  = (fromIntegral $ numerator rat)
                                 / (fromIntegral $ denominator rat)
                         in ([], CExpr (Just (CCall (CVar (builtinIdent "log") node)
                                                    [CConst (CFloatConst (cFloat x') node)]
                                                    node))
                                       node)
            (LReal x) -> ([],constExpr $ CFloatConst (cFloat $ fromRational x))


toCType :: Sing (a :: Hakaru) -> CTypeSpecifier NodeInfo
toCType SInt       = CIntType undefNode
toCType SNat       = CIntType undefNode
toCType SProb      = CDoubleType undefNode
toCType SReal      = CDoubleType undefNode
toCType _          = error "TODO: toCType"



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
flattenSCon (Summate _ _)   = error "TODO: flattenSCon: Summate"
flattenSCon Expect          = error "TODO: flattenSCon: Expect"
flattenSCon Observe         = error "TODO: flattenSCon: Observe"

flattenPrimOp :: ( ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
              => PrimOp typs a
              -> SArgs abt args
              -> CStat
flattenPrimOp Not          (x :* End)      = error "TODO: flattenPrimOp Not"
flattenPrimOp Pi           End             = error "TODO: flattenPrimOp Pi"
flattenPrimOp Cos          (x :* End)      = error "TODO: flattenPrimOp Cos"
flattenPrimOp Sin          (x :* End)      = error "TODO: flattenPrimOp Sin"
flattenPrimOp RealPow      (x :* y :* End) = error "TODO: flattenPrimOp RealPow"
flattenPrimOp Exp          (x :* End)      = error "TODO: flattenPrimOp Exp"
flattenPrimOp (Infinity _) End             = error "TODO: flattenPrimOp Infinity"
flattenPrimOp (Equal _)    (x :* y :* End) = error "TODO: flattenPrimOp (Equal _)"
flattenPrimOp (Less _)     (x :* y :* End) = error "TODO: flattenPrimOp (Less _)"
flattenPrimOp (NatPow _)   (x :* y :* End) = error "TODO: flattenPrimOp (NatPow _)"
flattenPrimOp (Negate _)   (x :* End)      = error "TODO: flattenPrimOp (Negate _)"
flattenPrimOp (Recip _)    (x :* End)      = error "TODO: flattenPrimOp (Recip _)"
flattenPrimOp (NatRoot _)  (x :* y :* End) = error "TODO: flattenPrimOp (NatRoot _)"
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
