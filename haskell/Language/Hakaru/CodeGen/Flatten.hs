{-# LANGUAGE DataKinds,
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

import Data.List.NonEmpty
import Data.Number.Natural
import Data.Ratio
import Data.Sequence (Seq)

----- Using enviroment representation from Language.Hakaru.Sample
data EAssoc =
    forall a. EAssoc {-# UNPACK #-} !(Variable a) !(Value a)

newtype Env = Env (IM.IntMap EAssoc)

emptyEnv :: Env
emptyEnv = Env IM.empty

updateEnv :: EAssoc -> Env -> Env
updateEnv v@(EAssoc x _) (Env xs) =
    Env $ IM.insert (fromNat $ varID x) v xs

lookupVar :: Variable a -> Env -> Maybe (Value a)
lookupVar x (Env env) = do
    EAssoc x' e' <- IM.lookup (fromNat $ varID x) env
    Refl         <- varEq x x'
    return e'
----

flattenABT :: ABT Term abt
           => abt '[] a
           -> NonEmpty CStat
flattenABT e = caseVarSyn e flattenVar flattenTerm

flattenVar :: Variable (a :: Hakaru) -> NonEmpty CStat
flattenVar = undefined

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


nAryOp_c :: NaryOp a -> Seq b -> CStat
nAryOp_c And      = undefined
nAryOp_c Or       = undefined
nAryOp_c Xor      = undefined
nAryOp_c Iff      = undefined
nAryOp_c (Min o)  = undefined
nAryOp_c (Max o)  = undefined
nAryOp_c (Sum _)  = undefined
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



flattenSCon :: ABT Term abt
            => SCon args a
            -> SArgs abt args
            -> NonEmpty CStat
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
              -> NonEmpty CStat
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
               -> NonEmpty CStat
flattenArrayOp (Index _)  (x :* y :* End)      = undefined
flattenArrayOp (Size _)   (x :* End)           = undefined
flattenArrayOp (Reduce _) (x :* y :* z :* End) = undefined


flattenMeasureOp :: ( ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
                 => MeasureOp typs a
                 -> SArgs abt args
                 -> NonEmpty CStat
flattenMeasureOp Lebesgue    End             = undefined
flattenMeasureOp Counting    End             = undefined
flattenMeasureOp Categorical (x :* End)      = undefined
flattenMeasureOp Uniform     (x :* y :* End) = undefined
flattenMeasureOp Normal      (x :* y :* End) = undefined
flattenMeasureOp Poisson     (x :* End)      = undefined
flattenMeasureOp Gamma       (x :* y :* End) = undefined
flattenMeasureOp Beta        (x :* y :* End) = undefined
