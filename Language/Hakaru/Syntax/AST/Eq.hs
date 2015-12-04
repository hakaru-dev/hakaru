{-# LANGUAGE DataKinds
           , GADTs
           , TypeOperators
           , FlexibleContexts
           , UndecidableInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}

module Language.Hakaru.Syntax.AST.Eq where

import Language.Hakaru.Syntax.HClasses
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.Coercion
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.TypeOf


jmEq_S :: (ABT AST abt, JmEq2 abt) 
         =>  SCon args a   -> SArgs abt args  ->
             SCon args' a' -> SArgs abt args' ->
             Maybe (TypeEq a a', TypeEq args args')
jmEq_S Lam_      es Lam_       es' =
    jmEq1 es es' >>= \Refl -> Just (Refl, Refl)
jmEq_S App_      es App_       es' =
    jmEq1 es es' >>= \Refl -> Just (Refl, Refl)
jmEq_S Let_      es Let_       es' =
    jmEq1 es es' >>= \Refl -> Just (Refl, Refl)
jmEq_S (Ann_ _)  es (Ann_ _)  es' =
    jmEq1 es es' >>= \Refl -> Just (Refl, Refl)
jmEq_S (CoerceTo_ c) (es :* End) (CoerceTo_ c') (es' :* End) = do
    (Refl, Refl) <- jmEq2 es es'
    let t1 = singCoerceTo c  (typeOf es)
    let t2 = singCoerceTo c' (typeOf es')
    Refl <- jmEq1 t1 t2
    return (Refl, Refl)
jmEq_S (UnsafeFrom_ c) (es :* End) (UnsafeFrom_ c') (es' :* End) = do
    (Refl, Refl) <- jmEq2 es es'
    let t1 = singCoerceFrom c  (typeOf es)
    let t2 = singCoerceFrom c' (typeOf es')
    Refl <- jmEq1 t1 t2
    return (Refl, Refl)
jmEq_S (PrimOp_ op) es (PrimOp_ op') es' = do
    Refl <- jmEq1 es es'
    (Refl, Refl) <- jmEq2 op op'
    return (Refl, Refl)
jmEq_S (ArrayOp_ op) es (ArrayOp_ op') es' = do
    Refl <- jmEq1 es es'
    (Refl, Refl) <- jmEq2 op op'
    return (Refl, Refl)
jmEq_S (MeasureOp_ op) es (MeasureOp_ op') es' = do
    Refl <- jmEq1 es es'
    (Refl, Refl) <- jmEq2 op op'
    return (Refl, Refl)
jmEq_S Dirac     es Dirac      es' =
    jmEq1 es es' >>= \Refl -> Just (Refl, Refl)
jmEq_S MBind     es MBind      es' =
    jmEq1 es es' >>= \Refl -> Just (Refl, Refl)
jmEq_S Integrate es Integrate  es' =
    jmEq1 es es' >>= \Refl -> Just (Refl, Refl)
jmEq_S Summate   es Summate    es' =
    jmEq1 es es' >>= \Refl -> Just (Refl, Refl)
jmEq_S Expect    es Expect     es' =
    jmEq1 es es' >>= \Refl -> Just (Refl, Refl)
jmEq_S _         _  _          _   = Nothing

instance JmEq2 abt => JmEq1 (SArgs abt) where
    jmEq1 End       End       = Just Refl
    jmEq1 (x :* xs) (y :* ys) = do
      (Refl, Refl) <- jmEq2 x y
      Refl <- jmEq1 xs ys
      return Refl
    jmEq1 _         _         = Nothing

instance JmEq2 PrimOp where
    jmEq2 Not       Not            = Just (Refl, Refl)
    jmEq2 Impl      Impl           = Just (Refl, Refl)
    jmEq2 Diff      Diff           = Just (Refl, Refl)
    jmEq2 Nand      Nand           = Just (Refl, Refl)
    jmEq2 Nor       Nor            = Just (Refl, Refl)
    jmEq2 Pi        Pi             = Just (Refl, Refl)
    jmEq2 Sin       Sin            = Just (Refl, Refl)
    jmEq2 Cos       Cos            = Just (Refl, Refl)
    jmEq2 Tan       Tan            = Just (Refl, Refl)
    jmEq2 Asin      Asin           = Just (Refl, Refl)
    jmEq2 Acos      Acos           = Just (Refl, Refl)
    jmEq2 Atan      Atan           = Just (Refl, Refl)
    jmEq2 Sinh      Sinh           = Just (Refl, Refl)
    jmEq2 Cosh      Cosh           = Just (Refl, Refl)
    jmEq2 Tanh      Tanh           = Just (Refl, Refl)
    jmEq2 Asinh     Asinh          = Just (Refl, Refl)
    jmEq2 Acosh     Acosh          = Just (Refl, Refl)
    jmEq2 Atanh     Atanh          = Just (Refl, Refl)
    jmEq2 RealPow   RealPow        = Just (Refl, Refl)
    jmEq2 Exp       Exp            = Just (Refl, Refl)
    jmEq2 Log       Log            = Just (Refl, Refl)
    jmEq2 Infinity  Infinity       = Just (Refl, Refl)
    jmEq2 NegativeInfinity NegativeInfinity = Just (Refl, Refl)
    jmEq2 GammaFunc GammaFunc      = Just (Refl, Refl)
    jmEq2 BetaFunc  BetaFunc       = Just (Refl, Refl)
    jmEq2 (Equal a)   (Equal a')   =
        jmEq1 (sing_HEq a) (sing_HEq a') >>= \Refl ->
        Just (Refl, Refl)
    jmEq2 (Less a)    (Less a')    =
        jmEq1 (sing_HOrd a) (sing_HOrd a') >>= \Refl ->
        Just (Refl, Refl)
    jmEq2 (NatPow a)  (NatPow a')  =
        jmEq1 a a' >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Negate a)  (Negate a')  =
        jmEq1 a a' >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Abs a)     (Abs a')     =
        jmEq1 a a' >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Signum a)  (Signum a')  =
        jmEq1 a a' >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Recip a)   (Recip a')   =
        jmEq1 a a' >>= \Refl -> Just (Refl, Refl)
    jmEq2 (NatRoot a) (NatRoot a') =
        jmEq1 a a' >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Erf a) (Erf a') =
        jmEq1 a a' >>= \Refl -> Just (Refl, Refl)


instance Eq2 PrimOp where
    eq2 x y = maybe False (const True) (jmEq2 x y)

instance JmEq2 ArrayOp where
    jmEq2 (Index  x) (Index  y) = jmEq1 x y >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Size   x) (Size   y) = jmEq1 x y >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Reduce x) (Reduce y) = jmEq1 x y >>= \Refl -> Just (Refl, Refl)

instance Eq2 ArrayOp where
    eq2 x y = maybe False (const True) (jmEq2 x y)

instance JmEq2 MeasureOp where
    jmEq2 Lebesgue    Lebesgue    = Just (Refl, Refl)
    jmEq2 Counting    Counting    = Just (Refl, Refl)
    jmEq2 Categorical Categorical = Just (Refl, Refl)
    jmEq2 Uniform     Uniform     = Just (Refl, Refl)
    jmEq2 Normal      Normal      = Just (Refl, Refl)
    jmEq2 Poisson     Poisson     = Just (Refl, Refl)
    jmEq2 Gamma       Gamma       = Just (Refl, Refl)
    jmEq2 (DirichletProcess a) (DirichletProcess a') =
        jmEq1 a a' >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Plate a) (Plate a') =
        jmEq1 a a' >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Chain s a) (Chain s' a') =
        jmEq1 s s' >>= \Refl ->
        jmEq1 a a' >>= \Refl ->
        Just (Refl, Refl)

instance Eq2 MeasureOp where
    eq2 x y = maybe False (const True) (jmEq2 x y)

instance (ABT AST abt, JmEq2 abt) => JmEq1 (AST abt) where
    jmEq1 (o :$ es) (o' :$ es') = do
        (Refl, Refl) <- jmEq_S o es o' es'
        return Refl
    jmEq1 _         _           = undefined

-- TODO: a more general function of type:
--   (JmEq2 abt) => AST abt a -> AST abt b -> Maybe (Sing a, TypeEq a b)
-- This can then be used to define typeOf and instance JmEq2 AST

instance (ABT AST abt, JmEq2 abt) => Eq1 (AST abt) where
    eq1 x y = maybe False (const True) (jmEq1 x y)

instance (ABT AST abt, JmEq2 abt) => Eq (AST abt a) where
    (==) = eq1
