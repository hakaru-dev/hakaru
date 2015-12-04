{-# LANGUAGE DataKinds
           , GADTs
           , TypeOperators
           , FlexibleContexts
           , UndecidableInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}

module Language.Hakaru.Syntax.AST.Eq where

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
    jmEq2 = undefined

instance Eq2 PrimOp where
    eq2 x y = maybe False (const True) (jmEq2 x y)

instance JmEq2 ArrayOp where
    jmEq2 (Index  x) (Index  y) = jmEq1 x y >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Size   x) (Size   y) = jmEq1 x y >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Reduce x) (Reduce y) = jmEq1 x y >>= \Refl -> Just (Refl, Refl)

instance Eq2 ArrayOp where
    eq2 x y = maybe False (const True) (jmEq2 x y)

instance JmEq2 MeasureOp where
    jmEq2 = undefined

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
