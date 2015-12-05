{-# LANGUAGE DataKinds
           , GADTs
           , TypeOperators
           , PolyKinds
           , FlexibleContexts
           , UndecidableInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
---------------------------------------------------------------------
--
-- Warning: The following module is for testing purposes only.
--   These instances are inefficient and using them will usually
--   lead to inefficient solutions.
--
---------------------------------------------------------------------
module Language.Hakaru.Syntax.AST.Eq where

import Language.Hakaru.Syntax.HClasses
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.Coercion
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.TypeOf

import qualified Data.Foldable as F
import qualified Data.Sequence as S

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
    jmEq2 _       _        = Nothing


instance Eq2 PrimOp where
    eq2 x y = maybe False (const True) (jmEq2 x y)

instance JmEq2 ArrayOp where
    jmEq2 (Index  x) (Index  y) = jmEq1 x y >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Size   x) (Size   y) = jmEq1 x y >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Reduce x) (Reduce y) = jmEq1 x y >>= \Refl -> Just (Refl, Refl)
    jmEq2 _          _          = Nothing

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
    jmEq2 Beta        Beta        = Just (Refl, Refl)
    jmEq2 (DirichletProcess a) (DirichletProcess a') =
        jmEq1 a a' >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Plate a) (Plate a') =
        jmEq1 a a' >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Chain s a) (Chain s' a') =
        jmEq1 s s' >>= \Refl ->
        jmEq1 a a' >>= \Refl ->
        Just (Refl, Refl)
    jmEq2 _           _ = Nothing

instance Eq2 MeasureOp where
    eq2 x y = maybe False (const True) (jmEq2 x y)

instance JmEq1 NaryOp where
    jmEq1 And And = Just Refl
    jmEq1 Or  Or  = Just Refl
    jmEq1 Xor Xor = Just Refl
    jmEq1 Iff Iff = Just Refl
    jmEq1 (Min a)  (Min a')  = jmEq1 (sing_HOrd a) (sing_HOrd a')
    jmEq1 (Max a)  (Max a')  = jmEq1 (sing_HOrd a) (sing_HOrd a')
    jmEq1 (Sum a)  (Sum a')  = jmEq1 a a'
    jmEq1 (Prod a) (Prod a') = jmEq1 a a'
    jmEq1 _        _         = Nothing


instance Eq1 NaryOp where
    eq1 x y = maybe False (const True) (jmEq1 x y)

instance JmEq1 Literal where
    jmEq1 (LNat _)  (LNat _)  = Just Refl
    jmEq1 (LInt _)  (LInt _)  = Just Refl
    jmEq1 (LProb _) (LProb _) = Just Refl
    jmEq1 (LReal _) (LReal _) = Just Refl
    jmEq1 _         _         = Nothing

instance (ABT AST abt, JmEq2 abt) => JmEq1 (AST abt) where
    jmEq1 (o :$ es) (o' :$ es') = do
        (Refl, Refl) <- jmEq_S o es o' es'
        return Refl
    jmEq1 (NaryOp_ o _) (NaryOp_ o' _)  = jmEq1 o o'
    jmEq1 (Literal_ v)  (Literal_ v')   = jmEq1 v v'
    jmEq1 (Empty_ a)    (Empty_ a')     = jmEq1 a a'
    jmEq1 (Array_ _ a)  (Array_ _ a')   =
        jmEq2 a a' >>= \(Refl, Refl) -> Just Refl
    jmEq1 (Datum_ _)    (Datum_ _)      = error "TODO jmEq1{Datum}"
    jmEq1 _              _              = Nothing

-- TODO: a more general function of type:
--   (JmEq2 abt) => AST abt a -> AST abt b -> Maybe (Sing a, TypeEq a b)
-- This can then be used to define typeOf and instance JmEq2 AST

instance (ABT AST abt, JmEq2 abt) => Eq1 (AST abt) where
    eq1 (NaryOp_ o es) (NaryOp_ o' es') =
        case jmEq1 o o' of
             Just Refl -> F.all (\(x,y) -> eq2 x y) (S.zip es es')
             Nothing   -> False
    eq1 (Literal_ a)   (Literal_ a')    = eq1 a a'
    eq1 (Array_ n a)   (Array_ n' a')   = eq2 n n' && eq2 a a'
    eq1 (Case_ a b)    (Case_ a' b')    =
        case jmEq2 a a' of
          Just (Refl, Refl)  -> eq2 a a' &&
              F.all (\(x, y) -> eq1 x y) (zip b b')
          Nothing            -> False
    eq1 (Superpose_ [])          (Superpose_ [])             = True
    eq1 (Superpose_ ((p,m):pms)) (Superpose_ ((p',m'):pms')) =
        eq2 p p' &&
        eq2 m m' &&
        eq1 (Superpose_ pms) (Superpose_ pms')
    eq1 x y = maybe False (const True) (jmEq1 x y)

instance (ABT AST abt, JmEq2 abt) => Eq (AST abt a) where
    (==) = eq1

instance ( Show1 (Sing :: k -> *)
         , JmEq1 (Sing :: k -> *)
         , JmEq1 (syn (TrivialABT syn))
         , Foldable21 syn) =>
         JmEq2 (TrivialABT (syn :: ([k] -> k -> *) -> k -> *))
    where
    jmEq2 x y = case (viewABT x, viewABT y) of
                  (Syn t1, Syn t2) ->
                      jmEq1 t1 t2 >>= \Refl -> Just (Refl, Refl) 
                  (Var (Variable _ _ t1), Var (Variable _ _ t2)) ->
                      jmEq1 t1 t2 >>= \Refl -> Just (Refl, Refl)
                  (Bind (Variable _ _ x1) v1, Bind (Variable _ _ x2) v2) -> do
                      Refl <- jmEq1 x1 x2
                      (Refl,Refl) <- jmEq2 (unviewABT v1) (unviewABT v2)
                      return (Refl, Refl)
                  _ -> Nothing


instance ( Show1 (Sing :: k -> *)
         , JmEq1 (Sing :: k -> *)
         , JmEq1 (syn (TrivialABT syn))
         , Foldable21 syn) =>
         JmEq1 (TrivialABT (syn :: ([k] -> k -> *) -> k -> *) xs)
    where
    jmEq1 x y = jmEq2 x y >>= \(Refl, Refl) -> Just Refl


instance ( Show1 (Sing :: k ->  *)
         , JmEq1 (Sing :: k -> *)
         , Foldable21 syn
         , Eq1 (syn (TrivialABT syn))) =>
         Eq2 (TrivialABT (syn :: ([k] -> k -> *) -> k -> *))
    where
    eq2 x y = case (viewABT x, viewABT y) of
                (Syn t1, Syn t2) -> eq1 t1 t2
                (Var t1, Var t2) -> eq1 t1 t2
                (Bind x1 v1, Bind x2 v2) ->
                    x1 `eq1` x2 &&
                    (unviewABT v1) `eq2` (unviewABT v2)
                _                -> False


instance ( Show1 (Sing :: k ->  *)
         , JmEq1 (Sing :: k -> *)
         , Foldable21 syn
         , Eq1 (syn (TrivialABT syn))) =>
         Eq1 (TrivialABT (syn :: ([k] -> k -> *) -> k -> *) xs)
    where
    eq1 = eq2

instance ( Show1 (Sing :: k ->  *)
         , JmEq1 (Sing :: k -> *)
         , Foldable21 syn
         , Eq1 (syn (TrivialABT syn))) =>
         Eq (TrivialABT (syn :: ([k] -> k -> *) -> k -> *) xs a)
    where
    (==) = eq1
