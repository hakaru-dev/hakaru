{-# LANGUAGE DataKinds
           , GADTs
           , TypeOperators
           , PolyKinds
           , FlexibleContexts
           , UndecidableInstances
           #-}

-- TODO: all the instances here are orphans. To ensure that we don't
-- have issues about orphan instances, we should give them all
-- newtypes and only provide the instance for those newtypes!
-- (and\/or: for the various op types, it's okay to move them to
-- AST.hs to avoid orphanage. It's just the instances for 'Term'
-- itself which are morally suspect outside of testing.)
{-# OPTIONS_GHC -Wall -fwarn-tabs -fno-warn-orphans #-}
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

---------------------------------------------------------------------
-- | This function performs 'jmEq' on a @(:$)@ node of the AST.
-- It's necessary to break it out like this since we can't just
-- give a 'JmEq1' instance for 'SCon' due to polymorphism issues
-- (e.g., we can't just say that 'Lam_' is John Major equal to
-- 'Lam_', since they may be at different types). However, once the
-- 'SArgs' associated with the 'SCon' is given, that resolves the
-- polymorphism.
jmEq_S
    :: (ABT Term abt, JmEq2 abt)
    => SCon args  a  -> SArgs abt args
    -> SCon args' a' -> SArgs abt args'
    -> Maybe (TypeEq a a', TypeEq args args')
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
    let t1 = coerceTo c  (typeOf es)
    let t2 = coerceTo c' (typeOf es')
    Refl <- jmEq1 t1 t2
    return (Refl, Refl)
jmEq_S (UnsafeFrom_ c) (es :* End) (UnsafeFrom_ c') (es' :* End) = do
    (Refl, Refl) <- jmEq2 es es'
    let t1 = coerceFrom c  (typeOf es)
    let t2 = coerceFrom c' (typeOf es')
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
    jmEq1 (x :* xs) (y :* ys) =
        jmEq2 x  y  >>= \(Refl, Refl) ->
        jmEq1 xs ys >>= \Refl ->
        Just Refl
    jmEq1 _         _         = Nothing


instance JmEq2 PrimOp where
    jmEq2 Not         Not         = Just (Refl, Refl)
    jmEq2 Impl        Impl        = Just (Refl, Refl)
    jmEq2 Diff        Diff        = Just (Refl, Refl)
    jmEq2 Nand        Nand        = Just (Refl, Refl)
    jmEq2 Nor         Nor         = Just (Refl, Refl)
    jmEq2 Pi          Pi          = Just (Refl, Refl)
    jmEq2 Sin         Sin         = Just (Refl, Refl)
    jmEq2 Cos         Cos         = Just (Refl, Refl)
    jmEq2 Tan         Tan         = Just (Refl, Refl)
    jmEq2 Asin        Asin        = Just (Refl, Refl)
    jmEq2 Acos        Acos        = Just (Refl, Refl)
    jmEq2 Atan        Atan        = Just (Refl, Refl)
    jmEq2 Sinh        Sinh        = Just (Refl, Refl)
    jmEq2 Cosh        Cosh        = Just (Refl, Refl)
    jmEq2 Tanh        Tanh        = Just (Refl, Refl)
    jmEq2 Asinh       Asinh       = Just (Refl, Refl)
    jmEq2 Acosh       Acosh       = Just (Refl, Refl)
    jmEq2 Atanh       Atanh       = Just (Refl, Refl)
    jmEq2 RealPow     RealPow     = Just (Refl, Refl)
    jmEq2 Exp         Exp         = Just (Refl, Refl)
    jmEq2 Log         Log         = Just (Refl, Refl)
    jmEq2 Infinity    Infinity    = Just (Refl, Refl)
    jmEq2 NegativeInfinity NegativeInfinity = Just (Refl, Refl)
    jmEq2 GammaFunc   GammaFunc   = Just (Refl, Refl)
    jmEq2 BetaFunc    BetaFunc    = Just (Refl, Refl)
    jmEq2 (Equal a)   (Equal b)   =
        jmEq1 (sing_HEq a) (sing_HEq b) >>= \Refl ->
        Just (Refl, Refl)
    jmEq2 (Less a)    (Less b)    =
        jmEq1 (sing_HOrd a) (sing_HOrd b) >>= \Refl ->
        Just (Refl, Refl)
    jmEq2 (NatPow  a) (NatPow  b) = jmEq1 a b >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Negate  a) (Negate  b) = jmEq1 a b >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Abs     a) (Abs     b) = jmEq1 a b >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Signum  a) (Signum  b) = jmEq1 a b >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Recip   a) (Recip   b) = jmEq1 a b >>= \Refl -> Just (Refl, Refl)
    jmEq2 (NatRoot a) (NatRoot b) = jmEq1 a b >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Erf     a) (Erf     b) = jmEq1 a b >>= \Refl -> Just (Refl, Refl)
    jmEq2 _ _ = Nothing

instance Eq2 PrimOp where
    eq2 x y = maybe False (const True) (jmEq2 x y)
    
instance Eq1 (PrimOp args) where
    eq1 x y = maybe False (const True) (jmEq2 x y)


instance JmEq2 ArrayOp where
    jmEq2 (Index  a) (Index  b) = jmEq1 a b >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Size   a) (Size   b) = jmEq1 a b >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Reduce a) (Reduce b) = jmEq1 a b >>= \Refl -> Just (Refl, Refl)
    jmEq2 _          _          = Nothing

instance Eq2 ArrayOp where
    eq2 x y = maybe False (const True) (jmEq2 x y)
    
instance Eq1 (ArrayOp args) where
    eq1 x y = maybe False (const True) (jmEq2 x y)


instance JmEq2 MeasureOp where
    jmEq2 Lebesgue    Lebesgue    = Just (Refl, Refl)
    jmEq2 Counting    Counting    = Just (Refl, Refl)
    jmEq2 Categorical Categorical = Just (Refl, Refl)
    jmEq2 Uniform     Uniform     = Just (Refl, Refl)
    jmEq2 Normal      Normal      = Just (Refl, Refl)
    jmEq2 Poisson     Poisson     = Just (Refl, Refl)
    jmEq2 Gamma       Gamma       = Just (Refl, Refl)
    jmEq2 Beta        Beta        = Just (Refl, Refl)
    jmEq2 (DirichletProcess a) (DirichletProcess b) =
        jmEq1 a b >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Plate a) (Plate b) =
        jmEq1 a b >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Chain s a) (Chain t b) =
        jmEq1 s t >>= \Refl ->
        jmEq1 a b >>= \Refl ->
        Just (Refl, Refl)
    jmEq2 _           _ = Nothing

instance Eq2 MeasureOp where
    eq2 x y = maybe False (const True) (jmEq2 x y)
    
instance Eq1 (MeasureOp args) where
    eq1 x y = maybe False (const True) (jmEq2 x y)


instance JmEq1 NaryOp where
    jmEq1 And      And      = Just Refl
    jmEq1 Or       Or       = Just Refl
    jmEq1 Xor      Xor      = Just Refl
    jmEq1 Iff      Iff      = Just Refl
    jmEq1 (Min  a) (Min  b) = jmEq1 (sing_HOrd a) (sing_HOrd b)
    jmEq1 (Max  a) (Max  b) = jmEq1 (sing_HOrd a) (sing_HOrd b)
    jmEq1 (Sum  a) (Sum  b) = jmEq1 a b
    jmEq1 (Prod a) (Prod b) = jmEq1 a b
    jmEq1 _        _        = Nothing

instance Eq1 NaryOp where
    eq1 x y = maybe False (const True) (jmEq1 x y)


instance JmEq1 Literal where
    jmEq1 (LNat  x) (LNat  y) = if x == y then Just Refl else Nothing
    jmEq1 (LInt  x) (LInt  y) = if x == y then Just Refl else Nothing
    jmEq1 (LProb x) (LProb y) = if x == y then Just Refl else Nothing
    jmEq1 (LReal x) (LReal y) = if x == y then Just Refl else Nothing
    jmEq1 _         _         = Nothing


instance (ABT Term abt, JmEq2 abt) => JmEq1 (Term abt) where
    jmEq1 (o :$ es) (o' :$ es') = do
        (Refl, Refl) <- jmEq_S o es o' es'
        return Refl
    jmEq1 (NaryOp_ o es) (NaryOp_ o' es') = do
        Refl <- jmEq1 o o'
        () <- all_jmEq2 es es'
        return Refl
    jmEq1 (Literal_ v)  (Literal_ w)   = jmEq1 v w
    jmEq1 (Empty_ a)    (Empty_ b)     = jmEq1 a b
    jmEq1 (Array_ i f)  (Array_ j g)   = do
        (Refl, Refl) <- jmEq2 i j
        (Refl, Refl) <- jmEq2 f g
        Just Refl
    jmEq1 (Datum_ _)     (Datum_ _)     = error "TODO jmEq1{Datum_}"
    jmEq1 (Case_  _ _)   (Case_  _ _)   = error "TODO jmEq1{Case_}"
    jmEq1 (Superpose_ _) (Superpose_ _) = error "TODO jmEq1{Superpose_}"
    jmEq1 _              _              = Nothing


all_jmEq2
    :: (ABT Term abt, JmEq2 abt)
    => S.Seq (abt '[] a)
    -> S.Seq (abt '[] a)
    -> Maybe ()
all_jmEq2 xs ys =
    let eq x y = maybe False (const True) (jmEq2 x y)
    in if F.and (S.zipWith eq xs ys) then Just () else Nothing


-- TODO: a more general function of type:
--   (JmEq2 abt) => Term abt a -> Term abt b -> Maybe (Sing a, TypeEq a b)
-- This can then be used to define typeOf and instance JmEq2 Term

instance (ABT Term abt, JmEq2 abt) => Eq1 (Term abt) where
    eq1 x y = maybe False (const True) (jmEq1 x y)

instance (ABT Term abt, JmEq2 abt) => Eq (Term abt a) where
    (==) = eq1

instance ( Show1 (Sing :: k -> *)
         , JmEq1 (Sing :: k -> *)
         , JmEq1 (syn (TrivialABT syn))
         , Foldable21 syn
         ) => JmEq2 (TrivialABT (syn :: ([k] -> k -> *) -> k -> *))
    where
    jmEq2 x y =
        case (viewABT x, viewABT y) of
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
         , Foldable21 syn
         ) => JmEq1 (TrivialABT (syn :: ([k] -> k -> *) -> k -> *) xs)
    where
    jmEq1 x y = jmEq2 x y >>= \(Refl, Refl) -> Just Refl

instance ( Show1 (Sing :: k ->  *)
         , JmEq1 (Sing :: k -> *)
         , Foldable21 syn
         , JmEq1 (syn (TrivialABT syn))
         ) => Eq2 (TrivialABT (syn :: ([k] -> k -> *) -> k -> *))
    where
    eq2 x y = maybe False (const True) (jmEq2 x y)

instance ( Show1 (Sing :: k ->  *)
         , JmEq1 (Sing :: k -> *)
         , Foldable21 syn
         , JmEq1 (syn (TrivialABT syn))
         ) => Eq1 (TrivialABT (syn :: ([k] -> k -> *) -> k -> *) xs)
    where
    eq1 = eq2

instance ( Show1 (Sing :: k ->  *)
         , JmEq1 (Sing :: k -> *)
         , Foldable21 syn
         , JmEq1 (syn (TrivialABT syn))
         ) => Eq (TrivialABT (syn :: ([k] -> k -> *) -> k -> *) xs a)
    where
    (==) = eq1
