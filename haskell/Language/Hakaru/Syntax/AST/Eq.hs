{-# LANGUAGE CPP
           , DataKinds
           , GADTs
           , TypeOperators
           , PolyKinds
           , FlexibleContexts
           , ScopedTypeVariables
           , UndecidableInstances
           #-}

-- TODO: all the instances here are orphans. To ensure that we don't
-- have issues about orphan instances, we should give them all
-- newtypes and only provide the instance for those newtypes!
-- (and\/or: for the various op types, it's okay to move them to
-- AST.hs to avoid orphanage. It's just the instances for 'Term'
-- itself which are morally suspect outside of testing.)
{-# OPTIONS_GHC -Wall -fwarn-tabs -fno-warn-orphans #-}
----------------------------------------------------------------
--                                                    2016.05.24
-- |
-- Module      :  Language.Hakaru.Syntax.ABT.Eq
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Warning: The following module is for testing purposes only. Using
-- the 'JmEq1' instance for 'Term' is inefficient and should not
-- be done accidentally. To implement that (orphan) instance we
-- also provide the following (orphan) instances:
--
-- > SArgs      : JmEq1
-- > Term       : JmEq1, Eq1, Eq
-- > TrivialABT : JmEq2, JmEq1, Eq2, Eq1, Eq
--
-- TODO: because this is only for testing, everything else should
-- move to the @Tests@ directory.
----------------------------------------------------------------
module Language.Hakaru.Syntax.AST.Eq where

import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.TypeOf

import Control.Monad.Reader

import qualified Data.Foldable      as F
import qualified Data.List.NonEmpty as L
import qualified Data.Sequence      as S
import qualified Data.Traversable   as T

#if __GLASGOW_HASKELL__ < 710
import           Data.Functor ((<$>))
import           Data.Traversable
#endif


import Data.Maybe
-- import Data.Number.Nat

import Unsafe.Coerce

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


-- TODO: Handle jmEq2 of pat and pat'
jmEq_Branch
    :: (ABT Term abt, JmEq2 abt)
    => [(Branch a abt b, Branch a abt b')]
    -> Maybe (TypeEq b b')
jmEq_Branch []                                  = Nothing
jmEq_Branch [(Branch pat e, Branch pat' e')]    = do
    (Refl, Refl) <- jmEq2 e e'
    return Refl
jmEq_Branch ((Branch pat e, Branch pat' e'):es) = do
    (Refl, Refl) <- jmEq2 e e'
    jmEq_Branch es

instance JmEq2 abt => JmEq1 (SArgs abt) where
    jmEq1 End       End       = Just Refl
    jmEq1 (x :* xs) (y :* ys) =
        jmEq2 x  y  >>= \(Refl, Refl) ->
        jmEq1 xs ys >>= \Refl ->
        Just Refl
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
    jmEq1 (Datum_ (Datum hint _ _)) (Datum_ (Datum hint' _ _))
        -- BUG: We need to compare structurally rather than using the hint
        | hint == hint' = unsafeCoerce (Just Refl)
        | otherwise     = Nothing
    jmEq1 (Case_  a bs) (Case_  a' bs')      = do
        (Refl, Refl) <- jmEq2 a a'
        jmEq_Branch (zip bs bs')
    jmEq1 (Superpose_ pms) (Superpose_ pms') = do
      (Refl,Refl) L.:| _ <- T.sequence $ fmap jmEq_Tuple (L.zip pms pms')
      return Refl
    jmEq1 _              _              = Nothing


all_jmEq2
    :: (ABT Term abt, JmEq2 abt)
    => S.Seq (abt '[] a)
    -> S.Seq (abt '[] a)
    -> Maybe ()
all_jmEq2 xs ys =
    let eq x y = isJust (jmEq2 x y)
    in if F.and (S.zipWith eq xs ys) then Just () else Nothing


jmEq_Tuple :: (ABT Term abt, JmEq2 abt)
           => ((abt '[] a , abt '[] b), 
               (abt '[] a', abt '[] b'))
           -> Maybe (TypeEq a a', TypeEq b b')
jmEq_Tuple ((a,b), (a',b')) = do
  a'' <- jmEq2 a a' >>= (\(Refl, Refl) -> Just Refl)
  b'' <- jmEq2 b b' >>= (\(Refl, Refl) -> Just Refl)
  return (a'', b'')


-- TODO: a more general function of type:
--   (JmEq2 abt) => Term abt a -> Term abt b -> Maybe (Sing a, TypeEq a b)
-- This can then be used to define typeOf and instance JmEq2 Term

instance (ABT Term abt, JmEq2 abt) => Eq1 (Term abt) where
    eq1 x y = isJust (jmEq1 x y)

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
    eq2 x y = isJust (jmEq2 x y)

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


type Varmap = Assocs (Variable :: Hakaru -> *)

alphaEq
    :: forall abt a
    .  (ABT Term abt)
    => abt '[] a
    -> abt '[] a
    -> Bool
alphaEq e1 e2 = runReader (go (viewABT e1) (viewABT e2)) emptyAssocs
    where
    -- Don't compare @x@ to @y@ directly; instead,
    -- look up whatever @x@ renames to (i.e., @y'@)
    -- and then see whether that is equal to @y@.
    go  :: forall xs1 xs2 a
        .  View (Term abt) xs1 a
        -> View (Term abt) xs2 a
        -> Reader Varmap Bool
    go (Var x) (Var y) = do
        s <- ask
        return $
            case lookupAssoc x s of
            Nothing -> isJust (varEq x  y) -- free variables
            Just y' -> isJust (varEq y' y)

    -- remember that @x@ renames to @y@ and recurse
    go (Bind x e1) (Bind y e2) =
        case jmEq1 (varType x) (varType y) of
        Just Refl -> local (insertAssoc (Assoc x y)) (go e1 e2)
        Nothing   -> return False

    -- perform the core comparison for syntactic equality
    go (Syn t1) (Syn t2) = termEq t1 t2

    -- if the views don't match, then clearly they are not equal.
    go _ _ = return False

    termEq :: forall a
        .  Term abt a
        -> Term abt a
        -> Reader Varmap Bool
    termEq e1 e2 =
        case (e1, e2) of
        (o1 :$ es1, o2 :$ es2)             -> sConEq o1 es1 o2 es2
        (NaryOp_ op1 es1, NaryOp_ op2 es2)
            | op1 == op2 ->
                F.and <$> (T.sequence $ S.zipWith go (fmap viewABT es1)
                    (fmap viewABT es2))
            | otherwise -> return False
        (Literal_ x, Literal_ y)           -> return (x == y)
        (Empty_ x, Empty_ y)               -> return $ maybe False (const True) (jmEq1 x y)
        (Datum_ d1, Datum_ d2)             -> datumEq d1 d2
        (Array_ n1 e1, Array_ n2 e2)       -> do
            m1 <- go (viewABT n1) (viewABT n2)
            m2 <- go (viewABT e1) (viewABT e2)
            return (m1 && m2)
        (Case_ e1 bs1, Case_ e2 bs2)       ->
            case jmEq1 (typeOf e1) (typeOf e2) of
            Just Refl -> do
                m1 <- go (viewABT e1) (viewABT e2)
                m2 <- and <$> (zipWithM sBranch bs1 bs2)
                return (m1 && m2)
        (Superpose_ pms1, Superpose_ pms2) ->
            F.and <$> (T.sequence $ L.zipWith pairEq pms1 pms2)
        (Reject_ x, Reject_ y)             ->
            return $ maybe False (const True) (jmEq1 x y)
        (_, _)                             -> return False

    sArgsEq
        :: forall args
        .  SArgs abt args
        -> SArgs abt args
        -> Reader Varmap Bool
    sArgsEq End         End         = return True
    sArgsEq (e1 :* es1) (e2 :* es2) = do
        m  <- go (viewABT e1) (viewABT e2)
        ms <- sArgsEq es1 es2
        return (m && ms)
    sArgsEq _ _ = return False

    sConEq
        :: forall a args1 args2
        .  SCon  args1 a
        -> SArgs abt args1
        -> SCon args2 a
        -> SArgs abt args2
        -> Reader Varmap Bool
    sConEq Lam_   e1 Lam_   e2 = sArgsEq e1 e2

    sConEq App_   (e1  :* e2  :* End)
           App_   (e1' :* e2' :* End) = do
        case jmEq1 (typeOf e2) (typeOf e2') of
        Just Refl -> do
            m1 <- go (viewABT e1) (viewABT e1')
            m2 <- go (viewABT e2) (viewABT e2')
            return (m1 && m2)
        Nothing   -> return False

    sConEq Let_   (e1  :* e2  :* End)
           Let_   (e1' :* e2' :* End) = do
        case jmEq1 (typeOf e1) (typeOf e1') of
        Just Refl -> do
            m1 <- go (viewABT e1) (viewABT e1')
            m2 <- go (viewABT e2) (viewABT e2')
            return (m1 && m2)
        Nothing   -> return False

    sConEq (CoerceTo_ _) (e1 :* End)
           (CoerceTo_ _) (e2 :* End) =
        case jmEq1 (typeOf e1) (typeOf e2) of
        Just Refl -> return True
        Nothing   -> return False

    sConEq (UnsafeFrom_ _) (e1 :* End)
           (UnsafeFrom_ _) (e2 :* End) =
        case jmEq1 (typeOf e1) (typeOf e2) of
        Just Refl -> return True
        Nothing   -> return False

    sConEq (PrimOp_ o1) es1
           (PrimOp_ o2) es2    = primOpEq o1 es1 o2 es2

    sConEq (ArrayOp_ o1) es1
           (ArrayOp_ o2) es2   = arrayOpEq o1 es1 o2 es2

    sConEq (MeasureOp_ o1) es1
           (MeasureOp_ o2) es2 = measureOpEq o1 es1 o2 es2

    sConEq Dirac e1
           Dirac e2            = sArgsEq e1 e2

    sConEq MBind (e1  :* e2  :* End)
           MBind (e1' :* e2' :* End) = do
        case jmEq1 (typeOf e1) (typeOf e1') of
        Just Refl -> do
            m1 <- go (viewABT e1) (viewABT e1')
            m2 <- go (viewABT e2) (viewABT e2')
            return (m1 && m2)
        Nothing   -> return False

    sConEq Plate     e1 Plate     e2    = sArgsEq e1 e2
    sConEq Chain     e1 Chain     e2    = sArgsEq e1 e2
    sConEq Integrate e1 Integrate e2    = sArgsEq e1 e2
    sConEq Summate   e1 Summate   e2    = sArgsEq e1 e2

    sConEq Expect (e1  :* e2  :* End)
           Expect (e1' :* e2' :* End) = do
        case jmEq1 (typeOf e1) (typeOf e1') of
        Just Refl -> do
            m1 <- go (viewABT e1) (viewABT e1')
            m2 <- go (viewABT e2) (viewABT e2')
            return (m1 && m2)
        Nothing   -> return False

    sConEq _ _ _ _ = return False


    primOpEq
        :: forall a typs1 typs2 args1 args2
        .  (typs1 ~ UnLCs args1, args1 ~ LCs typs1,
            typs2 ~ UnLCs args2, args2 ~ LCs typs2)
        => PrimOp typs1 a -> SArgs abt args1
        -> PrimOp typs2 a -> SArgs abt args2
        -> Reader Varmap Bool
    primOpEq p1 e1 p2 e2 =
        case jmEq2 p1 p2 of
        Just (Refl, Refl) -> sArgsEq e1 e2
        Nothing           -> return False

    arrayOpEq
        :: forall a typs1 typs2 args1 args2
        .  (typs1 ~ UnLCs args1, args1 ~ LCs typs1,
            typs2 ~ UnLCs args2, args2 ~ LCs typs2)
        => ArrayOp typs1 a -> SArgs abt args1
        -> ArrayOp typs2 a -> SArgs abt args2
        -> Reader Varmap Bool
    arrayOpEq p1 e1 p2 e2 =
        case jmEq2 p1 p2 of
        Just (Refl, Refl) -> sArgsEq e1 e2
        Nothing           -> return False

    measureOpEq
        :: forall a typs1 typs2 args1 args2
        . (typs1 ~ UnLCs args1, args1 ~ LCs typs1,
            typs2 ~ UnLCs args2, args2 ~ LCs typs2)
        => MeasureOp typs1 a -> SArgs abt args1
        -> MeasureOp typs2 a -> SArgs abt args2
        -> Reader Varmap Bool
    measureOpEq m1 e1 m2 e2 =
        case jmEq2 m1 m2 of
        Just (Refl,Refl) -> sArgsEq e1 e2
        Nothing          -> return False

    datumEq :: forall a
        .  Datum (abt '[]) a
        -> Datum (abt '[]) a
        -> Reader Varmap Bool
    datumEq (Datum _ _ d1) (Datum _ _ d2) = datumCodeEq d1 d2

    datumCodeEq
        :: forall xss a
        .  DatumCode xss (abt '[]) a
        -> DatumCode xss (abt '[]) a
        -> Reader Varmap Bool
    datumCodeEq (Inr c) (Inr d) = datumCodeEq c d
    datumCodeEq (Inl c) (Inl d) = datumStructEq c d
    datumCodeEq _       _       = return False

    datumStructEq
        :: forall xs a
        .  DatumStruct xs (abt '[]) a
        -> DatumStruct xs (abt '[]) a
        -> Reader Varmap Bool
    datumStructEq (Et c1 c2) (Et d1 d2) = do
        m  <- datumFunEq c1 d1
        ms <- datumStructEq c2 d2
        return (m && ms)
    datumStructEq Done       Done       = return True
    datumStructEq _          _          = return False
    
    datumFunEq
        :: forall x a
        .  DatumFun x (abt '[]) a
        -> DatumFun x (abt '[]) a
        -> Reader Varmap Bool
    datumFunEq (Konst e) (Konst f) = go (viewABT e) (viewABT f) 
    datumFunEq (Ident e) (Ident f) = go (viewABT e) (viewABT f) 
    datumFunEq _          _        = return False
    
    pairEq
        :: forall a b
        .  (abt '[] a, abt '[] b)
        -> (abt '[] a, abt '[] b)
        -> Reader Varmap Bool
    pairEq (x1, y1) (x2, y2) = do
        m1 <- go (viewABT x1) (viewABT x2)
        m2 <- go (viewABT y1) (viewABT y2)
        return (m1 && m2)

    sBranch
        :: forall a b
        .  Branch a abt b
        -> Branch a abt b
        -> Reader Varmap Bool
    sBranch (Branch _ e1) (Branch _ e2) = go (viewABT e1) (viewABT e2)
