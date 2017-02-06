{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE EmptyCase                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2017.02.01
-- |
-- Module      :  Language.Hakaru.Syntax.ANF
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :
-- Stability   :  experimental
-- Portability :  GHC-only
--
--
----------------------------------------------------------------
module Language.Hakaru.Syntax.ANF where

import Prelude hiding ((==), (+))
import qualified Data.IntMap                      as IM
import           Data.Maybe
import           Data.Number.Nat
import           Data.Sequence                    ((<|))
import qualified Data.Sequence                    as S

import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.Datum
import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Types.DataKind

import           Language.Hakaru.Syntax.Prelude

-- The renaming environment which maps variables in the original term to their
-- counterparts in the new term. This is needed since the mechanism which
-- ensures hygiene for the AST only factors in binders, but not free variables
-- in the expression being constructed. When we construct a new binding form, a
-- new variable is introduced and the variable in the old expression must be
-- mapped to the new one.

type Env = Assocs (Variable :: Hakaru -> *)

updateEnv :: forall (a :: Hakaru) . Variable a -> Variable a -> Env -> Env
updateEnv vin vout = insertAssoc (Assoc vin vout)

-- | The context in which A-normalization occurs. Represented as a continuation,
-- the context expects an expression of a particular type (usually a variable)
-- and produces a new expression as a result.
type Context abt a b = abt '[] a -> abt '[] b

-- | Extract a variable from an abt. This function is partial
getVar :: (ABT Term abt) => abt xs a -> Variable a
getVar abt = case viewABT abt of
               Var v -> v
               _     -> error "getVar: not given a variable"

-- | Useful function for generating fresh variables from an existing variable by
-- wrapping @binder@.
freshVar
  :: (ABT Term abt)
  => Variable a
  -> (Variable a -> abt xs b)
  -> abt (a ': xs) b
freshVar var f = binder (varHint var) (varType var) (f . getVar)

-- | Entry point for the normalization process. Initializes normalize' with the
-- empty context.
normalize
  :: (ABT Term abt)
  => abt '[] a
  -> abt '[] a
normalize abt = normalize' abt emptyAssocs id

normalize'
  :: (ABT Term abt)
  => abt '[] a
  -> Env
  -> Context abt a b
  -> abt '[] b
normalize' abt = caseVarSyn abt normalizeVar normalizeTerm

normalizeVar :: (ABT Term abt) => Variable a -> Env -> Context abt a b -> abt '[] b
normalizeVar v env ctxt = ctxt . var $ fromMaybe v (lookupAssoc v env)

isValue
  :: (ABT Term abt)
  => abt xs a
  -> Bool
isValue abt =
  case viewABT abt of
    Var{}  -> True
    Bind{} -> False
    Syn s  -> isValueTerm s
  where
    isValueTerm Literal_{}  = True
    isValueTerm Datum_{}    = True
    isValueTerm (Lam_ :$ _) = True
    isValueTerm _           = False

-- TODO: Probably need to implement Superpose_ and maybe Reject_
normalizeTerm
  :: (ABT Term abt)
  => Term abt a
  -> Env
  -> Context abt a b
  -> abt '[] b
normalizeTerm (NaryOp_ op args) = normalizeNaryOp op args
normalizeTerm (x :$ args)       = normalizeSCon x args
normalizeTerm (Case_ c bs)      = normalizeCase c bs
normalizeTerm (Datum_ d)        = normalizeDatum d
normalizeTerm (Array_ s b)      = normalizeArray s b
normalizeTerm term              = const ($ syn term)

normalizeArray
  :: (ABT Term abt)
  => abt '[] 'HNat
  -> abt '[ 'HNat ] a
  -> Env
  -> Context abt ('HArray a) b
  -> abt '[] b
normalizeArray size body env ctxt =
  normalizeName size env $ \size' ->
  caseBind body $ \v body' ->
  let body'' = normalizeBody body' v env
  in ctxt $ syn (Array_ size' body'')

normalizeDatum
  :: (ABT Term abt)
  => Datum (abt '[]) (HData' t)
  -> Env
  -> (abt '[] (HData' t) -> abt '[] r)
  -> abt '[] r
normalizeDatum d env ctxt = ctxt $ datum_ newdata
  where newdata = fmap11 (\x -> normalize' x env id) d

remapVar
  :: (ABT Term abt)
  => Variable a
  -> Env
  -> (Env -> abt xs b)
  -> abt (a ': xs) b
remapVar var env f = freshVar var $ \var' -> f (updateEnv var var' env)

normalizeCase
  :: forall a b c abt . (ABT Term abt)
  => abt '[] a
  -> [Branch a abt b]
  -> Env
  -> Context abt b c
  -> abt '[] c
normalizeCase cond bs env ctxt =
  normalizeName cond env $ \ cond' ->
    let -- TODO: How do we deal with pattern variables?
        {-normalizeBranch :: Branch a abt b -> Context abt b c -> Branch a abt c-}
        normalizeBranch :: forall d e f . Branch d abt e -> Context abt e f -> Branch d abt f
        normalizeBranch (Branch pat body) ctxt' =
          case pat of
            PWild -> Branch PWild (normalize' body env ctxt')
            PVar  -> caseBind body $ \v body' ->
                       Branch PVar (normalizeBodyWithCtxt body' v env ctxt')

            -- Minimum needed to match True and False
            PDatum _ (PInl PDone)        -> Branch pat (normalize' body env ctxt')
            PDatum _ (PInr (PInl PDone)) -> Branch pat (normalize' body env ctxt')
            _     -> error "normalizeBranch: pattern variables not implemented"

        simple :: Branch a abt b -> Bool
        simple (Branch pat body) =
          case pat of
            PWild                        -> isValue body
            PVar                         -> caseBind body $ \_ body' -> isValue body'
            PDatum _ (PInl PDone)        -> isValue body
            PDatum _ (PInr (PInl PDone)) -> isValue body

        branches :: forall d . Context abt b d -> [Branch a abt d]
        branches ctxt = map (flip normalizeBranch ctxt) bs

    -- A possible optimization is to push the context into each conditional,
    -- possibly opening up other optimizations at the cost of code growth.
    in if False -- all simple bs
       then syn $ Case_ cond' (branches ctxt)
       else ctxt $ syn $ Case_ cond' (branches id)

normalizeBody
  :: (ABT Term abt)
  => abt '[] b
  -> Variable a
  -> Env
  -> abt '[a] b
normalizeBody body vold env =
  freshVar vold $ \vnew -> normalize' body (updateEnv vold vnew env) id

normalizeBodyWithCtxt
  :: (ABT Term abt)
  => abt '[] a
  -> Variable b
  -> Env
  -> Context abt a c
  -> abt '[b] c
normalizeBodyWithCtxt body vold env ctxt =
  freshVar vold $ \vnew -> normalize' body (updateEnv vold vnew env) ctxt

normalizeName
  :: (ABT Term abt)
  => abt '[] a
  -> Env
  -> Context abt a b
  -> abt '[] b
normalizeName abt env ctxt = normalize' abt env giveName
  where
    giveName abt' | isValue abt' = ctxt abt'
                  | otherwise    = let_ abt' ctxt

normalizeNames
  :: (ABT Term abt)
  => S.Seq (abt '[] a)
  -> Env
  -> (S.Seq (abt '[] a) -> abt '[] b)
  -> abt '[] b
normalizeNames abts env = foldr f ($ S.empty) abts
  where
    f x acc ctxt = normalizeName x env $ \t -> acc (ctxt . (t <|))

normalizeNaryOp
  :: (ABT Term abt)
  => NaryOp a
  -> S.Seq (abt '[] a)
  -> Env
  -> Context abt a b
  -> abt '[] b
normalizeNaryOp op args env ctxt = normalizeNames args env (ctxt . syn . NaryOp_ op)

normalizeSCon
  :: (ABT Term abt)
  => SCon args a
  -> SArgs abt args
  -> Env
  -> Context abt a b
  -> abt '[] b

normalizeSCon Lam_ =
  \(body :* End) env ctxt -> caseBind body $
    \v body' ->
      let body'' = normalizeBody body' v env
      in ctxt $ syn (Lam_ :$ body'' :* End)

normalizeSCon Let_ =
  \(rhs :* body :* End) env ctxt -> caseBind body $
    \v body' ->
      normalize' rhs env $ \rhs' ->
      let mkbody v' = normalize' body' (updateEnv v v' env) ctxt
      in syn (Let_ :$ rhs' :* freshVar v mkbody :* End)

-- TODO: Remove code duplication between sum and product cases
normalizeSCon s@Summate{} =
  \(lo :* hi :* body :* End) env ctxt ->
    normalizeName lo env $ \lo' ->
    normalizeName hi env $ \hi' ->
    caseBind body $ \v body' ->
    let body'' = normalizeBody body' v env
    in ctxt $ syn (s :$ lo' :* hi' :* body'' :* End)

normalizeSCon p@Product{} =
  \(lo :* hi :* body :* End) env ctxt ->
    normalizeName lo env $ \lo' ->
    normalizeName hi env $ \hi' ->
    caseBind body $ \v body' ->
    let body'' = normalizeBody body' v env
    in ctxt $ syn (p :$ lo' :* hi' :* body'' :* End)

normalizeSCon MBind =
  \(ma :* b :* End) env ctxt ->
    normalize' ma env $ \ma' ->
    caseBind b $ \v b' ->
    let b'' = normalizeBody b' v env
    in ctxt $ syn (MBind :$ ma' :* b'' :* End)

normalizeSCon Plate =
  \(e :* b :* End) env ctxt ->
    normalize' e env $ \e' ->
    caseBind b $ \v b' ->
    let b'' = normalizeBody b' v env
    in ctxt $ syn (Plate :$ e' :* b'' :* End)

normalizeSCon Dirac =
  \(e :* End) env ctxt -> normalize' e env (ctxt . dirac)

normalizeSCon (UnsafeFrom_ c) =
  \(t :* End) env ctxt -> normalize' t env (ctxt . unsafeFrom_ c)

normalizeSCon (CoerceTo_ c) =
  \(t :* End) env ctxt -> normalize' t env (ctxt . coerceTo_ c)

normalizeSCon (MeasureOp_ op) = normalizeMeasureOp op

normalizeSCon (ArrayOp_ op) = normalizeArrayOp op
normalizeSCon (PrimOp_ op)  = normalizePrimOp op
normalizeSCon op            = error $ "not implemented: normalizeSCon{" ++ show op ++ "}"

normalizeArrayOp
  :: (ABT Term abt, args ~ LCs typs)
  => ArrayOp typs a
  -> SArgs abt args
  -> Env
  -> Context abt a b
  -> abt '[] b
normalizeArrayOp op xs env ctxt =
  case (op, xs) of
    (Size _   ,           x :* End) -> normalizeOp1 (arrayOp1_ op) x env ctxt
    (Index _  ,      x :* y :* End) -> normalizeOp2 (arrayOp2_ op) x y env ctxt
    (Reduce _ , x :* y :* z :* End) -> normalizeOp3 (arrayOp3_ op) x y z env ctxt

normalizePrimOp
  :: (ABT Term abt, args ~ LCs typs)
  => PrimOp typs a
  -> SArgs abt args
  -> Env
  -> Context abt a b
  -> abt '[] b
normalizePrimOp op xs env ctxt =
  case (op, xs) of
    -- Logical operatons
    (Not  ,      x :* End) -> normalizeOp1 (primOp1_ op) x env ctxt
    (Impl , x :* y :* End) -> normalizeOp2 (primOp2_ op) x y env ctxt
    (Diff , x :* y :* End) -> normalizeOp2 (primOp2_ op) x y env ctxt
    (Nand , x :* y :* End) -> normalizeOp2 (primOp2_ op) x y env ctxt
    (Nor  , x :* y :* End) -> normalizeOp2 (primOp2_ op) x y env ctxt

    -- Trig stuff
    (Pi    ,      End) -> ctxt $ primOp0_ Pi
    (Sin   , x :* End) -> normalizeOp1 (primOp1_ op) x env ctxt
    (Cos   , x :* End) -> normalizeOp1 (primOp1_ op) x env ctxt
    (Tan   , x :* End) -> normalizeOp1 (primOp1_ op) x env ctxt
    (Asin  , x :* End) -> normalizeOp1 (primOp1_ op) x env ctxt
    (Acos  , x :* End) -> normalizeOp1 (primOp1_ op) x env ctxt
    (Atan  , x :* End) -> normalizeOp1 (primOp1_ op) x env ctxt
    (Sinh  , x :* End) -> normalizeOp1 (primOp1_ op) x env ctxt
    (Cosh  , x :* End) -> normalizeOp1 (primOp1_ op) x env ctxt
    (Tanh  , x :* End) -> normalizeOp1 (primOp1_ op) x env ctxt
    (Asinh , x :* End) -> normalizeOp1 (primOp1_ op) x env ctxt
    (Acosh , x :* End) -> normalizeOp1 (primOp1_ op) x env ctxt
    (Atanh , x :* End) -> normalizeOp1 (primOp1_ op) x env ctxt

    (RealPow    , x :* y :* End) -> normalizeOp2 (primOp2_ op) x y env ctxt
    (Exp        ,      x :* End) -> normalizeOp1 (primOp1_ op) x env ctxt
    (Log        ,      x :* End) -> normalizeOp1 (primOp1_ op) x env ctxt
    (Infinity _ ,           End) -> ctxt $ primOp0_ op
    (GammaFunc  ,      x :* End) -> normalizeOp1 (primOp1_ op) x env ctxt
    (BetaFunc   , x :* y :* End) -> normalizeOp2 (primOp2_ op) x y env ctxt

    -- Comparisons
    (Equal _ , x :* y :* End) -> normalizeOp2 (primOp2_ op) x y env ctxt
    (Less _  , x :* y :* End) -> normalizeOp2 (primOp2_ op) x y env ctxt

    -- HSemiring operations
    (NatPow _ , x :* y :* End) -> normalizeOp2 (primOp2_ op) x y env ctxt

    -- HRing operations
    (Negate _  ,      x :* End) -> normalizeOp1 (primOp1_ op) x env ctxt
    (Abs _     ,      x :* End) -> normalizeOp1 (primOp1_ op) x env ctxt
    (Signum _  ,      x :* End) -> normalizeOp1 (primOp1_ op) x env ctxt
    (Recip _   ,      x :* End) -> normalizeOp1 (primOp1_ op) x env ctxt
    (NatRoot _ , x :* y :* End) -> normalizeOp2 (primOp2_ op) x y env ctxt
    (Erf _     ,      x :* End) -> normalizeOp1 (primOp1_ op) x env ctxt

normalizeOp1
  :: (ABT Term abt)
  => (abt '[] a -> t)
  -> abt '[] a
  -> Env
  -> (t -> abt '[] c)
  -> abt '[] c
normalizeOp1 mk x env ctxt = normalizeName x env (ctxt . mk)

normalizeOp2
  :: (ABT Term abt)
  => (abt '[] a -> abt '[] b -> t)
  -> abt '[] a
  -> abt '[] b
  -> Env
  -> (t -> abt '[] c)
  -> abt '[] c
normalizeOp2 mk x y env ctxt =
  normalizeName x env $ \x' ->
  normalizeName y env $ \y' ->
  ctxt (mk x' y')

normalizeOp3
  :: (ABT Term abt)
  => (abt '[] a -> abt '[] b -> abt '[] c -> t)
  -> abt '[] a
  -> abt '[] b
  -> abt '[] c
  -> Env
  -> (t -> abt '[] d)
  -> abt '[] d
normalizeOp3 mk x y z env ctxt =
  normalizeName x env $ \x' ->
  normalizeName y env $ \y' ->
  normalizeName z env $ \z' ->
  ctxt (mk x' y' z')

normalizeMeasureOp
  :: (ABT Term abt, args ~ LCs typs)
  => MeasureOp typs a
  -> SArgs abt args
  -> Env
  -> Context abt ('HMeasure a) b
  -> abt '[] b
normalizeMeasureOp op xs env ctxt =
  case (op, xs) of
    (Lebesgue    ,           End) -> ctxt $ measure0_ op
    (Counting    ,           End) -> ctxt $ measure0_ op
    (Categorical ,      x :* End) -> normalizeName x env (ctxt . measure1_ op)
    (Poisson     ,      x :* End) -> normalizeName x env (ctxt . measure1_ op)
    (Uniform     , x :* y :* End) -> normalizeOp2 (measure2_ op) x y env ctxt
    (Normal      , x :* y :* End) -> normalizeOp2 (measure2_ op) x y env ctxt
    (Gamma       , x :* y :* End) -> normalizeOp2 (measure2_ op) x y env ctxt
    (Beta        , x :* y :* End) -> normalizeOp2 (measure2_ op) x y env ctxt

