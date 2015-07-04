{-# LANGUAGE GADTs
           , KindSignatures
           , DataKinds
           , TypeOperators
           , NoImplicitPrelude
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.07.02
-- |
-- Module      :  Language.Hakaru.Syntax.Expect
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- This is a fork of "Language.Hakaru.Expect" to work with our new
-- AST. This module shouldn't actually be called
-- "Language.Hakaru.Syntax.Expect"; it should keep the old name,
-- once we switch everything over to using the new AST.
----------------------------------------------------------------
module Language.Hakaru.Syntax.Expect
    ( normalize
    , total
    , expect
    ) where

import Prelude (($), (.), flip, error, Maybe(..))
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM

import Language.Hakaru.Syntax.Nat      (fromNat)
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.TypeEq
import Language.Hakaru.Syntax.Coercion (signed)
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.Prelude

----------------------------------------------------------------

normalize :: (ABT abt) => abt ('HMeasure a) -> abt ('HMeasure a)
normalize m = superpose [(recip (total m), m)]

total :: (ABT abt) => abt ('HMeasure a) -> abt 'HProb
total m = expect m $ \_ -> prob_ 1

expect
    :: (ABT abt)
    => abt ('HMeasure a)
    -> (abt a -> abt 'HProb) -> abt 'HProb
expect e = apM $ expect_ e IM.empty


----------------------------------------------------------------
-- We can't do this as a type family, because that cause ambiguity issues
data Expect :: (Hakaru -> *) -> Hakaru -> * where
    ExpectNat   :: abt 'HNat               -> Expect abt 'HNat
    ExpectInt   :: abt 'HInt               -> Expect abt 'HInt
    ExpectProb  :: abt 'HProb              -> Expect abt 'HProb
    ExpectReal  :: abt 'HReal              -> Expect abt 'HReal
    ExpectArray :: abt ('HArray a)         -> Expect abt ('HArray a)
    ExpectData  :: abt ('HData t xss)      -> Expect abt ('HData t xss)
    ExpectFun   :: (abt a -> Expect abt b) -> Expect abt (a ':-> b)
    ExpectMeasure
        :: ((abt a -> abt 'HProb) -> abt 'HProb)
        -> Expect abt ('HMeasure a)

-- TODO: a general function for converting Expect back into plain Haskell functions. We may need to define a type family that mirrors the Expect datatype, and then enable -XAllowAmbiguousTypes to be able to use it...

apF :: Expect abt (a ':-> b) -> abt a -> Expect abt b
apF (ExpectFun f) x = f x

apM :: Expect abt ('HMeasure a) -> (abt a -> abt 'HProb) -> abt 'HProb
apM (ExpectMeasure f) c = f c


data V :: (Hakaru -> *) -> * where
    V :: {-# UNPACK #-} !Variable -> abt a -> V abt
    -- TODO: store the @Expect abt a@ instead?

type Env abt = IntMap (V abt)

pushEnv :: V abt -> Env abt -> Env abt
pushEnv v@(V x _) = IM.insert (fromNat $ varID x) v

getSing :: (ABT abt) => abt a -> Sing a
getSing _ = error "TODO: get singletons of anything after typechecking"


expect_ :: (ABT abt) => abt a -> Env abt -> Expect abt a
expect_ e xs =
    flip (caseVarSynABT e)
        (`expectAST` xs)
        $ \x a ->
            case IM.lookup (fromNat $ varID x) xs of
            Nothing       -> error "expect: unbound variable"
            Just (V _ e') ->
                let b = getSing e' in
                case jmEq a b of
                Nothing   -> error "expect: ill-typed environment"
                Just Refl -> expectify b e' xs


expectify :: (ABT abt) => Sing a -> abt a -> Env abt -> Expect abt a
expectify SNat         e _  = ExpectNat   e
expectify SInt         e _  = ExpectInt   e
expectify SProb        e _  = ExpectProb  e
expectify SReal        e _  = ExpectReal  e
expectify (SData  _ _) e _  = ExpectData  e
expectify (SArray   _) e _  = ExpectArray e
expectify (SFun   _ s) e xs = ExpectFun $ \x -> expectify s (e `app` x) xs
expectify (SMeasure _) e xs = expect_ e xs


expectAST :: (ABT abt) => AST abt a -> Env abt -> Expect abt a
expectAST (Lam_ _ e1) xs =
    ExpectFun $ \e2 ->
    caseOpenABT e1 $ \x e' ->
    expect_ e' $ pushEnv (V x e2) xs

expectAST (App_ e1 e2) xs =
    expect_ e1 xs `apF` e2

expectAST (Let_ e1 e2) xs =
    caseOpenABT e2 $ \x e' ->
    expect_ e' $ pushEnv (V x e1) xs

expectAST (Fix_ e1) xs =
    caseOpenABT e1 $ \x e' ->
    expect_ e' $ pushEnv (V x e1) xs -- BUG: looping?

expectAST (Ann_    _ e)  xs = expect_ e xs
expectAST (PrimOp_ o)    _  = expectPrimOp o
expectAST (NaryOp_ o es) xs = error "TODO: expect{NaryOp_}"
expectAST (Value_  v)    _  =
    case v of
    VNat   _ -> ExpectNat  $ value_ v
    VInt   _ -> ExpectInt  $ value_ v
    VProb  _ -> ExpectProb $ value_ v
    VReal  _ -> ExpectReal $ value_ v
    VDatum _ -> ExpectData $ value_ v

expectAST (CoerceTo_   c  e ) xs = error "TODO: expect{CoerceTo_}"
expectAST (UnsafeFrom_ c  e ) xs = error "TODO: expect{UnsafeFrom_}"
expectAST Empty_                 = ExpectArray . syn $ Empty_
expectAST (Array_      e1 e2) _  = ExpectArray . syn $ Array_ e1 e2
expectAST (Datum_      d)     _  = ExpectData $ datum_ d
expectAST (Case_       e  bs) xs = error "TODO: expect{Case_}"
expectAST (Measure_    o)     _  = expectMeasure o
expectAST (Bind_       e1 e2) xs =
    ExpectMeasure $ \c ->
    caseOpenABT e2 $ \x e' ->
    expect_ e1 xs `apM` \a ->
    (expect_ e' $ pushEnv (V x a) xs) `apM` c
expectAST (Superpose_ pms) xs =
    ExpectMeasure $ \c ->
    sum [ p * (expect_ m xs `apM` c) | (p, m) <- pms ]


-- BUG: something about can't deduce (Expect abt0 a ~ Expect abt a); we can get rid of that with -XAllowAmbiguousTypes
expectMeasure :: (ABT abt) => Measure a -> Expect abt a
expectMeasure Dirac       =
    ExpectFun $ \a ->
    ExpectMeasure $ \c -> c a
expectMeasure Lebesgue    =
    ExpectMeasure $ \c ->
    integrate negativeInfinity infinity c
expectMeasure Counting    =
    ExpectMeasure $ \c ->
    summate   negativeInfinity infinity c
expectMeasure Categorical =
    ExpectFun $ \ps ->
    ExpectMeasure $ \c -> 
    error "TODO: expectMeasure{Categorical}"
    {-
    let_ (summateV ps) $ \tot ->
    flip (if_ (0 < tot)) 0
        $ summateV (mapWithIndex (\i p -> p * c i) ps) / tot
    -}
expectMeasure Uniform =
    ExpectFun $ \lo ->
    ExpectFun $ \hi ->
    ExpectMeasure $ \c -> 
    integrate lo hi $ \x ->
        c x / unsafeProb (hi - lo)
expectMeasure Normal =
    ExpectFun $ \mu ->
    ExpectFun $ \sd ->
    ExpectMeasure $ \c -> 
    integrate negativeInfinity infinity $ \x ->
        exp (negate ((x - mu) ^ nat_ 2)
            / fromProb (prob_ 2 * sd ** real_ 2))
        / sd / sqrt (prob_ 2 * pi) * c x
expectMeasure Poisson =
    ExpectFun $ \l ->
    ExpectMeasure $ \c ->
    flip (if_ (prob_ 0 < l)) (prob_ 0)
        $ summate (real_ 0) infinity $ \x ->
            l ** fromInt x
            / gammaFunc (fromInt x + real_ 1)
            / exp (fromProb l)
            * c (unsafeFrom_ signed x)
expectMeasure Gamma =
    ExpectFun $ \shape ->
    ExpectFun $ \scale ->
    ExpectMeasure $ \c ->
    integrate (real_ 0) infinity $ \x ->
        let x_ = unsafeProb x in 
        x_ ** (fromProb shape - real_ 1)
        * exp (negate . fromProb $ x_ / scale)
        / (scale ** shape * gammaFunc shape)
        * c x_
expectMeasure Beta =
    ExpectFun $ \a ->
    ExpectFun $ \b ->
    ExpectMeasure $ \c ->
    integrate (real_ 0) (real_ 1) $ \x ->
        let x_ = unsafeProb x in 
        x_ ** (fromProb a - real_ 1)
        * (unsafeProb (real_ 1 - x) ** (fromProb b - real_ 1))
        / betaFunc a b * c (unsafeProb x)
expectMeasure DirichletProcess =
    ExpectFun $ \p ->
    ExpectFun $ \m ->
    ExpectMeasure $ \c ->
    error "TODO: expectMeasure{DirichletProcess}"
expectMeasure Plate =
    ExpectFun $ \ms ->
    ExpectMeasure $ \c -> 
    error "TODO: expectMeasure{Plate}"
expectMeasure Chain =
    ExpectFun $ \mz ->
    ExpectFun $ \s0 ->
    ExpectMeasure $ \c ->
    error "TODO: expectMeasure{Chain}"


expectFun1 :: (s -> Expect abt b) -> (abt a -> s) -> Expect abt (a ':-> b)
expectFun1 h f =
    ExpectFun $ \x ->
    h $ f x

expectFun2
    :: (s -> Expect abt c)
    -> (abt a -> abt b -> s)
    -> Expect abt (a ':-> b ':-> c)
expectFun2 h f =
    ExpectFun $ \x ->
    ExpectFun $ \y ->
    h $ f x y

expectFun3
    :: (s -> Expect abt d)
    -> (abt a -> abt b -> abt c -> s)
    -> Expect abt (a ':-> b ':-> c ':-> d)
expectFun3 h f =
    ExpectFun $ \x ->
    ExpectFun $ \y ->
    ExpectFun $ \z ->
    h $ f x y z

expectPrimOp :: (ABT abt) => PrimOp a -> Expect abt a
expectPrimOp Not       = expectFun1 ExpectData not
expectPrimOp Impl      = expectFun2 ExpectData $ primOp2_ Impl
expectPrimOp Diff      = expectFun2 ExpectData $ primOp2_ Diff
expectPrimOp Nand      = expectFun2 ExpectData nand
expectPrimOp Nor       = expectFun2 ExpectData nor
expectPrimOp Pi        = ExpectProb pi
expectPrimOp Sin       = expectFun1 ExpectReal sin
expectPrimOp Cos       = expectFun1 ExpectReal cos
expectPrimOp Tan       = expectFun1 ExpectReal tan
expectPrimOp Asin      = expectFun1 ExpectReal asin
expectPrimOp Acos      = expectFun1 ExpectReal acos
expectPrimOp Atan      = expectFun1 ExpectReal atan
expectPrimOp Sinh      = expectFun1 ExpectReal sinh
expectPrimOp Cosh      = expectFun1 ExpectReal cosh
expectPrimOp Tanh      = expectFun1 ExpectReal tanh
expectPrimOp Asinh     = expectFun1 ExpectReal asinh
expectPrimOp Acosh     = expectFun1 ExpectReal acosh
expectPrimOp Atanh     = expectFun1 ExpectReal atanh
expectPrimOp RealPow   = expectFun2 ExpectProb (**)
expectPrimOp Exp       = expectFun1 ExpectProb exp
expectPrimOp Log       = expectFun1 ExpectReal log
expectPrimOp Infinity         = ExpectProb infinity
expectPrimOp NegativeInfinity = ExpectReal negativeInfinity
expectPrimOp GammaFunc = expectFun1 ExpectProb gammaFunc
expectPrimOp BetaFunc  = expectFun2 ExpectProb betaFunc
expectPrimOp Integrate = expectFun3 ExpectProb $ primOp3_ Integrate
expectPrimOp Summate   = expectFun3 ExpectProb $ primOp3_ Summate
expectPrimOp Index     = error "TODO: expectPrimOp{Index}" -- The lookup could return an HMeasure or a (':->)...
expectPrimOp Size      = expectFun1 ExpectNat size
expectPrimOp Reduce    = error "TODO: expectPrimOp{Reduce}" -- Not sure why this one doesn't typecheck
expectPrimOp Less      = expectFun2 ExpectData (<)
expectPrimOp Equal     = expectFun2 ExpectData (==)
expectPrimOp NatPow    = error "TODO: expectPrimOp{NatPow}" -- Need to prove the first argument can't be an HMeasure or HFun before we can use (^)
expectPrimOp Negate    = error "TODO: expectPrimOp{Negate}" -- Need to prove the argument can't be an HMeasure or HFun before we can use 'negate'
expectPrimOp Abs       = error "TODO: expectPrimOp{Abs}" -- Need to prove the argument can't be an HMeasure or HFun before we can use 'abs_'
expectPrimOp Signum    = error "TODO: expectPrimOp{Signum}" -- Need to prove the argument can't be an HMeasure or HFun before we can use 'signum'
expectPrimOp Recip     = error "TODO: expectPrimOp{Recip}" -- Need to prove the argument can't be an HMeasure or HFun before we can use 'recip'
expectPrimOp NatRoot   = error "TODO: expectPrimOp{NatRoot}" -- Need to prove the argument can't be an HMeasure or HFun before we can use @primOp2_ NatRoot@
expectPrimOp Erf       = error "TODO: expectPrimOp{Erf}" -- Need to prove the argument can't be an HMeasure or HFun before we can use 'erf'

{-
expectNaryOp :: (ABT abt) => NaryOp a -> Expect abt _
expectNaryOp And  = _
expectNaryOp Or   = _
expectNaryOp Xor  = _
expectNaryOp Iff  = _
expectNaryOp Min  = _
expectNaryOp Max  = _
expectNaryOp Sum  = _
expectNaryOp Prod = _
-}

----------------------------------------------------------------
----------------------------------------------------------- fin.