{-# LANGUAGE GADTs
           , KindSignatures
           , DataKinds
           , TypeOperators
           , NoImplicitPrelude
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.07.05
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

import Prelude (($), (.), id, flip, error, Maybe(..))
import Data.Sequence         (Seq)
import Data.IntMap           (IntMap)
import qualified Data.IntMap as IM

import Language.Hakaru.Syntax.Nat      (fromNat)
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.TypeEq
import Language.Hakaru.Syntax.HClasses
import Language.Hakaru.Syntax.Coercion
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
-- TODO: factor out all the trivial constructors, separating them from ExpectFun and ExpectMeasure
{-
type family   IsTrivialExpect (a :: Hakaru) :: Bool
type instance IsTrivialExpect (unused :: Hakaru) where
    IsTrivialExpect (a ':-> b)    = 'False
    IsTrivialExpect ('HMeasure a) = 'False
    IsTrivialExpect a             = 'True

type TrivialExpect a = IsTrivialExpect a ~ 'True
-}

-- TODO: we accidentally rediscovered NBE (for functions). Should we do NBE for the \"trivial\" types too? That cuts to the chase of needing an interpreter for 'Case_'... (of course, NBE doesn't work so well for open terms...) Or maybe we should just NBE things away before calling 'expect'?
-- We can't do this as a type family, because that causes ambiguity issues due to the @abt@ being parametric (but we have no way of explaining that to type families).
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

-- TODO: a general function for converting Expect back into plain
-- Haskell functions; we could call it \"expectify\", to pun on the
-- reify\/reflect of NBE. We may need to define a type family that
-- mirrors the Expect datatype, and then enable -XAllowAmbiguousTypes
-- to be able to use it...

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


-- | Reflect a term into it's expectation semantics. In particular,
-- this function handles variables; everything else is handed off
-- to the 'expectAST' or 'expectSing' helper functions.
expect_ :: (ABT abt) => abt a -> Env abt -> Expect abt a
expect_ e xs =
    flip (caseVarSyn e)
        (`expectAST` xs)
        $ \x a ->
            case IM.lookup (fromNat $ varID x) xs of
            Nothing       -> error "expect: unbound variable"
            Just (V _ e') ->
                let b = getSing e' in
                case jmEq a b of
                Nothing   -> error "expect: ill-typed environment"
                Just Refl -> expectSing b e' xs


-- | A singleton-directed variant of 'expect_'. This function just
-- does the bare minimum necessary for wrapping an @abt@ up in
-- 'Expect'. In particular, the environment is only ever used if
-- the term's type is an @n@-ary function (including where @n=0@)
-- returning a measure.
expectSing :: (ABT abt) => Sing a -> abt a -> Env abt -> Expect abt a
expectSing SNat         e _  = ExpectNat   e
expectSing SInt         e _  = ExpectInt   e
expectSing SProb        e _  = ExpectProb  e
expectSing SReal        e _  = ExpectReal  e
expectSing (SData  _ _) e _  = ExpectData  e
expectSing (SArray   _) e _  = ExpectArray e
expectSing (SFun   _ s) e xs = ExpectFun $ \x -> expectSing s (e `app` x) xs
expectSing (SMeasure _) e xs = expect_ e xs


expectAST :: (ABT abt) => AST abt a -> Env abt -> Expect abt a
expectAST (Lam_ e1) xs =
    ExpectFun $ \e2 ->
    caseBind e1 $ \x e' ->
    expect_ e' $ pushEnv (V x e2) xs

expectAST (App_ e1 e2) xs =
    expect_ e1 xs `apF` e2

expectAST (Let_ e1 e2) xs =
    caseBind e2 $ \x e' ->
    expect_ e' $ pushEnv (V x e1) xs

expectAST (Fix_ e1) xs =
    caseBind e1 $ \x e' ->
    expect_ e' $ pushEnv (V x e1) xs -- BUG: looping?

expectAST (Ann_        _ e)   xs = expect_ e xs
expectAST (PrimOp_     o)     xs =
    expectSing (sing_PrimOp o) (syn $ PrimOp_ o) xs
    -- TODO: we should beware of 'Index' and 'Reduce'. They may need evaluating if they happen to return functions or measures

expectAST (NaryOp_     o es)  xs =
    expectSing (sing_NaryOp o) (syn $ NaryOp_ o es) xs

expectAST (Value_      v)     xs = expectSing (sing_Value v) (value_ v) xs
expectAST (CoerceTo_   c  e)  xs = expectCoerceTo   c $ expect_ e xs
expectAST (UnsafeFrom_ c  e)  xs = expectUnsafeFrom c $ expect_ e xs
expectAST Empty_              _  = ExpectArray . syn $ Empty_
expectAST (Array_      e1 e2) _  = ExpectArray . syn $ Array_ e1 e2
expectAST (Datum_      d)     _  = ExpectData $ datum_ d
expectAST (Case_       e  bs) xs = error "TODO: expect{Case_}" -- use 'isBind' to capture the easy cases at least
expectAST (Measure_    o)     _  = expectMeasure o
expectAST (Bind_       e1 e2) xs =
    ExpectMeasure $ \c ->
    caseBind e2 $ \x e' ->
    expect_ e1 xs `apM` \a ->
    (expect_ e' $ pushEnv (V x a) xs) `apM` c
expectAST (Superpose_ pms) xs =
    ExpectMeasure $ \c ->
    sum [ p * (expect_ m xs `apM` c) | (p, m) <- pms ]


expectMeasure :: (ABT abt) => Measure a -> Expect abt a
expectMeasure (Dirac _) =
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
expectMeasure (DirichletProcess _) =
    ExpectFun $ \p ->
    ExpectFun $ \m ->
    ExpectMeasure $ \c ->
    error "TODO: expectMeasure{DirichletProcess}"
expectMeasure (Plate _) =
    ExpectFun $ \ms ->
    ExpectMeasure $ \c -> 
    error "TODO: expectMeasure{Plate}"
expectMeasure (Chain _ _) =
    ExpectFun $ \mz ->
    ExpectFun $ \s0 ->
    ExpectMeasure $ \c ->
    error "TODO: expectMeasure{Chain}"



-- TODO: how to avoid all this boilerplate?
expectCoerceTo :: (ABT abt) => Coercion a b -> Expect abt a -> Expect abt b
expectCoerceTo IdCoercion           = id
expectCoerceTo (ConsCoercion c1 c2) =
    expectCoerceTo c2 . expectPrimCoerceTo c1


expectPrimCoerceTo
    :: (ABT abt) => PrimCoercion a b -> Expect abt a -> Expect abt b
expectPrimCoerceTo (Signed HRing_Int) (ExpectNat e) =
    ExpectInt $ coerceTo_ (singletonCoercion $ Signed HRing_Int) e
expectPrimCoerceTo (Signed HRing_Real) (ExpectProb e) =
    ExpectReal $ coerceTo_ (singletonCoercion $ Signed HRing_Real) e
expectPrimCoerceTo (Continuous HContinuous_Prob) (ExpectNat e) =
    ExpectProb $ coerceTo_
        (singletonCoercion $ Continuous HContinuous_Prob) e
expectPrimCoerceTo (Continuous HContinuous_Real) (ExpectInt e) =
    ExpectReal $ coerceTo_
        (singletonCoercion $ Continuous HContinuous_Real) e
expectPrimCoerceTo _ _ = error "expectPrimCoerceTo: the impossible happened"


expectUnsafeFrom
    :: (ABT abt) => Coercion a b -> Expect abt b -> Expect abt a
expectUnsafeFrom IdCoercion           = id
expectUnsafeFrom (ConsCoercion c1 c2) =
    expectPrimUnsafeFrom c1 . expectUnsafeFrom c2


expectPrimUnsafeFrom
    :: (ABT abt) => PrimCoercion a b -> Expect abt b -> Expect abt a
expectPrimUnsafeFrom (Signed HRing_Int) (ExpectInt e) =
    ExpectNat $ unsafeFrom_ (singletonCoercion $ Signed HRing_Int) e
expectPrimUnsafeFrom (Signed HRing_Real) (ExpectReal e) =
    ExpectProb $ unsafeFrom_ (singletonCoercion $ Signed HRing_Real) e
expectPrimUnsafeFrom (Continuous HContinuous_Prob) (ExpectProb e) =
    ExpectNat $ unsafeFrom_
        (singletonCoercion $ Continuous HContinuous_Prob) e
expectPrimUnsafeFrom (Continuous HContinuous_Real) (ExpectReal e) =
    ExpectInt $ unsafeFrom_
        (singletonCoercion $ Continuous HContinuous_Real) e
expectPrimUnsafeFrom _ _ = error "expectPrimCoerceTo: the impossible happened"

----------------------------------------------------------------
----------------------------------------------------------- fin.
