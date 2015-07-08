{-# LANGUAGE GADTs
           , KindSignatures
           , DataKinds
           , TypeOperators
           , NoImplicitPrelude
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.07.07
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

import           Prelude (($), (.), id, flip, error, Maybe(..), Either(..))
import           Data.IntMap   (IntMap)
import qualified Data.IntMap   as IM

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
expect e = apM $ expectSynDir e IM.empty


----------------------------------------------------------------
-- We can't do this as a type family, because that causes ambiguity
-- issues due to the @abt@ being parametric (but we have no way of
-- explaining that to type families). cf., -XAllowAmbiguousTypes
--
-- TODO: only partially interpret things (functions, arrays), doing so lazily as needed.
--
-- | @Expect abt a@ gives the expectation-semantic interpretation
-- of @abt a@. The only \"real\" change is interpreting measures
-- as linear functionals; all the other interpretations are just
-- for performing normalization-by-evaluation in order to construct
-- that linear functional.
data Expect :: (Hakaru -> *) -> Hakaru -> * where
    -- We don't bother interpreting primitive numeric types.
    ExpectNat  :: abt 'HNat  -> Expect abt 'HNat
    ExpectInt  :: abt 'HInt  -> Expect abt 'HInt
    ExpectProb :: abt 'HProb -> Expect abt 'HProb
    ExpectReal :: abt 'HReal -> Expect abt 'HReal

    -- We have to interpret arrays so we can evaluate 'Index' and
    -- 'Reduce' as needed.
    ExpectArray
        :: abt 'HNat
        -> (abt 'HNat -> Expect abt a)
        -> Expect abt ('HArray a)

    -- TODO: actually interpret 'HData', so we can evaluate 'Case_'
    ExpectData
        :: abt ('HData t xss)
        -> Expect abt ('HData t xss)

    -- We have to interpret functions so we can (easily) interpret
    -- our parameterized measures. This interpretation allows us
    -- to evaluate 'App_' as needed.
    ExpectFun
        :: (abt a -> Expect abt b)
        -> Expect abt (a ':-> b)

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


data Assoc :: (Hakaru -> *) -> * where
    Assoc :: {-# UNPACK #-} !(Variable a) -> abt a -> Assoc abt
    -- TODO: store the @Expect abt a@ instead?
    -- TODO: have two different versions of variable lookup; one for when we need to take the expectation of the variable, and one for just plugging things into place.

type Env abt = IntMap (Assoc abt)

pushEnv :: Assoc abt -> Env abt -> Env abt
pushEnv v@(Assoc x _) = IM.insert (fromNat $ varID x) v

getSing :: (ABT abt) => abt a -> Sing a
getSing _ = error "TODO: get singletons of anything after typechecking"


-- TODO: Move this to ABT.hs
-- TODO: Swap the argument order?
-- TODO: use a proper exception\/error monad; like 'Either'.
-- TODO: Remove the 'getSing' requirement by storing singletons in
-- the environment? If so, then should we return @Maybe (Sing a)@
-- as well? (a) That will let us know whether we had to perform
-- variable lookups along the way, and so prevents losing information;
-- (b) we can't just return @Sing a@ because doing so would require
-- taking a @Sing a@ input, and if we had that already then there's
-- no point in returning it...
--
-- | Perform recursive variable lookups until we can finally return
-- some syntax.
resolveVar
    :: (ABT abt)
    => abt a
    -> Env abt
    -> Either (Variable a) (AST abt a)
resolveVar e xs =
    flip (caseVarSyn e) Right $ \x ->
        case IM.lookup (fromNat $ varID x) xs of
        Just (Assoc x' e') ->
            case varEq x x' of
            Just Refl -> resolveVar e' xs
            Nothing   -> error "resolveVar: ill-formed environment"
        Nothing       -> Left x
            -- error "resolveVar: unbound variable"
            -- error "TODO: replace the variable with a new variable of a different type (i.e., of the appropriate type); or, wrap the variable with a (Hakaru-)call to (Hakaru-)'expect'"
            -- TODO: make sure that @lam$\t -> total (factor t)@ works

-- TODO: if we really do have 'getSing', then we can call it in
-- 'expect' and jump directly to 'expectTypeDir'; then we could
-- probably find a way to thread singletons through in order to
-- combine 'expectSynDir' and 'expectTypeDir' into a single function.
--
-- TODO: when should we switch back and forth between 'expectSynDir'
-- and 'expectTypeDir'? The old version of 'expectSynDir' switched
-- to 'expectTypeDir' whenever it had looked up a variable; is that
-- what we want?
--
-- | Perform a syntax-directed reflection of a term into it's
-- expectation semantics. This function will perform whatever
-- evaluation it needs to in order to expose the things being
-- reflected.
expectSynDir :: (ABT abt) => abt a -> Env abt -> Expect abt a
expectSynDir e xs =
    case resolveVar e xs of
    Left  x -> error "TODO" -- App_ (syn . PrimOp_ . Expect $ varType x) (var x)
    Right t -> expectAST t xs



-- | Perform a type-directed reflection of a term into it's expectation
-- semantics. This function does the bare minimum necessary for
-- wrapping up an @abt@ into 'Expect'; thus, it will build up a
-- larger term from the @abt a@ argument, without looking inside
-- it (whenever possible). Only only when absolutely necessary, do
-- we fall back to the syntax-directed 'expectSynDir'. \"Absolutely
-- necessary\" is when we have an @n@-ary function returning a
-- measure (including when @n=0@), or when we have an array of such,
-- or when we have some expression which evaluates to an array (but
-- which is not yet an array literal).
--
-- This is mainly for 'PrimOp', 'NaryOp', and 'Value' to do the
-- right thing with a minimum of boilerplate code.
expectTypeDir :: (ABT abt) => Sing a -> abt a -> Env abt -> Expect abt a
expectTypeDir SNat         e _  = ExpectNat   e
expectTypeDir SInt         e _  = ExpectInt   e
expectTypeDir SProb        e _  = ExpectProb  e
expectTypeDir SReal        e _  = ExpectReal  e
expectTypeDir (SData  _ _) e _  = ExpectData  e
expectTypeDir (SArray   a) e xs =
    -- TODO: fold this into 'expectAST'? cf., type-dir vs syn-dir...
    case resolveVar e xs of
    Left  x -> error "TODO" -- App_ (syn . PrimOp_ . Expect $ varType x) (var x)
    Right (Array_ e1 e2) ->
        ExpectArray e1 $ \ei ->
        caseBind e2 $ \x e' ->
            case jmEq (getSing ei) (varType x) of
            Just Refl -> expectTypeDir a e' $ pushEnv (Assoc x ei) xs
            Nothing   -> error "TODO"
    Right Empty_       -> expectEmpty
    Right t            -> expectAST t xs
expectTypeDir (SFun   _ a) e xs =
    ExpectFun $ \e2 ->
    expectTypeDir a (e `app` e2) xs
expectTypeDir (SMeasure _) e xs =
    expectSynDir e xs


expectEmpty :: (ABT abt) => Expect abt ('HArray a)
expectEmpty = ExpectArray (nat_ 0) $ error "expect: indexing an empty array"


expectAST :: (ABT abt) => AST abt a -> Env abt -> Expect abt a
expectAST (Lam_ e1) xs =
    ExpectFun $ \e2 ->
    caseBind e1 $ \x e' ->
        case jmEq (getSing e2) (varType x) of
        Just Refl -> expectSynDir e' $ pushEnv (Assoc x e2) xs
        Nothing   -> error "TODO"

expectAST (App_ e1 e2) xs =
    expectSynDir e1 xs `apF` e2

expectAST (Let_ e1 e2) xs =
    caseBind e2 $ \x e' ->
        case jmEq (getSing e1) (varType x) of
        Just Refl -> expectSynDir e' $ pushEnv (Assoc x e1) xs
        Nothing   -> error "TODO"

expectAST (Fix_ e1) xs =
    caseBind e1 $ \x e' ->
        let self = syn $ Fix_ e1 in
        case jmEq (getSing self) (varType x) of
        Just Refl -> expectSynDir e' $ pushEnv (Assoc x self) xs -- BUG: could loop
        Nothing   -> error "TODO"

expectAST (Ann_ _ e) xs =
    expectSynDir e xs

expectAST (PrimOp_ o) xs =
    -- N.B., we can't just use the default implementation for 'Index' and 'Reduce', because they could produce a measure by eliminating an array. Thus, to avoid looping forever, we must actually interpret arrays in our 'Expect' semantics, so that we can actually eliminate them here.
    -- TODO: this further suggests that these three shouldn't really be considered 'PrimOp's
    case o of
    Index a ->
        ExpectFun $ \arr ->
        ExpectFun $ \i ->
        -- TODO: should that be type-directed or syntax-directed?
        case expectTypeDir (SArray a) arr xs of
        -- TODO: should we insert a guard that @i < e1@?
        ExpectArray e1 e2 -> e2 i
    Size   a ->
        ExpectFun $ \arr ->
        -- TODO: should that be type-directed or syntax-directed?
        case expectTypeDir (SArray a) arr xs of
        ExpectArray e1 e2 -> expectSynDir e1 xs
    Reduce a -> error "TODO: expectAST{Reduce}"

    -- Everything else is trivial
    _ -> expectTypeDir (sing_PrimOp o) (syn $ PrimOp_ o) xs

expectAST (NaryOp_ o es) xs =
    expectTypeDir (sing_NaryOp o) (syn $ NaryOp_ o es) xs

expectAST (Value_ v) xs =
    expectTypeDir (sing_Value v) (value_ v) xs

expectAST (CoerceTo_   c  e)  xs = expectCoerceTo   c $ expectSynDir e xs
expectAST (UnsafeFrom_ c  e)  xs = expectUnsafeFrom c $ expectSynDir e xs
expectAST Empty_              _  = expectEmpty
expectAST (Array_      e1 e2) xs =
    ExpectArray e1 $ \ei ->
    caseBind e2 $ \x e' ->
        case jmEq (getSing ei) (varType x) of
        Just Refl -> expectSynDir e' $ pushEnv (Assoc x ei) xs
        Nothing   -> error "TODO"

expectAST (Datum_      d)     _  = ExpectData $ datum_ d
expectAST (Case_       e  bs) xs = error "TODO: expect{Case_}"
    -- In theory we should be able to use 'isBind' to filter our the hard cases and be able to tackle 'if_' at the very least. However, The problem is, we don't have @ABT (Expect abt)@ so we can't turn our @View (Expect abt)@ into an @Expect abt@...
    -- > | F.any (Monoid.getAny . foldMap1 (Monoid.Any . isBind)) $ bs =
    -- >     ...
    -- > | otherwise =
    -- >     let e'  = expectTypeDir (getSing e) e xs
    -- >         bs' = map (fmap1 (`expectSynDir` xs)) bs
    -- >         e2  = Syn $ Case_ e' bs'
    -- >     in ...?

expectAST (Measure_    o)     _  = expectMeasure o
expectAST (Bind_       e1 e2) xs =
    ExpectMeasure $ \c ->
    expectSynDir e1 xs `apM` \a ->
    caseBind e2 $ \x e' ->
        case jmEq (getSing a) (varType x) of
        Just Refl -> (expectSynDir e' $ pushEnv (Assoc x a) xs) `apM` c
        Nothing   -> error "TODO"

expectAST (Superpose_ pms) xs =
    ExpectMeasure $ \c ->
    sum [ p * (expectSynDir m xs `apM` c) | (p, m) <- pms ]


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
    let_ (summateV ps) $ \tot ->
    flip (if_ (prob_ 0 < tot)) (prob_ 0)
        $ summateV (mapWithIndex (\i p -> p * c i) ps) / tot
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
expectCoerceTo CNil          = id
expectCoerceTo (CCons c1 c2) =
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
expectUnsafeFrom CNil          = id
expectUnsafeFrom (CCons c1 c2) =
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
