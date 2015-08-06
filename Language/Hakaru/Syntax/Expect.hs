{-# LANGUAGE GADTs
           , KindSignatures
           , DataKinds
           , TypeOperators
           , NoImplicitPrelude
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.08.06
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

import           Prelude (($), (.), flip, error, Maybe(..), Either(..))
import           Data.IntMap   (IntMap)
import qualified Data.IntMap   as IM

import Language.Hakaru.Syntax.Nat      (fromNat)
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.TypeEq
import Language.Hakaru.Syntax.Coercion
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.Prelude

----------------------------------------------------------------

normalize :: (ABT abt) => abt '[] ('HMeasure a) -> abt '[] ('HMeasure a)
normalize m = superpose [(recip (total m), m)]

total :: (ABT abt) => abt '[] ('HMeasure a) -> abt '[] 'HProb
total m = expect m $ \_ -> prob_ 1

expect
    :: (ABT abt)
    => abt '[] ('HMeasure a)
    -> (abt '[] a -> abt '[] 'HProb) -> abt '[] 'HProb
expect e = apM $ expectSynDir e IM.empty

{- For debugging via the old Expect.hs:

-- Must rely on the Mochastic instance to define the @Expect repr@. Not clear how to build one directly from a plain @repr@.
almostExpect
    :: (Mochastic repr, Lambda repr)
    => Expect repr ('HMeasure a)
    -> repr ('HFun ('HFun (Expect' a) 'HProb) 'HProb)
almostExpect m = lam (\c -> unpair (unExpect m) (\_ m2 -> m2 `app` c))

prettyAlmostExpect = runPrettyPrint . almostExpect
-}

{- Test cases:

(1) make sure that @lam$\x -> total (weight x)@ works. Right now it returns @lam$\x -> x * prob_ 1@ which is correct, but could still be simplified further. It used to return @lam$\t -> sum [t * prob_ 1]@ but we fixed that.


(2) make sure that @lam$\m -> total m@ works. Right now it throws a <<loop>> exception! However, note that the following does work:
> let x = Variable (Name (Text.pack "x") 1) (SMeasure sWhatever)
> in syn . Lam_ . bind x . total $ var x
It's a problem with our 'binder' macro; surely due to the fact that 'expect' has to force things in order to store them in the 'Env'. Is there a way around that? Maybe by explicitly using the 'Expect' primop, and then performing the evaluation of that primop after 'binder' has finished constructing the first-order AST; but how can we specify that order of evaluation (except by making the evaluation of 'Expect' as 'expect' explicit)?

(3) Just using the numbers @2@ and @3@ to make the output a bit clearer:
> let x = Variable (Name (Data.Text.pack "x") 2) (SFun SInt $ SMeasure SProb)
> in syn . Lam_ . bind x . total $ (var x `app` int_ 3) :: TrivialABT '[] (('HInt ':-> 'HMeasure 'HProb) ':-> 'HProb)
N.B., the call to the 'Expect' primop should be applied to the whole @var x `app` int_ 3@ expression, not just to the @var x@ subexpression! This works, at present.
-}


----------------------------------------------------------------
-- TODO: only partially interpret things (functions, arrays), doing so lazily as needed.
--
-- | @Expect abt a@ gives the expectation-semantic interpretation
-- of @abt a@. The only \"real\" change is interpreting measures
-- as linear functionals; all the other interpretations are just
-- for performing normalization-by-evaluation in order to construct
-- that linear functional.
data Expect :: ([Hakaru] -> Hakaru -> *) -> Hakaru -> * where

    -- | This constructor captures two cases: (1) we don't bother
    -- performing NBE on primitive numeric types, so we just leave
    -- them as ASTs; (2) we can't interpret free variables or
    -- expressions whose reduction is blocked by a variable in head
    -- position, so we'll just wrap these ASTs with the 'Expect'
    -- primop (as neessary).
    ExpectAST :: abt '[] a -> Expect abt a

    -- TODO: keep track of the old 'varHint' used for the array body, in case we need to undo the HOAS.
    -- | We interpret arrays so that we can evaluate 'Index' and
    -- 'Reduce' as needed.
    ExpectArray
        :: abt '[] 'HNat
        -> (abt '[] 'HNat -> Expect abt a)
        -> Expect abt ('HArray a)

    -- TODO: actually interpret 'HData', so we can evaluate 'Case_'
    ExpectData
        :: abt '[] ('HData t xss)
        -> Expect abt ('HData t xss)

    -- TODO: keep track of the old 'varHint' used for the lambda body, in case we need to undo the HOAS.
    -- | We interpret functions so we can (easily) interpret our
    -- parameterized measures. This interpretation allows us to
    -- evaluate 'App_' as needed; which is especially helpful for
    -- the case where it's a beta-redex with 'Lam_'.
    ExpectFun
        :: (abt '[] a -> Expect abt b)
        -> Expect abt (a ':-> b)

    -- | The whole goal of this module is to provide the following
    -- interpretation for measures.
    ExpectMeasure
        :: ((abt '[] a -> abt '[] 'HProb) -> abt '[] 'HProb)
        -> Expect abt ('HMeasure a)


-- TODO: a general function for converting Expect back into plain
-- Haskell functions; we could call it \"expectify\", to pun on the
-- reify\/reflect of NBE. We may need to define a type family that
-- mirrors the Expect datatype, and then enable -XAllowAmbiguousTypes
-- to be able to use it...


-- | Apply a function, removing administrative redexes if possible.
apF :: (ABT abt) => Expect abt (a ':-> b) -> abt '[] a -> Expect abt b
apF (ExpectFun f) e = f e
apF (ExpectAST f) e = ExpectAST $ f `app` e


-- | Apply a measure's integrator to a given function, removing
-- administrative redexes if possible. N.B., if the argument is an
-- 'ExpectAST', then we're stuck converting the continuation argument
-- into a lambda in the resulting AST.
--
-- TODO: how can we minimize our need to do that (e.g., only do it for the top-level @apM@ in 'expect' and not at any of the other @apM@ call sites)?
apM :: (ABT abt)
    => Expect abt ('HMeasure a)
    -> (abt '[] a -> abt '[] 'HProb) -> abt '[] 'HProb
apM (ExpectMeasure f) c = f c
apM (ExpectAST     e) c =
    -- TODO: should we really be doing this here? or should it only be in 'expectTypeDir'?
    case getSing e of
    SMeasure a -> primOp2_ (Expect a) e (lamWithType a c)


data Assoc :: ([Hakaru] -> Hakaru -> *) -> * where
    Assoc :: {-# UNPACK #-} !(Variable a) -> abt '[] a -> Assoc abt
    -- TODO: store the @Expect abt a@ instead?
    -- TODO: have two different versions of variable lookup; one for when we need to take the expectation of the variable, and one for just plugging things into place.

type Env abt = IntMap (Assoc abt)

pushEnv :: Assoc abt -> Env abt -> Env abt
pushEnv v@(Assoc x _) = IM.insert (fromNat $ varID x) v

getSing :: (ABT abt) => abt '[] a -> Sing a
getSing _ = error "TODO: get singletons of anything after typechecking"

-- N.B., in the ICFP 2015 pearl paper, we take the expectation of bound variables prior to taking the expectation of their scope. E.g., @expect(let_ v e1 e2) xs c = expect e1 xs $ \x -> expect e2 (pushEnv v x xs) c@. Whereas here, I'm being lazier and performing the expectation on variable lookup. If the variable is never used (by wasted computation) or used exactly once (by Tonelli's theorem), then this delayed evaluation preserves the expectation semantics (ICFP 2015, §5.6.0); so we only need to worry if the variable is used more than once, in which case we'll have to worry about whether the various integrals commute/exchange with one another. More generally, cf. Bhat et al.'s \"active variables\"


-- TODO: Move this to ABT.hs
-- TODO: Swap the argument order?
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
    => abt '[] a
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
--
-- N.B., when the expression is a variable of measure type, then
-- we're stuck producing a lambda for the second argument to the
-- 'Expect' primop.
expectSynDir :: (ABT abt) => abt '[] a -> Env abt -> Expect abt a
expectSynDir e xs =
    case resolveVar e xs of
    Right t -> expectAST t xs
    Left  x -> expectTypeDir (varType x) (var x)


-- | Perform type-directed reflection in order to lift an expression
-- into its expectation semantics without actually looking at it.
-- For expressions of function type, this means eta-expanding things
-- (with a Haskell lambda and a Hakaru application); which is used
-- by the 'expectAST' call-site for handling 'PrimOp'. For expressions
-- of measure types, we wrap the expression with an explicit call
-- to the 'Expect' primop; which is the right thing to do for
-- variables in the 'expectSynDir' call-site.
--
-- TODO: it's not entirely clear what this function should do for arrays and datatypes...
expectTypeDir :: (ABT abt) => Sing a -> abt '[] a -> Expect abt a
expectTypeDir SNat         e = ExpectAST e
expectTypeDir SInt         e = ExpectAST e
expectTypeDir SProb        e = ExpectAST e
expectTypeDir SReal        e = ExpectAST e
expectTypeDir (SData  _ _) e = ExpectAST e -- TODO: is that right?
expectTypeDir (SArray   _) e = ExpectAST e -- TODO: is that right?
expectTypeDir (SFun   _ a) e =
    ExpectFun $ \e2 ->
    expectTypeDir a (e `app` e2)
expectTypeDir (SMeasure a) e =
    -- TODO: should we really be doing this here? or should it only be in 'apM'?
    ExpectMeasure $ \c ->
    primOp2_ (Expect a) e (lamWithType a c)
    -- TODO: can we reuse 'apM' somehow, instead of repeating ourselves? We could use @ExpectMeasure (apM . ExpectAST $ var x)@ if we can make 'getSing' work. N.B., we cannot use 'expect' in lieu of the 'Expect' primop, because that will cause us to loop (without throwing a <<loop>> exception).



expectAST :: (ABT abt) => AST abt a -> Env abt -> Expect abt a
expectAST (Lam_ e1) xs =
    ExpectFun $ \e2 ->
    caseBind e1 $ \x e' ->
        case jmEq (getSing e2) (varType x) of
        Just Refl -> expectSynDir e' $ pushEnv (Assoc x e2) xs
        Nothing   -> error "TODO: expectAST{Lam_} with mismatched types"

expectAST (App_ e1 e2) xs =
    expectSynDir e1 xs `apF` e2

expectAST (Let_ e1 e2) xs =
    caseBind e2 $ \x e' ->
        case jmEq (getSing e1) (varType x) of
        Just Refl -> expectSynDir e' $ pushEnv (Assoc x e1) xs
        Nothing   -> error "TODO: expectAST{Let_} with mismatched types"

expectAST (Fix_ e1) xs =
    caseBind e1 $ \x e' ->
        let self = syn $ Fix_ e1 in
        case jmEq (getSing self) (varType x) of
        Just Refl -> expectSynDir e' $ pushEnv (Assoc x self) xs -- BUG: could loop
        Nothing   -> error "TODO: expectAST{Fix_} with mismatched types"

expectAST (Ann_ _ e) xs =
    -- TODO: should we re-wrap it up in a type annotation?
    expectSynDir e xs

expectAST (PrimOp_ o) xs =
    -- N.B., we can't just use the default implementation for 'Index' and 'Reduce', because they could produce a measure by eliminating an array. Thus, to avoid looping forever, we must actually interpret arrays in our 'Expect' semantics, so that we can actually eliminate them here.
    -- TODO: this further suggests that these three shouldn't really be considered 'PrimOp's
    case o of
    Index a ->
        ExpectFun $ \arr ->
        case expectSynDir arr xs of
        -- TODO: should we insert a guard that @i < e1@?
        ExpectArray e1 e2 -> ExpectFun e2
        ExpectAST   e     -> ExpectAST $ primOp1_ o e
    Size a ->
        ExpectFun $ \arr ->
        case expectSynDir arr xs of
        ExpectArray e1 _ -> expectSynDir e1 xs
        ExpectAST   e    -> ExpectAST $ primOp1_ o e
    Reduce a -> error "TODO: expectAST{Reduce}"

    -- All the other PrimOps are functions returning primitive types (the four numbers or HBool); so we'll just eta-expand them.
    _ -> expectTypeDir (sing_PrimOp o) (primOp0_ o)

expectAST (NaryOp_ o es) _ = ExpectAST . syn $ NaryOp_ o es
    -- N.B., no NaryOps operate on types containing HMeasure nor
    -- (:->); thus we're guaranteed to never need to descend into @es@.
expectAST (Value_ v)     _ = ExpectAST $ value_ v
    -- N.B., no Values have types containing HMeasure, (:->), nor
    -- HArray; thus we're guaranteed to never need to descend into @v@.

expectAST (CoerceTo_   c  e)  xs = expectCoerceTo   c $ expectSynDir e xs
expectAST (UnsafeFrom_ c  e)  xs = expectUnsafeFrom c $ expectSynDir e xs
expectAST Empty_              _  =
    ExpectArray (nat_ 0) $ error "expect: indexing an empty array"
expectAST (Array_      e1 e2) xs =
    ExpectArray e1 $ \ei ->
    caseBind e2 $ \x e' ->
        case jmEq (getSing ei) (varType x) of
        Just Refl -> expectSynDir e' $ pushEnv (Assoc x ei) xs
        Nothing   -> error "TODO: expectAST{Array_} with mismatched types"

expectAST (Datum_      d)     _  = ExpectData $ datum_ d
expectAST (Case_       e  bs) xs = error "TODO: expect{Case_}"
    -- In theory we should be able to use 'isBind' to filter our the hard cases and be able to tackle 'if_' at the very least. However, The problem is, we don't have @ABT (Expect abt)@ so we can't turn our @View (Expect abt)@ into an @Expect abt@...
    -- > | F.any (Monoid.getAny . foldMap1 (Monoid.Any . isBind)) $ bs =
    -- >     ...
    -- > | otherwise =
    -- >     let e'  = expectTypeDir (getSing e) e
    -- >         bs' = map (fmap1 (`expectSynDir` xs)) bs
    -- >         e2  = Syn $ Case_ e' bs'
    -- >     in ...?
    --
    --
    -- According to the old Expect.hs, we have expect(if_ b t f) = if_ b (expect t) (expect f); albeit with the @lam$\x0 -> ... `unpair` \x1 x2 -> x2 `app` x0@ wrapper around it at the top level.
    -- Similarly for @uneither@, going under the binders and leaving the bound variables as-is, thus changing their types. E.g., @uneither x dirac m@ becomes @uneither x (\x1 -> let_ x1$\x2-> pair (dirac x2) (lam$\x3 -> x3 `app` x2)) (...)@ so it looks like that's what @(unExpect . f . Expect)@ actually means...
    -- Though this seems to contradict the ICFP2015 paper, which has @expect(if_ b t f) rho c = expect b rho $\b' -> expect (if b then t else f) rho c@. Then again, everything is implicitly a measure in that paper; so that's prolly all that's going on.
    --
    -- According to the Lazy.tex paper, we should have something like:
    -- > expect (Case_ e bs) xs c =
    -- >     foreach bs $ \(pat,body) ->
    -- >         case tryMatching pat (denotation e xs) of
    -- >         Matches ys   -> expect body (ys ++ xs) c
    -- >         Doesn'tMatch -> 0 -- == expect (superpose[]) xs c
    -- where @denotation e xs@ is the constant interpretation for non-measures, and the @expect@ integrator interpretation for measures
    -- We can avoid some of that administrative stuff, by using @let_@ to name the @denotation e xs@ stuff and then use Hakaru's @Case_@ on that.

expectAST (Measure_    o)     _  = expectMeasure o
expectAST (Bind_       e1 e2) xs =
    ExpectMeasure $ \c ->
    expectSynDir e1 xs `apM` \a ->
    caseBind e2 $ \x e' ->
        case jmEq (getSing a) (varType x) of
        Just Refl -> (expectSynDir e' $ pushEnv (Assoc x a) xs) `apM` c
        Nothing   -> error "TODO: expectAST{Bind_} with mismatched types"

expectAST (Superpose_ pms) xs =
    ExpectMeasure $ \c ->
    sum [ p * (expectSynDir m xs `apM` c) | (p, m) <- pms ]
    -- TODO: in the Lazy.tex paper, we use @denotation p xs@ and guard against that interpretation being negative...
    -- TODO: if @pms@ is null, then automatically simplify to just 0


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


expectCoerceTo :: (ABT abt) => Coercion a b -> Expect abt a -> Expect abt b
expectCoerceTo c (ExpectAST e) = ExpectAST $ coerceTo_ c e
expectCoerceTo _ _ = error "expectCoerceTo: the impossible happened"

expectUnsafeFrom
    :: (ABT abt) => Coercion a b -> Expect abt b -> Expect abt a
expectUnsafeFrom c (ExpectAST e) = ExpectAST $ unsafeFrom_ c e
expectUnsafeFrom _ _ = error "expectUnsafeFrom: the impossible happened"

----------------------------------------------------------------
----------------------------------------------------------- fin.
