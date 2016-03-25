{-# LANGUAGE GADTs
           , EmptyCase
           , KindSignatures
           , DataKinds
           , TypeOperators
           , NoImplicitPrelude
           , ScopedTypeVariables
           , FlexibleContexts
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.03.24
-- |
-- Module      :  Language.Hakaru.Expect
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- TODO: Switch everything over to using "Language.Hakaru.Evaluation.Lazy" for getting rid of redexes, instead of the current NBE-based approach.
----------------------------------------------------------------
module Language.Hakaru.Expect
    ( normalize
    , total
    , expect
    ) where

import           Prelude   (($), (.), flip, map, error, Either(..))
import qualified Data.Text as Text

import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.Prelude

----------------------------------------------------------------

-- | Convert an arbitrary measure into a probability measure; i.e.,
-- reweight things so that the total weight\/mass is 1.
normalize
    :: (ABT Term abt) => abt '[] ('HMeasure a) -> abt '[] ('HMeasure a)
normalize m = withWeight (recip $ total m) m


-- | Compute the total weight\/mass of a measure.
total :: (ABT Term abt) => abt '[] ('HMeasure a) -> abt '[] 'HProb
total m = expect m $ \_ -> prob_ 1


-- | Convert a measure into its integrator.
expect
    :: (ABT Term abt)
    => abt '[] ('HMeasure a)
    -> (abt '[] a -> abt '[] 'HProb) -> abt '[] 'HProb
expect e = apM $ expectSynDir ImpureMeasure e emptyAssocs
-- TODO: we should prolly grab the @c@ here and pass it down through 'expectSynDir'; rather than gluing things together with just the 'Expect' data type. Maybe that'll make it easier to handle 'Case_'

----------------------------------------------------------------
-- | Explicit proof that a given Hakaru type is impure. We use this
-- to eliminate unreachable branches in 'expectTerm'.
data ImpureType :: Hakaru -> * where
    ImpureMeasure :: ImpureType ('HMeasure a)
    ImpureFun     :: !(ImpureType a) -> ImpureType (b ':-> a)
    ImpureArray   :: !(ImpureType a) -> ImpureType ('HArray a)

-- | Lazily pattern match on the 'ImpureFun' constructor.
unImpureFun :: ImpureType (b ':-> a) -> ImpureType a
unImpureFun (ImpureFun p) = p

-- | Lazily pattern match on the 'ImpureArray' constructor.
unImpureArray :: ImpureType ('HArray a) -> ImpureType a
unImpureArray (ImpureArray p) = p


----------------------------------------------------------------
-- | @Expect abt a@ gives the expectation-semantic interpretation
-- of @abt '[] a@, where @a@ is some 'ImpureType'. The only \"real\"
-- change is interpreting measures as linear functionals; all the
-- other interpretations are just for performing
-- normalization-by-evaluation in order to construct that linear
-- functional with a minimum of administrative redexes.
data Expect :: ([Hakaru] -> Hakaru -> *) -> Hakaru -> * where
    -- BUG: haddock doesn't like annotations on GADT constructors
    -- <https://github.com/hakaru-dev/hakaru/issues/6>

    -- The whole goal of this module is to provide the following
    -- interpretation for measures.
    ExpectMeasure
        :: ((abt '[] a -> abt '[] 'HProb) -> abt '[] 'HProb)
        -> Expect abt ('HMeasure a)

    -- We interpret functions so we can (easily) interpret our
    -- parameterized measures. This interpretation allows us to
    -- evaluate 'App_' as needed; which is especially helpful for
    -- the case where it's a beta-redex with 'Lam_'.
    --
    -- We keep track of the user-supplied variable name hint (if
    -- any), so that we can reify things back into @abt@ as necessary.
    ExpectFun
        :: Text.Text
        -> (abt '[] a -> Expect abt b)
        -> Expect abt (a ':-> b)

    -- We interpret arrays so that we can evaluate 'Index' and
    -- 'Reduce' as needed.
    --
    -- We keep track of the user-supplied variable name hint (if
    -- any), so that we can reify things back into @abt@ as necessary.
    ExpectArray
        :: Text.Text
        -> abt '[] 'HNat
        -> (abt '[] 'HNat -> Expect abt a)
        -> Expect abt ('HArray a)

    -- TODO: interpret 'HData', so we can NBE 'Case_' of 'Datum_'?


-- | Apply a measure's integrator to a given function, removing
-- administrative redexes if possible.
apM :: (ABT Term abt)
    => Expect abt ('HMeasure a)
    -> (abt '[] a -> abt '[] 'HProb) -> abt '[] 'HProb
apM (ExpectMeasure f) c = f c

-- This function is only used once, for 'expectTerm' of 'App_'.
-- | Apply a function, removing administrative redexes if possible.
apF :: (ABT Term abt)
    => Expect abt (a ':-> b)
    -> abt '[] a -> Expect abt b
apF (ExpectFun _ e1) e2 = e1 e2

-- This function is only used once, for 'expectTerm' of the 'Index' primop.
-- | Index into an array, removing administrative redexes if possible.
-- This macro does not insert any sort of bounds checking. We assume
-- the functional component of the 'ExpectArray' already does that
-- wherever is appropriate.
apA :: (ABT Term abt)
    => Expect abt ('HArray a)
    -> abt '[] 'HNat -> Expect abt a
apA (ExpectArray _ _ e2) ei = e2 ei


----------------------------------------------------------------
-- N.B., in the ICFP 2015 pearl paper, we took the expectation of bound variables prior to taking the expectation of their scope. E.g., @expect(let_ v e1 e2) xs c = expect e1 xs $ \x -> expect e2 (insertAssoc v x xs) c@. Whereas here, I'm being lazier and performing the expectation on variable lookup. This delayed evaluation preserves the expectation semantics (ICFP 2015, §5.6.0) whenever (1) the variable is never used (by wasted computation), or (2) used exactly once (by Tonelli's theorem); so we only need to worry if (3) the variable is used more than once, in which case we'll have to worry about whether the various integrals commute/exchange with one another. More generally, cf. Bhat et al.'s \"active variables\"


-- BUG: Make sure our use of Assocs has the correct capture-avoiding behavior!!

----------------------------------------------------------------
-- | Perform a syntax-directed reflection of a term into it's
-- expectation semantics. This function will perform whatever
-- evaluation it needs to in order to expose the things being
-- reflected.
--
-- N.B., if the expression is blocked on some free variable, then
-- we're stuck producing a lambda for the second argument to the
-- 'Expect' primop.
expectSynDir
    :: (ABT Term abt)
    => ImpureType a -- N.B., should be lazy\/irrelevant in this argument
    -> abt '[] a
    -> Assocs (abt '[])
    -> Expect abt a
expectSynDir p e xs =
    case resolveVar e xs of
    Right t -> expectTerm p t xs
    Left  x -> expectTypeDir p (varType x) (var x)


-- | Perform type-directed reflection in order to lift an expression
-- into its expectation semantics without actually looking at it. That is,
--
-- * for measure types, we wrap the expression with an explicit
--   call to the 'Expect' primop.
-- * for function types, we take the NBE interpretation (i.e.,
--   \"eta-expand\" them with a Haskell lambda and a Hakaru
--   application), so that we can rebuild the context around a
--   blocked expression. Ultimately inserting the explicit call to
--   the 'Expect' primop around the whole expression of the function
--   applied to its arguments.
-- * for array types, we take their NBE interpretation as well.
--   Again, this ensures that the explicit call to the 'Expect'
--   primop ends up in the right place.
expectTypeDir
    :: (ABT Term abt)
    => ImpureType a -- N.B., should be lazy\/irrelevant in this argument
    -> Sing a
    -> abt '[] a
    -> Expect abt a
expectTypeDir p SNat         _ = case p of {}
expectTypeDir p SInt         _ = case p of {}
expectTypeDir p SProb        _ = case p of {}
expectTypeDir p SReal        _ = case p of {}
expectTypeDir p (SData  _ _) _ = case p of {}
expectTypeDir p (SArray   a) e =
    ExpectArray Text.empty (arrayOp1_ (Size a) e) $ \ei ->
    expectTypeDir (unImpureArray p) a (arrayOp2_ (Index a) e ei)
    -- TODO: is there any way of @Let_@-binding the @e@ expression, to guarantee we can't possibly duplicate it by someone wanting to reify the @ExpectArray@ back into a plain Hakaru array?
expectTypeDir p (SFun   _ a) e =
    ExpectFun Text.empty $ \e2 ->
    expectTypeDir (unImpureFun p) a (e `app` e2)
expectTypeDir _ (SMeasure a) e =
    ExpectMeasure $ \c ->
    syn (Expect :$ e :* binder Text.empty a c :* End)


expectTerm
    :: (ABT Term abt)
    => ImpureType a -- N.B., should be lazy\/irrelevant in this argument
    -> Term abt a
    -> Assocs (abt '[])
    -> Expect abt a
expectTerm p (Lam_ :$ es) xs =
    case es of
    e1 :* End ->
        caseBind e1 $ \x e' ->
        ExpectFun (varHint x) $ \e2 ->
        expectSynDir (unImpureFun p) e' $ insertAssoc (Assoc x e2) xs
    _ -> error "expectTerm: the impossible happened"

expectTerm p (App_ :$ es) xs =
    case es of
    e1 :* e2 :* End ->
        expectSynDir (ImpureFun p) e1 xs `apF` e2
    _ -> error "expectTerm: the impossible happened"

expectTerm p (Let_ :$ es) xs =
    case es of
    e1 :* e2 :* End ->
        caseBind e2 $ \x e' ->
        expectSynDir p e' $ insertAssoc (Assoc x e1) xs
    _ -> error "expectTerm: the impossible happened"

expectTerm p (PrimOp_ _ :$ _) _ = case p of {}
expectTerm p (ArrayOp_ o :$ es) xs =
    case o of
    Index _ ->
        case es of
        arr :* ei :* End -> expectSynDir (ImpureArray p) arr xs `apA` ei
        _ -> error "expectTerm: the impossible happened"

    Reduce a -> error "TODO: expectTerm{Reduce}"
    
    _ -> case p of {}

expectTerm p (NaryOp_     _ _)    _ = case p of {}
expectTerm p (Literal_    _)      _ = case p of {}
expectTerm p (CoerceTo_   _ :$ _) _ = case p of {}
expectTerm p (UnsafeFrom_ _ :$ _) _ = case p of {}
expectTerm _ (Empty_ _)           _ =
    ExpectArray Text.empty (nat_ 0)
        $ error "expect: indexing an empty array"
    -- TODO: should we instead emit the AST for buggily indexing an empty array?
expectTerm p (Array_ e1 e2) xs =
    caseBind e2 $ \x e' ->
    ExpectArray (varHint x) e1 $ \ei ->
    -- BUG: we should wrap this in a guard that @ei < e1@, instead of just performing the substitution arbitrarily.
    expectSynDir (unImpureArray p) e' $ insertAssoc (Assoc x ei) xs

expectTerm p (Datum_ _)    _  = case p of {}
expectTerm p (Case_  e bs) xs =
    -- TODO: doing case analysis on @p@ is just a hack to try and get at least some things to work. We can probably get everything to work by doing induction on @p@, but it'd be better if we could grab the type of the whole case expression and do induction on that...
    case p of
    ImpureMeasure ->
        ExpectMeasure $ \c ->
        -- TODO: for some reason we can't get 'fmap21' to typecheck here in order to clean up the mapping over @body@
        syn . Case_ e . (`Prelude.map` bs) $ \(Branch pat body) ->
            Branch pat . expectBranch c p xs $ viewABT body
    _ -> error "TODO: expect{Case_}"

    -- We're just treating the pattern-bound variables as if they were free variables, that way we'll insert an explicit call to the 'Expect' primop around any expressions blocked on those variables.
    -- Of course, it'd be nice to use NBE to reduce @Case_@-of-@Datum_@ redexes along the way... That'd look something like this according to Lazy.tex:
    -- > expect (Case_ e bs) xs c =
    -- >     foreach bs $ \(pat,body) ->
    -- >         case tryMatching pat (denotation e xs) of
    -- >         Matches ys   -> expect body (ys ++ xs) c
    -- >         Doesn'tMatch -> 0 -- == expect (superpose[]) xs c
    -- where @denotation e xs@ is the constant interpretation for non-measures, and the @expect@ integrator interpretation for measures
    -- We can avoid some of that administrative stuff, by using @let_@ to name the @denotation e xs@ stuff and then use Hakaru's @Case_@ on that.

expectTerm p (MeasureOp_ o :$ es) xs = expectMeasure p o es xs
expectTerm _ (Dirac :$ es) _ =
    case es of
    a :* End ->
        ExpectMeasure $ \c -> c a
    _ -> error "expectTerm: the impossible happened"

expectTerm p (MBind :$ es) xs =
    case es of
    e1 :* e2 :* End ->
        ExpectMeasure $ \c ->
        expectSynDir ImpureMeasure e1 xs `apM` \a ->
        caseBind e2 $ \x e' ->
        (expectSynDir p e' $ insertAssoc (Assoc x a) xs) `apM` c
    _ -> error "expectTerm: the impossible happened"

expectTerm p (Superpose_ es) xs =
    ExpectMeasure $ \c ->
    sum [ e1 * (expectSynDir p e2 xs `apM` c) | (e1, e2) <- es ]
    -- TODO: in the Lazy.tex paper, we use @denotation e1 xs@ and guard against that interpretation being negative...
    -- TODO: if @es@ is null, then automatically simplify to just 0

expectTerm p (Expect    :$ _) _ = case p of {}
expectTerm p (Integrate :$ _) _ = case p of {}
expectTerm p (Summate   :$ _) _ = case p of {}
expectTerm p (Plate     :$ _) _ = error "TODO: expectTerm{Plate}"
expectTerm p (Chain     :$ _) _ = error "TODO: expectTerm{Chain}"


expectBranch
    :: (ABT Term abt)
    => (abt '[] a -> abt '[] 'HProb)
    -> ImpureType ('HMeasure a)
    -> Assocs (abt '[])
    -> View (Term abt) xs ('HMeasure a)
    -> abt xs 'HProb
expectBranch c p xs (Syn  t)    = expectTerm   p      t  xs `apM` c
expectBranch c p xs (Var  x)    = expectSynDir p (var x) xs `apM` c
expectBranch c p xs (Bind x e') = bind x $ expectBranch c p xs e'


-- TODO: right now we just use the Assocs in a hackish way in order
-- to (hopefully) guarantee correctness. Really we should do something
-- more efficient rather than calling 'substs' repeatedly everywhere.
-- One possible option would be to residualize the Assocs directly
-- as a bunch of let bindings (or whatever) in the generated program
expectMeasure
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => ImpureType ('HMeasure a)
    -> MeasureOp typs a
    -> SArgs abt args
    -> Assocs (abt '[])
    -> Expect abt ('HMeasure a)
expectMeasure _ Lebesgue = \End rho ->
    ExpectMeasure $ \c ->
    integrate negativeInfinity infinity (substs rho . c)
expectMeasure _ Counting = \End rho ->
    ExpectMeasure $ \c ->
    summate negativeInfinity infinity (substs rho . c)
expectMeasure _ Categorical = \(ps :* End) rho ->
    ExpectMeasure $ \c ->
    let ps' = substs rho ps in
    let_ (summateV ps') $ \tot ->
    flip (if_ (prob_ 0 < tot)) (prob_ 0)
        $ summateV (mapWithIndex (\i p -> p * substs rho (c i)) ps') / tot
expectMeasure _ Uniform = \(lo :* hi :* End) rho ->
    ExpectMeasure $ \c ->
    let lo' = substs rho lo
        hi' = substs rho hi
    in
    integrate lo' hi' $ \x ->
        densityUniform hi' lo' x * substs rho (c x)
expectMeasure _ Normal = \(mu :* sd :* End) rho ->
    -- N.B., if\/when extending this to higher dimensions, the real equation is @recip (sqrt (2*pi*sd^2) ^ n) * integrate$\x -> c x * exp (negate (norm_n (x - mu) ^ 2) / (2*sd^2))@ for @Real^n@.
    ExpectMeasure $ \c ->
    integrate negativeInfinity infinity $ \x ->
        densityNormal (substs rho mu) (substs rho sd) x * substs rho (c x)
expectMeasure _ Poisson = \(l :* End) rho ->
    ExpectMeasure $ \c ->
    let l' = substs rho l in
    flip (if_ (prob_ 0 < l')) (prob_ 0)
        $ summate (real_ 0) infinity $ \x ->
            let x_ = unsafeFrom_ signed x in
            densityPoisson l' x_ * substs rho (c x_)
expectMeasure _ Gamma = \(shape :* scale :* End) rho ->
    ExpectMeasure $ \c ->
    integrate (real_ 0) infinity $ \x ->
        let x_ = unsafeProb x in
        densityGamma (substs rho shape) (substs rho scale) x_ * substs rho (c x_)
expectMeasure _ Beta = \(a :* b :* End) rho ->
    ExpectMeasure $ \c ->
    integrate (real_ 0) (real_ 1) $ \x ->
        let x_ = unsafeProb x in
        densityBeta (substs rho a) (substs rho b) x_ * substs rho (c x_)

----------------------------------------------------------------
----------------------------------------------------------- fin.
