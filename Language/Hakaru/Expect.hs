{-# LANGUAGE GADTs
           , EmptyCase
           , KindSignatures
           , DataKinds
           , TypeOperators
           , NoImplicitPrelude
           , ScopedTypeVariables
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.09
-- |
-- Module      :  Language.Hakaru.Expect
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
----------------------------------------------------------------
module Language.Hakaru.Expect
    ( normalize
    , total
    , expect
    ) where

import           Prelude (($), (.), flip, map, error, Maybe(..), Either(..))
import           Data.IntMap   (IntMap)
import qualified Data.IntMap   as IM
import qualified Data.Text     as Text

import Language.Hakaru.Syntax.IClasses (TypeEq(..))
import Language.Hakaru.Syntax.Nat      (fromNat)
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.Coercion
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.Prelude

----------------------------------------------------------------

-- | Convert an arbitrary measure into a probability measure; i.e.,
-- reweight things so that the total weight\/mass is 1.
normalize :: (ABT abt) => abt '[] ('HMeasure a) -> abt '[] ('HMeasure a)
normalize m = superpose [(recip (total m), m)]


-- | Compute the total weight\/mass of a measure.
total :: (ABT abt) => abt '[] ('HMeasure a) -> abt '[] 'HProb
total m = expect m $ \_ -> prob_ 1


-- | Convert a measure into its integrator.
expect
    :: (ABT abt)
    => abt '[] ('HMeasure a)
    -> (abt '[] a -> abt '[] 'HProb) -> abt '[] 'HProb
expect e = apM $ expectSynDir ImpureMeasure e emptyAssocs
-- TODO: we should prolly grab the @c@ here and pass it down through 'expectSynDir'; rather than gluing things together with just the 'Expect' data type. Maybe that'll make it easier to handle 'Case_'

{- For debugging via the old Expect.hs:

-- Must rely on the Mochastic instance to define the @Expect repr@. Not clear how to build one directly from a plain @repr@.
almostExpect
    :: (Mochastic repr, Lambda repr)
    => Expect repr ('HMeasure a)
    -> repr ('HFun ('HFun (Expect' a) 'HProb) 'HProb)
almostExpect m = lam (\c -> unpair (unExpect m) (\_ m2 -> m2 `app` c))

prettyAlmostExpect = runPrettyPrint . almostExpect
-}


test1 :: TrivialABT '[] ('HProb ':-> 'HProb)
test1 = lam $ \x -> total (weight x)
-- Currently returns @lam $ \x -> x * prob_ 1@ which is correct, but could still be simplified further. It used to return @lam $ \x -> sum [x * prob_ 1]@ but we fixed that via smart constructors.


test2 :: TrivialABT '[] ('HMeasure 'HProb ':-> 'HProb)
test2 = syn (Lam_ :$ bind x (total (var x)) :* End)
    where
    x = Variable (Text.pack "x") 2 (SMeasure SProb)
-- TODO: we'd rather use @lam $ \x -> total x@ but that causes 'binder' to throw a <<loop>> exception, presumably because 'expect' needs to force variable IDs to store them in the Assocs. Is there any way to work around that so we don't need to manually generate our own variable? Maybe by explicitly using the 'Expect' primop, and then performing the evaluation of that primop after 'binder' has finished constructing the first-order AST; but how can we specify that order of evaluation (except by making the evaluation of 'Expect' as 'expect' explicit)?


-- TODO: we'd rather use @lam $ \x -> total (x `app` int_ 3)@
test3 :: TrivialABT '[] (('HInt ':-> 'HMeasure 'HProb) ':-> 'HProb)
test3 = syn (Lam_ :$ bind x (total (var x `app` int_ 3)) :* End)
    where
    x = Variable (Text.pack "x") 2 (SFun SInt $ SMeasure SProb)

test4 :: TrivialABT '[] 'HProb
test4 = total $ if_ true (dirac unit) (weight (prob_ 5) >> dirac unit)

test5 :: TrivialABT '[] (HEither HUnit HUnit ':-> 'HProb)
test5 =
    lam $ \x ->
        total $
            uneither x
            (\_ -> dirac unit)
            (\_ -> weight (prob_ 5) >> dirac unit)

{-
total (array (nat_ 1) (\x -> dirac x) ! nat_ 0) :: TrivialABT '[] 'HProb
syn (Value_ (VProb LogFloat 1.0))
-}

----------------------------------------------------------------
-- | Explicit proof that a given Hakaru type is impure. We use this
-- to eliminate unreachable branches in 'expectAST'.
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

    -- | The whole goal of this module is to provide the following
    -- interpretation for measures.
    ExpectMeasure
        :: ((abt '[] a -> abt '[] 'HProb) -> abt '[] 'HProb)
        -> Expect abt ('HMeasure a)

    -- | We interpret functions so we can (easily) interpret our
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

    -- | We interpret arrays so that we can evaluate 'Index' and
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
apM :: (ABT abt)
    => Expect abt ('HMeasure a)
    -> (abt '[] a -> abt '[] 'HProb) -> abt '[] 'HProb
apM (ExpectMeasure f) c = f c

-- This function is only used once, for 'expectAST' of 'App_'.
-- | Apply a function, removing administrative redexes if possible.
apF :: (ABT abt)
    => Expect abt (a ':-> b)
    -> abt '[] a -> Expect abt b
apF (ExpectFun _ e1) e2 = e1 e2

-- This function is only used once, for 'expectAST' of the 'Index' primop.
-- | Index into an array, removing administrative redexes if possible.
-- This macro does not insert any sort of bounds checking. We assume
-- the functional component of the 'ExpectArray' already does that
-- wherever is appropriate.
apA :: (ABT abt)
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
    :: (ABT abt)
    => ImpureType a -- N.B., should be lazy\/irrelevant in this argument
    -> abt '[] a
    -> Assocs abt
    -> Expect abt a
expectSynDir p e xs =
    case resolveVar e xs of
    Right t -> expectAST p t xs
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
    :: (ABT abt)
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
    ExpectArray Text.empty (primOp1_ (Size a) e) $ \ei ->
    expectTypeDir (unImpureArray p) a (primOp2_ (Index a) e ei)
    -- TODO: is there any way of @Let_@-binding the @e@ expression, to guarantee we can't possibly duplicate it by someone wanting to reify the @ExpectArray@ back into a plain Hakaru array?
expectTypeDir p (SFun   _ a) e =
    ExpectFun Text.empty $ \e2 ->
    expectTypeDir (unImpureFun p) a (e `app` e2)
expectTypeDir _ (SMeasure a) e =
    ExpectMeasure $ \c ->
    -- measure2_ (Expect a) e (lamWithType a c)
    syn (Expect :$ e :* binder Text.empty a c :* End)


expectAST
    :: (ABT abt)
    => ImpureType a -- N.B., should be lazy\/irrelevant in this argument
    -> AST abt a
    -> Assocs abt
    -> Expect abt a
expectAST p (Lam_ :$ es) xs =
    case es of
    e1 :* End ->
        caseBind e1 $ \x e' ->
        ExpectFun (varHint x) $ \e2 ->
        expectSynDir (unImpureFun p) e' $ insertAssoc (Assoc x e2) xs
    _ -> error "expectAST: the impossible happened"

expectAST p (App_ :$ es) xs =
    case es of
    e1 :* e2 :* End ->
        expectSynDir (ImpureFun p) e1 xs `apF` e2
    _ -> error "expectAST: the impossible happened"

expectAST p (Let_ :$ es) xs =
    case es of
    e1 :* e2 :* End ->
        caseBind e2 $ \x e' ->
        expectSynDir p e' $ insertAssoc (Assoc x e1) xs
    _ -> error "expectAST: the impossible happened"

expectAST p (Fix_ :$ es) xs =
    case es of
    e1 :* End ->
        caseBind e1 $ \x e' ->
        expectSynDir p e' $ insertAssoc (Assoc x $ syn (Fix_ :$ e1 :* End)) xs -- BUG: could loop
    _ -> error "expectAST: the impossible happened"

expectAST p (Ann_ _ :$ es) xs =
    case es of
    e :* End ->
        -- TODO: should we re-wrap it up in a type annotation?
        expectSynDir p e xs
    _ -> error "expectAST: the impossible happened"

expectAST p (PrimOp_ o :$ es) xs =
    case o of
    Index _ ->
        case es of
        arr :* ei :* End -> expectSynDir (ImpureArray p) arr xs `apA` ei
        _ -> error "expectAST: the impossible happened"

    Reduce a -> error "TODO: expectAST{Reduce}"
    
    _ -> case p of {}

expectAST p (NaryOp_     _ _)    _ = case p of {}
expectAST p (Value_      _)      _ = case p of {}
expectAST p (CoerceTo_   _ :$ _) _ = case p of {}
expectAST p (UnsafeFrom_ _ :$ _) _ = case p of {}
expectAST _ Empty_               _ =
    ExpectArray Text.empty (nat_ 0)
        $ error "expect: indexing an empty array"
    -- TODO: should we instead emit the AST for buggily indexing an empty array?
expectAST p (Array_ e1 e2) xs =
    caseBind e2 $ \x e' ->
    ExpectArray (varHint x) e1 $ \ei ->
    -- BUG: we should wrap this in a guard that @ei < e1@, instead of just performing the substitution arbitrarily.
    expectSynDir (unImpureArray p) e' $ insertAssoc (Assoc x ei) xs

expectAST p (Datum_ _)    _  = case p of {}
expectAST p (Case_  e bs) xs =
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

expectAST p (MeasureOp_ o :$ es) xs = expectMeasure p o es xs
expectAST p (MBind :$ es) xs =
    case es of
    e1 :* e2 :* End ->
        ExpectMeasure $ \c ->
        expectSynDir ImpureMeasure e1 xs `apM` \a ->
        caseBind e2 $ \x e' ->
        (expectSynDir p e' $ insertAssoc (Assoc x a) xs) `apM` c
    _ -> error "expectAST: the impossible happened"

expectAST p (Superpose_ es) xs =
    ExpectMeasure $ \c ->
    sum [ e1 * (expectSynDir p e2 xs `apM` c) | (e1, e2) <- es ]
    -- TODO: in the Lazy.tex paper, we use @denotation e1 xs@ and guard against that interpretation being negative...
    -- TODO: if @es@ is null, then automatically simplify to just 0

expectAST p (Lub_ es) xs =
    -- TODO: doing case analysis on @p@ is just a hack to try and get at least some things to work. We can probably get everything to work by doing induction on @p@, but it'd be better if we could grab the type of the whole case expression and do induction on that...
    case p of
    ImpureMeasure ->
        ExpectMeasure $ \c ->
        syn $ Lub_ [ expectSynDir p e xs `apM` c | e <- es ]
    _ -> error "TODO: expectAST{Lub_}"
    {-
    -- BUG: these don't typecheck. We need to push the @syn . Lub_@ down over @Expect abt@.
    ImpureFun _ ->
        ExpectFun Text.empty $ \e2 ->
        syn $ Lub_ [ expectSynDir p e xs `apF` e2 | e <- es]
    ImpureArray _ ->
        ExpectArray Text.empty (error "TODO: expectAST{Lub_}") $ \ei ->
        syn $ Lub_ [ expectSynDir p e xs `apA` ei | e <- es]
    -}

expectAST p (Expect :$ _) _ = case p of {}


expectBranch
    :: (ABT abt)
    => (abt '[] a -> abt '[] 'HProb)
    -> ImpureType ('HMeasure a)
    -> Assocs abt
    -> View abt xs ('HMeasure a)
    -> abt xs 'HProb
expectBranch c p xs (Syn  t)    = expectAST    p      t  xs `apM` c
expectBranch c p xs (Var  x)    = expectSynDir p (var x) xs `apM` c
expectBranch c p xs (Bind x e') = bind x $ expectBranch c p xs e'


-- BUG: none of these use the Assocs; they must, in case we need to substitute for variables in the SArgs. Or we need to residualize the Assocs into the program we're generating...
expectMeasure
    :: (ABT abt, typs ~ UnLCs args, args ~ LCs typs)
    => ImpureType a 
    -> MeasureOp typs a
    -> SArgs abt args
    -> Assocs abt
    -> Expect abt a
expectMeasure _ (Dirac _) es _ =
    case es of
    a :* End ->
        ExpectMeasure $ \c -> c a
    _ -> error "expectMeasure: the impossible happened"
expectMeasure _ Lebesgue es _ =
    case es of
    End ->
        ExpectMeasure $ \c ->
        integrate negativeInfinity infinity c
    _ -> error "expectMeasure: the impossible happened"
expectMeasure _ Counting es _ =
    case es of
    End ->
        ExpectMeasure $ \c ->
        summate negativeInfinity infinity c
    _ -> error "expectMeasure: the impossible happened"
expectMeasure _ Categorical es _ =
    case es of
    ps :* End ->
        ExpectMeasure $ \c ->
        let_ (summateV ps) $ \tot ->
        flip (if_ (prob_ 0 < tot)) (prob_ 0)
            $ summateV (mapWithIndex (\i p -> p * c i) ps) / tot
    _ -> error "expectMeasure: the impossible happened"
expectMeasure _ Uniform  es _ =
    case es of
    lo :* hi :* End ->
        ExpectMeasure $ \c ->
        integrate lo hi $ \x ->
            c x / unsafeProb (hi - lo)
    _ -> error "expectMeasure: the impossible happened"
expectMeasure _ Normal es _ =
    case es of
    mu :* sd :* End ->
        ExpectMeasure $ \c ->
        integrate negativeInfinity infinity $ \x ->
            exp (negate ((x - mu) ^ nat_ 2)
                / fromProb (prob_ 2 * sd ^ nat_ 2))
            / sd / sqrt (prob_ 2 * pi) * c x
    _ -> error "expectMeasure: the impossible happened"
expectMeasure _ Poisson es _ =
    case es of
    l :* End ->
        ExpectMeasure $ \c ->
        flip (if_ (prob_ 0 < l)) (prob_ 0)
            $ summate (real_ 0) infinity $ \x ->
                l ^^ x
                / gammaFunc (fromInt x + real_ 1)
                / exp (fromProb l)
                * c (unsafeFrom_ signed x)
    _ -> error "expectMeasure: the impossible happened"
expectMeasure _ Gamma es _ =
    case es of
    shape :* scale :* End ->
        ExpectMeasure $ \c ->
        integrate (real_ 0) infinity $ \x ->
            let x_ = unsafeProb x in
            x_ ** (fromProb shape - real_ 1)
            * exp (negate . fromProb $ x_ / scale)
            / (scale ** shape * gammaFunc shape)
            * c x_
    _ -> error "expectMeasure: the impossible happened"
expectMeasure _ Beta es _ =
    case es of
    a :* b :* End ->
        ExpectMeasure $ \c ->
        integrate (real_ 0) (real_ 1) $ \x ->
            let x_ = unsafeProb x in
            x_ ** (fromProb a - real_ 1)
            * (unsafeProb (real_ 1 - x) ** (fromProb b - real_ 1))
            / betaFunc a b * c (unsafeProb x)
    _ -> error "expectMeasure: the impossible happened"
expectMeasure _ (DirichletProcess _) es _ =
    case es of
    p :* m :* End ->
        ExpectMeasure $ \c ->
        error "TODO: expectMeasure{DirichletProcess}"
    _ -> error "expectMeasure: the impossible happened"
expectMeasure _ (Plate _) es _ =
    case es of
    ms :* End ->
        ExpectMeasure $ \c ->
        error "TODO: expectMeasure{Plate}"
    _ -> error "expectMeasure: the impossible happened"
expectMeasure _ (Chain _ _) es _ =
    case es of
    mz :* s0 :* End ->
        ExpectMeasure $ \c ->
        error "TODO: expectMeasure{Chain}"
    _ -> error "expectMeasure: the impossible happened"

----------------------------------------------------------------
----------------------------------------------------------- fin.
