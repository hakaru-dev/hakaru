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

import           Prelude (($), (.), flip, map, error, Maybe(..), Either(..))
import           Data.IntMap   (IntMap)
import qualified Data.IntMap   as IM
import qualified Data.Text     as Text

import Language.Hakaru.Syntax.IClasses (fmap21)
import Language.Hakaru.Syntax.Nat      (fromNat)
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.TypeEq
import Language.Hakaru.Syntax.Coercion
import Language.Hakaru.Syntax.AST
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
expect e = apM $ expectSynDir ImpureMeasure e IM.empty
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
test2 = syn . Lam_ . bind x . total $ var x 
    where
    x = Variable (Name (Text.pack "x") 2) (SMeasure SProb)
-- TODO: we'd rather use @lam $ \x -> total x@ but that causes 'binder' to throw a <<loop>> exception, presumably because 'expect' needs to force variable IDs to store them in the Env. Is there any way to work around that so we don't need to manually generate our own variable? Maybe by explicitly using the 'Expect' primop, and then performing the evaluation of that primop after 'binder' has finished constructing the first-order AST; but how can we specify that order of evaluation (except by making the evaluation of 'Expect' as 'expect' explicit)?


-- TODO: we'd rather use @lam $ \x -> total (x `app` int_ 3)@
test3 :: TrivialABT '[] (('HInt ':-> 'HMeasure 'HProb) ':-> 'HProb)
test3 = syn . Lam_ . bind x . total $ (var x `app` int_ 3)
    where
    x = Variable (Name (Text.pack "x") 2) (SFun SInt $ SMeasure SProb)

test4 :: TrivialABT '[] 'HProb
test4 = total $ if_ true (dirac unit) (weight (prob_ 5) >> dirac unit)

-- TODO: this one still doesn't work at all. Need to finish fixing 'pLeft' and 'pRight' so that they typecheck again.
-- TODO: also need to fix the @Show1 AST@ instance so that it can print 'Datum_'. That's why we have to abstract over @x@ instead of just saying @left_ unit@ or the like
test5 :: TrivialABT '[] (HEither HUnit HUnit ':-> 'HProb)
test5 =
    lam $ \x ->
        total $
            uneither x
            (\_ -> dirac unit)
            (\_ -> weight (prob_ 5) >> dirac unit)


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
-- N.B., in the ICFP 2015 pearl paper, we took the expectation of bound variables prior to taking the expectation of their scope. E.g., @expect(let_ v e1 e2) xs c = expect e1 xs $ \x -> expect e2 (pushEnv v x xs) c@. Whereas here, I'm being lazier and performing the expectation on variable lookup. This delayed evaluation preserves the expectation semantics (ICFP 2015, §5.6.0) whenever (1) the variable is never used (by wasted computation), or (2) used exactly once (by Tonelli's theorem); so we only need to worry if (3) the variable is used more than once, in which case we'll have to worry about whether the various integrals commute/exchange with one another. More generally, cf. Bhat et al.'s \"active variables\"


-- TODO: Move all this Env stuff to ABT.hs so it can be reused everywhere we want some sort of evaluation environment.
-- BUG: Make sure this has the correct capture-avoiding behavior!!


-- | A single association pair in our environment\/heap.
data Assoc :: ([Hakaru] -> Hakaru -> *) -> * where
    Assoc :: {-# UNPACK #-} !(Variable a) -> abt '[] a -> Assoc abt
    -- TODO: is there any way we can be sure to maintain CSE? Maybe by inserting a 'Let_' the first time we do a lookup, destructively changing the environment so that subsequent lookups will reuse the 'Let_'-bound variable? That's not guaranteed to have the proper variable scoping\/binding however...
    
    -- TODO: store the @Expect abt a@ instead? Or store both?
    -- TODO: have two different versions of variable lookup? (one for when we need to take the expectation of the variable, and one for just plugging things into place)


-- BUG: since multiple 'varEq'-distinct variables could have the
-- same ID, we should really have the elements be a list of
-- associations (or something more efficient; e.g., if 'Sing' is
-- hashable).
type Env abt = IntMap (Assoc abt)

-- If we actually do have a list (etc) of variables for each ID, and want to add the new binding to whatever old ones, then it looks like there's no way to do that in one pass of both the IntMap and the list.
pushEnv :: Assoc abt -> Env abt -> Env abt
pushEnv v@(Assoc x _) xs =
    case IM.insertLookupWithKey (\_ v' _ -> v') (fromNat $ varID x) v xs of
    (Nothing, xs') -> xs'
    (Just _,  _)   -> error "pushEnv: variable is already assigned!"

-- N.B., it's up to 'varEq' to say whether we actually found the
-- right variable or not.
lookupEnv :: Variable a -> Env abt -> Maybe (abt '[] a)
lookupEnv x xs = do
    Assoc x' e' <- IM.lookup (fromNat $ varID x) xs
    Refl <- varEq x x'
    Just e'
{-
-- for @Env abt = IntMap [Assoc abt]@ this should work:
lookupEnv =
    \x xs -> do
        assocs <- IM.lookup (fromNat $ varID x) xs
        go x assocs
    where
    go x []                     = Nothing
    go x (Assoc x' e' : assocs) =
        case varEq x x' of
        Just Refl -> Just e'
        Nothing   -> go x assocs
-}

-- TODO: Swap the argument order?
-- | If the expression is a variable, then look it up. Recursing
-- until we can finally return some syntax.
resolveVar
    :: (ABT abt)
    => abt '[] a
    -> Env abt
    -> Either (Variable a) (AST abt a)
resolveVar e xs =
    flip (caseVarSyn e) Right $ \x ->
        case lookupEnv x xs of
        Just e' -> resolveVar e' xs
        Nothing -> Left x


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
    -> Env abt
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
    primOp2_ (Expect a) e (lamWithType a c)


expectAST
    :: (ABT abt)
    => ImpureType a -- N.B., should be lazy\/irrelevant in this argument
    -> AST abt a
    -> Env abt
    -> Expect abt a
expectAST p (Lam_ e1) xs =
    caseBind e1 $ \x e' ->
    ExpectFun (varHint x) $ \e2 ->
    expectSynDir (unImpureFun p) e' $ pushEnv (Assoc x e2) xs

expectAST p (App_ e1 e2) xs =
    expectSynDir (ImpureFun p) e1 xs `apF` e2

expectAST p (Let_ e1 e2) xs =
    caseBind e2 $ \x e' ->
    expectSynDir p e' $ pushEnv (Assoc x e1) xs

expectAST p (Fix_ e1) xs =
    caseBind e1 $ \x e' ->
    expectSynDir p e' $ pushEnv (Assoc x . syn $ Fix_ e1) xs -- BUG: could loop

expectAST p (Ann_ _ e) xs =
    -- TODO: should we re-wrap it up in a type annotation?
    expectSynDir p e xs

expectAST p (PrimOp_ o) xs =
    case o of
    Index _ ->
        ExpectFun Text.empty $ \arr ->
        ExpectFun Text.empty $ \ei ->
        let p' = ImpureArray . unImpureFun $ unImpureFun p
        in  expectSynDir p' arr xs `apA` ei

    Reduce a -> error "TODO: expectAST{Reduce}"
    
    _ -> case p of {}

expectAST p (NaryOp_     _ _) _ = case p of {}
expectAST p (Value_      _)   _ = case p of {}
expectAST p (CoerceTo_   _ _) _ = case p of {}
expectAST p (UnsafeFrom_ _ _) _ = case p of {}
expectAST _ Empty_            _ =
    ExpectArray Text.empty (nat_ 0)
        $ error "expect: indexing an empty array"
    -- TODO: should we instead emit the AST for buggily indexing an empty array?
expectAST p (Array_ e1 e2) xs =
    caseBind e2 $ \x e' ->
    ExpectArray (varHint x) e1 $ \ei ->
    -- BUG: we should wrap this in a guard that @ei < e1@, instead of just performing the substitution arbitrarily.
    expectSynDir (unImpureArray p) e' $ pushEnv (Assoc x ei) xs

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

expectAST _ (Measure_    o)     _  = expectMeasure o
expectAST p (Bind_       e1 e2) xs =
    ExpectMeasure $ \c ->
    expectSynDir ImpureMeasure e1 xs `apM` \a ->
    caseBind e2 $ \x e' ->
    (expectSynDir p e' $ pushEnv (Assoc x a) xs) `apM` c

expectAST p (Superpose_ es) xs =
    ExpectMeasure $ \c ->
    sum [ e1 * (expectSynDir p e2 xs `apM` c) | (e1, e2) <- es ]
    -- TODO: in the Lazy.tex paper, we use @denotation e1 xs@ and guard against that interpretation being negative...
    -- TODO: if @es@ is null, then automatically simplify to just 0



expectBranch
    :: (ABT abt)
    => (abt '[] a -> abt '[] 'HProb)
    -> ImpureType ('HMeasure a)
    -> Env abt
    -> View abt xs ('HMeasure a)
    -> abt xs 'HProb
expectBranch c p xs (Syn  t)    = expectAST    p      t  xs `apM` c
expectBranch c p xs (Var  x)    = expectSynDir p (var x) xs `apM` c
expectBranch c p xs (Bind x e') = bind x $ expectBranch c p xs e'



expectMeasure :: (ABT abt) => Measure a -> Expect abt a
expectMeasure (Dirac _) =
    ExpectFun Text.empty $ \a ->
    ExpectMeasure $ \c -> c a
expectMeasure Lebesgue    =
    ExpectMeasure $ \c ->
    integrate negativeInfinity infinity c
expectMeasure Counting    =
    ExpectMeasure $ \c ->
    summate   negativeInfinity infinity c
expectMeasure Categorical =
    ExpectFun Text.empty $ \ps ->
    ExpectMeasure $ \c ->
    let_ (summateV ps) $ \tot ->
    flip (if_ (prob_ 0 < tot)) (prob_ 0)
        $ summateV (mapWithIndex (\i p -> p * c i) ps) / tot
expectMeasure Uniform =
    ExpectFun Text.empty $ \lo ->
    ExpectFun Text.empty $ \hi ->
    ExpectMeasure $ \c ->
    integrate lo hi $ \x ->
        c x / unsafeProb (hi - lo)
expectMeasure Normal =
    ExpectFun Text.empty $ \mu ->
    ExpectFun Text.empty $ \sd ->
    ExpectMeasure $ \c ->
    integrate negativeInfinity infinity $ \x ->
        exp (negate ((x - mu) ^ nat_ 2)
            / fromProb (prob_ 2 * sd ** real_ 2))
        / sd / sqrt (prob_ 2 * pi) * c x
expectMeasure Poisson =
    ExpectFun Text.empty $ \l ->
    ExpectMeasure $ \c ->
    flip (if_ (prob_ 0 < l)) (prob_ 0)
        $ summate (real_ 0) infinity $ \x ->
            l ** fromInt x
            / gammaFunc (fromInt x + real_ 1)
            / exp (fromProb l)
            * c (unsafeFrom_ signed x)
expectMeasure Gamma =
    ExpectFun Text.empty $ \shape ->
    ExpectFun Text.empty $ \scale ->
    ExpectMeasure $ \c ->
    integrate (real_ 0) infinity $ \x ->
        let x_ = unsafeProb x in
        x_ ** (fromProb shape - real_ 1)
        * exp (negate . fromProb $ x_ / scale)
        / (scale ** shape * gammaFunc shape)
        * c x_
expectMeasure Beta =
    ExpectFun Text.empty $ \a ->
    ExpectFun Text.empty $ \b ->
    ExpectMeasure $ \c ->
    integrate (real_ 0) (real_ 1) $ \x ->
        let x_ = unsafeProb x in
        x_ ** (fromProb a - real_ 1)
        * (unsafeProb (real_ 1 - x) ** (fromProb b - real_ 1))
        / betaFunc a b * c (unsafeProb x)
expectMeasure (DirichletProcess _) =
    ExpectFun Text.empty $ \p ->
    ExpectFun Text.empty $ \m ->
    ExpectMeasure $ \c ->
    error "TODO: expectMeasure{DirichletProcess}"
expectMeasure (Plate _) =
    ExpectFun Text.empty $ \ms ->
    ExpectMeasure $ \c ->
    error "TODO: expectMeasure{Plate}"
expectMeasure (Chain _ _) =
    ExpectFun Text.empty $ \mz ->
    ExpectFun Text.empty $ \s0 ->
    ExpectMeasure $ \c ->
    error "TODO: expectMeasure{Chain}"

----------------------------------------------------------------
----------------------------------------------------------- fin.
