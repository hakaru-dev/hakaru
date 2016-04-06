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
--                                                    2016.04.05
-- |
-- Module      :  Language.Hakaru.Expect2
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
--
----------------------------------------------------------------
module Language.Hakaru.Expect2
    ( normalize
    , total
    , expect
    ) where

import           Prelude   (($), (.), error, return)
import qualified Data.Text as Text
import Data.Functor ((<$>))

import Language.Hakaru.Syntax.IClasses (Some2(..))
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST hiding (Expect)
import qualified Language.Hakaru.Syntax.AST as AST
import Language.Hakaru.Syntax.TypeOf (typeOf)
import qualified Language.Hakaru.Syntax.Prelude as P
import Language.Hakaru.Evaluation.Types
import Language.Hakaru.Evaluation.ExpectMonad (Expect(..), runExpect, pureEvaluate, emit, emit_)

----------------------------------------------------------------

-- | Convert an arbitrary measure into a probability measure; i.e.,
-- reweight things so that the total weight\/mass is 1.
normalize
    :: (ABT Term abt) => abt '[] ('HMeasure a) -> abt '[] ('HMeasure a)
normalize m = P.withWeight (P.recip $ total m) m


-- | Compute the total weight\/mass of a measure.
total :: (ABT Term abt) => abt '[] ('HMeasure a) -> abt '[] 'HProb
total m =
    expect m . binder Text.empty (sUnMeasure $ typeOf m) $ \_ -> P.one

-- TODO: is it actually a _measurable_ function from measurable-functions
-- to probs? If so, shouldn't we also capture that in the types?
--
-- | Convert a measure into its integrator. N.B., the second argument
-- is (a representation of) a measurable function from @a@ to
-- 'HProb@. We represent it as a binding form rather than as @abt
-- '[] (a ':-> 'HProb)@ in order to avoid introducing administrative
-- redexes. We could, instead, have used a Haskell function @abt
-- '[] a -> abt '[] 'HProb@ to eliminate the administrative redexes,
-- but that would introduce other implementation difficulties we'd
-- rather avoid.
expect
    :: (ABT Term abt)
    => abt '[] ('HMeasure a)
    -> abt '[a] 'HProb
    -> abt '[] 'HProb
expect e f = runExpect (expectTerm e) f [Some2 e, Some2 f]


residualizeExpect
    :: (ABT Term abt)
    => abt '[] ('HMeasure a)
    -> Expect abt (abt '[] a)
residualizeExpect e =
    var <$> emit Text.empty (sUnMeasure $ typeOf e)
        (\c -> syn (AST.Expect :$ e :* c :* End))

-- This version checks whether the first argument is a variable or not, avoiding the extraneous let binding as appropriate. We also avoid using 'binder', which is good because it constructs the term more directly, but is bad because we make no guarantees about hygiene! We expect callers to handle that.
-- TODO: move this elsewhere, so that 'runExpect' can use it.
-- TODO: make even smarter so that we drop the let binding in case @f@ doesn't actually use it?
let_ :: (ABT Term abt) => abt '[] a -> abt '[a] b -> abt '[] b
let_ e f =
    caseVarSyn e
        (\x -> caseBind f $ \y f' -> subst y (var x) f')
        (\_ -> syn (Let_ :$ e :* f :* End))
            

----------------------------------------------------------------
-- BUG: really rather than using 'pureEvaluate' itself, we should
-- have our own similar version which pushes the @expect _ c@ under
-- the branches; in lieu of allowing 'defaultCaseEvaluator' to
-- return a 'Neutral' term. How can we get this to work right? Seems
-- like a common problem to have since the backwards disintegrator(s)
-- have to do it too.


-- N.B., in the ICFP 2015 pearl paper, we took the expectation of
-- bound variables prior to taking the expectation of their scope.
-- E.g., @expect(let_ v e1 e2) xs c = expect e1 xs $ \x -> expect
-- e2 (insertAssoc v x xs) c@. Whereas here, I'm being lazier and
-- performing the expectation on variable lookup. This delayed
-- evaluation preserves the expectation semantics (ICFP 2015, §5.6.0)
-- whenever (1) the variable is never used (by wasted computation),
-- or (2) used exactly once (by Tonelli's theorem); so we only need
-- to worry if (3) the variable is used more than once, in which
-- case we'll have to worry about whether the various integrals
-- commute/exchange with one another. More generally, cf. Bhat et
-- al.'s \"active variables\"


expectTerm
    :: (ABT Term abt)
    => abt '[] ('HMeasure a)
    -> Expect abt (abt '[] a)
expectTerm e = do
    w <- pureEvaluate e
    case w of
        Neutral e'              -> residualizeExpect e'
        Head_ (WLiteral    _)   -> error "expect: the impossible happened"
        Head_ (WCoerceTo   _ _) -> error "expect: the impossible happened"
        Head_ (WUnsafeFrom _ _) -> error "expect: the impossible happened"
        Head_ (WMeasureOp o es) -> expectMeasureOp o es
        Head_ (WDirac e1)       -> return e1
        Head_ (WMBind e1 e2)    -> do
            v1 <- expectTerm e1
            expectTerm (let_ v1 e2)
            {-
            -- BUG: the new continuation we're passing to @expectTerm e1@ has 'Eval' type in the result. Really the issue here is that whatever new 'SLet' bindings are introduced in the nested call need to be residualized immediately around the nested call, instead of left on the heap for being residualized further up. Conversely, we cannot allow any 'SLet' bindings in the initial heap given to the nested call to be residualized there; since that would cause hygiene errors.
            caseBind e2 $ \x e2' -> do
            y <- freshenVar x
            expectTerm e1 . bind y $
                -- TODO: store the variable renaming in the 'Eval' monad so as to perform it lazily.
                expectTerm (subst x (var y) e2') c
            -}
        Head_ (WPlate _ _)     -> error "TODO: expect{Plate}"
        Head_ (WChain _ _ _)   -> error "TODO: expect{Chain}"
        Head_ (WSuperpose pes) -> expectSuperpose pes


-- N.B., we guarantee that each @e@ is called with the same heap
-- @h@ and emission-continuation @k@ (in addition to passing them
-- all the same function being integrated @c@).
--
-- BUG: the result of 'unEval' at @k@ and @h@ is some existential
-- type; not prob. Should we identify @c@ with @k@, or define yet
-- another monad (like 'Eval' but monomorphic at the final return
-- type of Prob)?
expectSuperpose
    :: (ABT Term abt)
    => [(abt '[] 'HProb, abt '[] ('HMeasure a))]
    -> Expect abt (abt '[] a)
expectSuperpose pes =
    -- BUG: we can't really merge the heaps afterwards... Also, this seems to loop...
    Expect $ \c h ->
        P.sum [ p P.* unExpect (expectTerm e) c h | (p,e) <- pes]
    -- BUG: in the Lazy.tex paper, we use @denotation p h@. We need that here too since @p@ may use variables bound in @h@!!
    -- TODO: in the Lazy.tex paper, we guard against that interpretation being negative...
    -- TODO: if @es@ is null, then automatically simplify to just 0


-- BUG: we assume the arguments are emissible!
emitIntegrate
    :: (ABT Term abt)
    => abt '[] 'HReal
    -> abt '[] 'HReal
    -> Expect abt (Variable 'HReal)
emitIntegrate lo hi =
    emit Text.empty SReal (\c ->
        syn (Integrate :$ lo :* hi :* c :* End))

-- BUG: we assume the arguments are emissible!
emitSummate
    :: (ABT Term abt)
    => abt '[] 'HReal
    -> abt '[] 'HReal
    -> Expect abt (Variable 'HInt)
emitSummate lo hi =
    emit Text.empty SInt (\c ->
        syn (Summate :$ lo :* hi :* c :* End))

-- TODO: can we / would it help to, reuse 'let_'?
-- BUG: we assume the argument is emissible!
emitLet :: (ABT Term abt) => abt '[] a -> Expect abt (Variable a)
emitLet e =
    caseVarSyn e return $ \_ ->
        emit Text.empty (typeOf e) $ \f ->
            syn (Let_ :$ e :* f :* End)


-- TODO: introduce HProb variants of integrate\/summate so we can avoid the need for 'unsafeProb' here
expectMeasureOp
    :: forall abt typs args a
    .  (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => MeasureOp typs a
    -> SArgs abt args
    -> Expect abt (abt '[] a)
expectMeasureOp Lebesgue = \End ->
    var <$> emitIntegrate P.negativeInfinity P.infinity
expectMeasureOp Counting = \End ->
    var <$> emitSummate P.negativeInfinity P.infinity
expectMeasureOp Categorical = \(ps :* End) ->
    error "TODO: expectMeasureOp{Categorical}"
    {-
    let_ ps $ \ps' ->
    let_ (summateV ps') $ \tot ->
    if_ (zero < tot)
        (summateV (mapWithIndex (\i p -> p * inst c i) ps') / tot)
        zero
    -}
expectMeasureOp Uniform = \(lo :* hi :* End) -> do
    -- BUG: @(let_ zero $ \y -> uniform y one)@ doesn't work as desired; *drops* the @SLet y zero@ binding entirely!!
    lo' <- var <$> emitLet lo
    hi' <- var <$> emitLet hi
    x   <- var <$> emitIntegrate lo' hi'
    emit_ (P.densityUniform lo' hi' x P.*)
    return x
    {-
    let_ lo $ \lo' ->
    let_ hi $ \hi' ->
    integrate lo' hi' $ \x ->
        densityUniform lo' hi' x * inst c x
    -}
expectMeasureOp Normal = \(mu :* sd :* End) -> do
    -- HACK: for some reason w need to break apart the 'emit' and the 'emit_' or else we get a "<<loop>>" exception. Not entirely sure why, but it prolly indicates a bug somewhere.
    x <- var <$> emitIntegrate P.negativeInfinity P.infinity
    emit_ (P.densityNormal mu sd x P.*)
    return x
    {-
    \c ->
        P.integrate P.negativeInfinity P.infinity $ \x ->
            P.densityNormal mu sd x P.* let_ x c)
    -}
expectMeasureOp Poisson = \(l :* End) -> do
    l' <- var <$> emitLet l
    emit_ (\c -> P.if_ (P.zero P.< l') c P.zero)
    x  <- var <$> emitSummate P.zero P.infinity
    x_ <- var <$> emitLet (P.unsafeFrom_ signed x) -- TODO: Or is this small enough that we'd be fine using Haskell's "let" and so duplicating the coercion of a variable however often?
    emit_ (P.densityPoisson l' x_ P.*)
    return x_
    {-
    let_ l $ \l' ->
    if_ (zero < l')
        (summate zero infinity $ \x ->
            let x_ = unsafeFrom_ signed x in
            densityPoisson l' x_ * inst c x_)
        zero
    -}
expectMeasureOp Gamma = \(shape :* scale :* End) -> do
    x  <- var <$> emitIntegrate P.zero P.infinity
    x_ <- var <$> emitLet (P.unsafeProb x) -- TODO: Or is this small enough that we'd be fine using Haskell's "let" and so duplicating the coercion of a variable however often?
    emit_ (P.densityGamma shape scale x_ P.*)
    return x_
    {-
    integrate zero infinity $ \x ->
        let x_ = unsafeProb x in
        densityGamma shape scale x_ * inst c x_
    -}
expectMeasureOp Beta = \(a :* b :* End) -> do
    x  <- var <$> emitIntegrate P.zero P.one
    x_ <- var <$> emitLet (P.unsafeProb x) -- TODO: Or is this small enough that we'd be fine using Haskell's "let" and so duplicating the coercion of a variable however often?
    emit_ (P.densityBeta a b x_ P.*)
    return x_
    {-
    integrate zero one $ \x ->
        let x_ = unsafeProb x in
        densityBeta a b x_ * inst c x_
    -}

----------------------------------------------------------------
----------------------------------------------------------- fin.
