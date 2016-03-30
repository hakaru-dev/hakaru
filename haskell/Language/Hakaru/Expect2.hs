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
--                                                    2016.03.29
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

import Language.Hakaru.Syntax.IClasses (Some2(..))
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.TypeOf (typeOf)
import Language.Hakaru.Syntax.Prelude
import Language.Hakaru.Evaluation.Types
import Language.Hakaru.Evaluation.EvalMonad (Eval(..), runEval, pureEvaluate)

----------------------------------------------------------------

-- | Convert an arbitrary measure into a probability measure; i.e.,
-- reweight things so that the total weight\/mass is 1.
normalize
    :: (ABT Term abt) => abt '[] ('HMeasure a) -> abt '[] ('HMeasure a)
normalize m = withWeight (recip $ total m) m


-- | Compute the total weight\/mass of a measure.
total :: (ABT Term abt) => abt '[] ('HMeasure a) -> abt '[] 'HProb
total m =
    expect m . binder Text.empty (sUnMeasure $ typeOf m) $ \_ -> prob_ 1
    {-
    let x = Variable Text.empty 0 (sUnMeasure $ typeOf m)
    in expect m (bind x one)
    -}

-- TODO: is it actually a _measurable_ function from measurable-functions
-- to probs? If so, shouldn't we also capture that in the types?
--
-- | Convert a measure into its integrator. N.B., the second argument
-- is (a representation of) a measurable function from @a@ to
-- 'HProb@. We represent it as a binding form rather than as @abt
-- '[] (a ':-> 'HProb)@ in order to avoid introducing administrative
-- redexes. We could, instead, have used a Haskell function @abt
-- '[] a -> abt '[] 'HProb@ to eliminate the administrative redexes,
-- but this introduces other implementation difficulties we'd rather
-- avoid.
expect
    :: (ABT Term abt)
    => abt '[] ('HMeasure a)
    -> abt '[a] 'HProb
    -> abt '[] 'HProb
expect e c = runEval (expectTerm e c) [Some2 e, Some2 c]


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

-- TODO: actually use the version commented out in ABT.hs
inst
    :: (ABT Term abt)
    => abt '[a] b
    -> abt '[]  a
    -> abt '[]  b
inst = error "TODO: inst"


expectTerm
    :: (ABT Term abt)
    => abt '[] ('HMeasure a)
    -> abt '[a] 'HProb
    -> Eval abt (abt '[] 'HProb)
expectTerm e c = do
    w <- pureEvaluate e
    case w of
        Neutral e'              -> return $ syn (Expect :$ e' :* c :* End)
        Head_ (WLiteral    _)   -> error "expect: the impossible happened"
        Head_ (WCoerceTo   _ _) -> error "expect: the impossible happened"
        Head_ (WUnsafeFrom _ _) -> error "expect: the impossible happened"
        Head_ (WMeasureOp o es) -> return $ expectMeasureOp o es c
        Head_ (WDirac e1)       -> return $ inst c e1
        Head_ (WMBind e1 e2)    ->
            error "TODO"
            {-
            -- BUG: the new continuation we're passing to @expectTerm e1@ has 'Eval' type in the result...
            caseBind e2 $ \x e2' -> do
            y <- freshenVar x
            expectTerm e1 . bind y $
                -- TODO: store the variable renaming in the 'Eval' monad so as to perform it lazily.
                expectTerm (subst x (var y) e2') c
            -}
        Head_ (WPlate _ _)     -> error "TODO: expect{Plate}"
        Head_ (WChain _ _ _)   -> error "TODO: expect{Chain}"
        Head_ (WSuperpose pes) -> expectSuperpose pes c


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
    -> abt '[a] 'HProb
    -> Eval abt (abt '[] 'HProb)
expectSuperpose pes c =
    error "TODO"
    {-
    Eval $ \k h -> sum [ p * unEval (expectTerm e c) k h | (p,e) <- pes]
    -- TODO: in the Lazy.tex paper, we use @denotation e1 h@ and guard against that interpretation being negative...
    -- TODO: if @es@ is null, then automatically simplify to just 0
    -}


expectMeasureOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => MeasureOp typs a
    -> SArgs abt args
    -> abt '[a] 'HProb
    -> abt '[] 'HProb
expectMeasureOp Lebesgue = \End c ->
    integrate negativeInfinity infinity (inst c)
expectMeasureOp Counting = \End c ->
    summate negativeInfinity infinity (inst c)
expectMeasureOp Categorical = \(ps :* End) c ->
    let_ (summateV ps) $ \tot ->
    if_ (zero < tot)
        (summateV (mapWithIndex (\i p -> p * inst c i) ps) / tot)
        zero
expectMeasureOp Uniform = \(lo :* hi :* End) c ->
    integrate lo hi $ \x ->
        densityUniform lo hi x * inst c x
expectMeasureOp Normal = \(mu :* sd :* End) c ->
    integrate negativeInfinity infinity $ \x ->
        densityNormal mu sd x * inst c x
expectMeasureOp Poisson = \(l :* End) c ->
    if_ (zero < l)
        (summate zero infinity $ \x ->
            let x_ = unsafeFrom_ signed x in
            densityPoisson l x_ * inst c x_)
        zero
expectMeasureOp Gamma = \(shape :* scale :* End) c ->
    integrate zero infinity $ \x ->
        let x_ = unsafeProb x in
        densityGamma shape scale x_ * inst c x_
expectMeasureOp Beta = \(a :* b :* End) c ->
    integrate zero one $ \x ->
        let x_ = unsafeProb x in
        densityBeta a b x_ * inst c x_

----------------------------------------------------------------
----------------------------------------------------------- fin.
