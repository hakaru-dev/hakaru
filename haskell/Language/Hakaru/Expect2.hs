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

import           Prelude   (($), (.), flip, map, error, Either(..), return)
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
import Language.Hakaru.Evaluation.Lazy
import Language.Hakaru.Evaluation.EvalMonad

----------------------------------------------------------------

-- | Convert an arbitrary measure into a probability measure; i.e.,
-- reweight things so that the total weight\/mass is 1.
normalize
    :: (ABT Term abt) => abt '[] ('HMeasure a) -> abt '[] ('HMeasure a)
normalize m = withWeight (recip $ total m) m


-- | Compute the total weight\/mass of a measure.
total :: (ABT Term abt) => abt '[] ('HMeasure a) -> abt '[] 'HProb
total m = expect m $ \_ -> prob_ 1


-- TODO: shouldn't the continuation be a Hakaru function? so that
-- the type explicitly captures that it has to be a measurable
-- function we're integrating over? (Yes, yes, we want to avoid
-- administrative redexes; but we can do that ourselves just fine
-- without losing the type safety.) N.B., the residualized 'Expect'
-- is treated as a binding form, rather than taking a second argument
-- of function type. N.B., treating the continuation as either a
-- Hakaru function or as a locally-open term would also let us
-- guarantee that the call to 'runEval' correctly initializes the
-- heap to avoid capturing free variables in the body of the function
-- being integrated!!
--
-- TODO: is it actually a _measurable_ function from measurable-functions
-- to probs? If so, shouldn't we also capture that in the types?
--
-- | Convert a measure into its integrator.
expect
    :: (ABT Term abt)
    => abt '[] ('HMeasure a)
    -> (abt '[] a -> abt '[] 'HProb)
    -> abt '[] 'HProb
expect e c = runEval (expectTerm e c) [Some2 e]


----------------------------------------------------------------
-- BUG: really rather than using 'pureEvaluate' itself, we should have our own similar version which pushes the @expect _ c@ under the branches; in lieu of allowing 'defaultCaseEvaluator' to return a 'Neutral' term. How can we get this to work right? Seems like a common problem to have since the backwards disintegrator(s) have to do it too.

-- N.B., in the ICFP 2015 pearl paper, we took the expectation of bound variables prior to taking the expectation of their scope. E.g., @expect(let_ v e1 e2) xs c = expect e1 xs $ \x -> expect e2 (insertAssoc v x xs) c@. Whereas here, I'm being lazier and performing the expectation on variable lookup. This delayed evaluation preserves the expectation semantics (ICFP 2015, §5.6.0) whenever (1) the variable is never used (by wasted computation), or (2) used exactly once (by Tonelli's theorem); so we only need to worry if (3) the variable is used more than once, in which case we'll have to worry about whether the various integrals commute/exchange with one another. More generally, cf. Bhat et al.'s \"active variables\"

expectTerm
    :: (ABT Term abt)
    => abt '[] ('HMeasure a)
    -> (abt '[] a -> abt '[] 'HProb)
    -> Eval abt (abt '[] 'HProb)
expectTerm e c = do
    w <- pureEvaluate e
    case w of
        Neutral e' ->
            case typeOf e' of
            SMeasure a ->
                return $ syn (Expect :$ e' :* binder Text.empty a c :* End)
            _ -> error "expect: the impossible happened"
        Head_ v ->
            case v of
            WLiteral    _   -> error "expect: the impossible happened"
            WCoerceTo   _ _ -> error "expect: the impossible happened"
            WUnsafeFrom _ _ -> error "expect: the impossible happened"

            WMeasureOp o es -> return $ expectMeasureOp o es c
            WDirac e1       -> return $ c e1
            WMBind e1 e2    ->
                -- BUG: the new continuation we're passing to @expectTerm e1@ has 'Eval' type in the result...
                expectTerm e1 $ \e3 ->
                    expectTerm (syn (Let_ :$ e3 :* e2 :* End)) c
                    -- Or, equivalently we could 'caseBind' @e2@ and push the 'SLet' directly, rather than relying on the initial 'pureEvaluate' of the recursive 'expectTerm' to do it for us.
            WPlate e1 e2    -> error "TODO: expect{Plate}"
            WChain e1 e2 e3 -> error "TODO: expect{Chain}"
            WSuperpose pes  -> expectSuperpose pes c


-- N.B., we guarantee that each @e@ is called with the same heap
-- @h@ and emission-continuation @k@ (in addition to passing them
-- all the same function being integrated @c@).
--
-- BUG: the result of 'unEval' at @k@ and @h@ is some existential type; not prob. Should we identify @c@ with @k@, or define yet another monad (like 'Eval' but monomorphic at the final return type of Prob)?
expectSuperpose
    :: (ABT Term abt)
    => [(abt '[] 'HProb, abt '[] ('HMeasure a))]
    -> (abt '[] a -> abt '[] 'HProb)
    -> Eval abt (abt '[] 'HProb)
expectSuperpose pes c =
    Eval $ \k h -> sum [ p * unEval (expectTerm e c) k h | (p,e) <- pes]
    -- TODO: in the Lazy.tex paper, we use @denotation e1 h@ and guard against that interpretation being negative...
    -- TODO: if @es@ is null, then automatically simplify to just 0


expectMeasureOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => MeasureOp typs a
    -> SArgs abt args
    -> (abt '[] a -> abt '[] 'HProb)
    -> abt '[] 'HProb
expectMeasureOp Lebesgue = \End c ->
    integrate negativeInfinity infinity c
expectMeasureOp Counting = \End c ->
    summate negativeInfinity infinity c
expectMeasureOp Categorical = \(ps :* End) c ->
    let_ (summateV ps) $ \tot ->
    if_ (zero < tot)
        (summateV (mapWithIndex (\i p -> p * c i) ps) / tot)
        zero
expectMeasureOp Uniform = \(lo :* hi :* End) c ->
    integrate lo hi $ \x ->
        densityUniform lo hi x * c x
expectMeasureOp Normal = \(mu :* sd :* End) c ->
    integrate negativeInfinity infinity $ \x ->
        densityNormal mu sd x * c x
expectMeasureOp Poisson = \(l :* End) c ->
    if_ (zero < l)
        (summate zero infinity $ \x ->
            let x_ = unsafeFrom_ signed x in
            densityPoisson l x_ * c x_)
        zero
expectMeasureOp Gamma = \(shape :* scale :* End) c ->
    integrate zero infinity $ \x ->
        let x_ = unsafeProb x in
        densityGamma shape scale x_ * c x_
expectMeasureOp Beta = \(a :* b :* End) c ->
    integrate zero one $ \x ->
        let x_ = unsafeProb x in
        densityBeta a b x_ * c x_

----------------------------------------------------------------
----------------------------------------------------------- fin.
