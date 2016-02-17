{-# LANGUAGE DataKinds
           , TypeOperators
           , NoImplicitPrelude
           , FlexibleContexts
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.12.15
-- |
-- Module      :  Language.Hakaru.Inference
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- TODO: we may want to give these longer\/more-explicit names so
-- as to be a bit less ambiguous in the larger Haskell ecosystem.
----------------------------------------------------------------
module Language.Hakaru.Inference
    ( priorAsProposal
    , mh
    , mcmc
    , gibbsProposal
    , slice
    , sliceX
    , incompleteBeta
    , regBeta
    , tCDF
    , approxMh
    ) where

import Prelude (($), (.), error, Maybe(..))
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing (SingI())
import Language.Hakaru.Syntax.AST (Term)
import Language.Hakaru.Syntax.ABT (ABT)
import Language.Hakaru.Syntax.Prelude
import Language.Hakaru.Expect (normalize)
import Language.Hakaru.Disintegrate (determine, density, disintegrate)

----------------------------------------------------------------
----------------------------------------------------------------
priorAsProposal
    :: (ABT Term abt, SingI a, SingI b)
    => abt '[] ('HMeasure (HPair a b))
    -> abt '[] (HPair a b)
    -> abt '[] ('HMeasure (HPair a b))
priorAsProposal p x =
    bern (prob_ 0.5) >>= \c ->
    p >>= \x' ->
    dirac $
        if_ c
            (pair (fst x ) (snd x'))
            (pair (fst x') (snd x ))


-- We don't do the accept\/reject part of MCMC here, because @min@
-- and @bern@ don't do well in @simplify@! So we'll be passing the
-- resulting AST of 'mh' to 'simplify' before plugging that into
-- @mcmc@; that's why 'easierRoadmapProg4' and 'easierRoadmapProg4''
-- have different types.
--
-- TODO: the @a@ type should be pure (aka @a ~ Expect' a@ in the old parlance).
-- BUG: get rid of the SingI requirements due to using 'lam'
mh  :: (ABT Term abt, SingI a)
    => (abt '[] a -> abt '[] ('HMeasure a))
    -> abt '[] ('HMeasure a)
    -> abt '[] (a ':-> 'HMeasure (HPair a 'HProb))
mh proposal target =
    case determine $ density target of
    Nothing -> error "mh: couldn't get density"
    Just theDensity ->
        let_ theDensity $ \mu ->
        lam $ \old ->
            proposal old >>= \new ->
            dirac $ pair new (mu `app` {-pair-} new {-old-} / mu `app` {-pair-} old {-new-})


-- BUG: get rid of the SingI requirements due to using 'lam' in 'mh'
mcmc :: (ABT Term abt, SingI a)
    => (abt '[] a -> abt '[] ('HMeasure a))
    -> abt '[] ('HMeasure a)
    -> abt '[] (a ':-> 'HMeasure a)
mcmc proposal target =
    let_ (mh proposal target) $ \f ->
    lam $ \old ->
        app f old >>= \new_ratio ->
        new_ratio `unpair` \new ratio ->
        bern (min (prob_ 1) ratio) >>= \accept ->
        dirac (if_ accept new old)


gibbsProposal
    :: (ABT Term abt, SingI a, SingI b)
    => abt '[] ('HMeasure (HPair a b))
    -> abt '[] (HPair a b)
    -> abt '[] ('HMeasure (HPair a b))
gibbsProposal p xy =
    case determine $ disintegrate p of
    Nothing -> error "gibbsProposal: couldn't disintegrate"
    Just q ->
        xy `unpair` \x _y ->
        pair x <$> normalize (q `app` x)


-- Slice sampling can be thought of:
--
-- slice target x = do
--      u  <- uniform(0, density(target, x))
--      x' <- lebesgue
--      condition (density(target, x') >= u) true
--      return x'

slice
    :: (ABT Term abt)
    => abt '[] ('HMeasure 'HReal)
    -> abt '[] ('HReal ':-> 'HMeasure 'HReal)
slice target =
    case determine $ density target of
    Nothing -> error "slice: couldn't get density"
    Just densAt ->
        lam $ \x ->
        uniform (real_ 0) (fromProb $ app densAt x) >>= \u ->
        normalize $
        lebesgue >>= \x' ->
        withGuard (u < (fromProb $ app densAt x')) $
        dirac x'


sliceX
    :: (ABT Term abt, SingI a)
    => abt '[] ('HMeasure a)
    -> abt '[] ('HMeasure (HPair a 'HReal))
sliceX target =
    case determine $ density target of
    Nothing -> error "sliceX: couldn't get density"
    Just densAt ->
        target `bindx` \x ->
        uniform (real_ 0) (fromProb $ app densAt x)


incompleteBeta
    :: (ABT Term abt)
    => abt '[] 'HProb
    -> abt '[] 'HProb
    -> abt '[] 'HProb
    -> abt '[] 'HProb
incompleteBeta x a b =
    let one = real_ 1 in
    integrate (real_ 0) (fromProb x) $ \t ->
        unsafeProb t ** (fromProb a - one)
        * unsafeProb (one - t) ** (fromProb b - one)


regBeta -- TODO: rename 'regularBeta'
    :: (ABT Term abt)
    => abt '[] 'HProb
    -> abt '[] 'HProb
    -> abt '[] 'HProb
    -> abt '[] 'HProb
regBeta x a b = incompleteBeta x a b / betaFunc a b


tCDF :: (ABT Term abt) => abt '[] 'HReal -> abt '[] 'HProb -> abt '[] 'HProb
tCDF x v =
    let b = regBeta (v / (unsafeProb (x*x) + v)) (v / prob_ 2) (prob_ 0.5)
    in  unsafeProb $ real_ 1 - real_ 0.5 * fromProb b


-- BUG: get rid of the SingI requirements due to using 'lam'
approxMh
    :: (ABT Term abt, SingI a)
    => (abt '[] a -> abt '[] ('HMeasure a))
    -> abt '[] ('HMeasure a)
    -> [abt '[] a -> abt '[] ('HMeasure a)]
    -> abt '[] (a ':-> 'HMeasure a)
approxMh _ _ [] = error "TODO: approxMh for empty list"
approxMh proposal prior (x:xs) =
    case determine . density $ bindx prior proposal of
    Nothing -> error "approxMh: couldn't get density"
    Just theDensity ->
        lam $ \old ->
        let_ theDensity $ \mu ->
        unsafeProb <$> uniform (real_ 0) (real_ 1) >>= \u ->
        proposal old >>= \new ->
        let_ (u * mu `app` pair new old / mu `app` pair old new) $ \u0 ->
        let_ (l new new / l old old) $ \l0 ->
        let_ (tCDF (n - real_ 1) (udif l0 u0)) $ \delta ->
        if_ (delta < eps)
            (if_ (u0 < l0)
                (dirac new)
                (dirac old))
            (approxMh proposal prior xs `app` old)
    where
    n   = real_ 2000
    eps = prob_ 0.05
    udif l u = unsafeProb $ fromProb l - fromProb u
    l   = \d1 d2 -> prob_ 2 -- determine (density (\theta -> x theta))
