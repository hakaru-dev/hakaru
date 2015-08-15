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
--                                                    2015.08.11
-- |
-- Module      :  Language.Hakaru.Syntax.EasierRoadmap
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- This is a fork of "Examples.EasierRoadmap" to work with our new
-- AST. This module shouldn't actually be called what it is; it should keep the old name, once we switch everything over to using the new AST.
--
-- TODO: @runDisintegrate@, @simplify@, @density@, @runSample@
----------------------------------------------------------------
module Language.Hakaru.Syntax.EasierRoadmap where

import Prelude (($), (.), undefined, error, IO, Maybe(..))

import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.TypeEq (SingI)
import Language.Hakaru.Syntax.HClasses (HSemiring_)
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.Prelude

{-
import Language.Hakaru.Syntax
import Language.Hakaru.Lazy (Backward, runDisintegrate, density)
import Language.Hakaru.Expect (Expect')
import Language.Hakaru.Simplify (simplify)
import Language.Hakaru.Any (Any)
import Language.Hakaru.Sample
-}


easierRoadmapProg1
    :: (ABT abt)
    => abt '[]
        ('HMeasure (HPair (HPair 'HReal 'HReal) (HPair 'HProb 'HProb)))
easierRoadmapProg1 =
    -- TODO: make 'uniform' polymorphic so it works on HProb too
    unsafeProb <$> uniform (real_ 3) (real_ 8) >>= \noiseT ->
    unsafeProb <$> uniform (real_ 1) (real_ 4) >>= \noiseE ->
    normal (real_ 0) noiseT >>= \x1 ->
    normal x1 noiseE >>= \m1 ->
    normal x1 noiseT >>= \x2 ->
    normal x2 noiseE >>= \m2 ->
    dirac $ pair (pair m1 m2) (pair noiseT noiseE)


easierRoadmapProg2
    :: (ABT abt)
    => abt '[] (HPair 'HReal 'HReal)
    -> abt '[] ('HMeasure (HPair 'HProb 'HProb))
easierRoadmapProg2 = \m1m2 -> 
    m1m2 `unpair` \m1 m2 ->
    unsafeProb <$> uniform (real_ 3) (real_ 8) >>= \noiseT ->
    unsafeProb <$> uniform (real_ 1) (real_ 4) >>= \noiseE ->
    normal (real_ 0) noiseT >>= \x1 ->
    weight (undefined x1 noiseE m1) >> -- TODO by disintegration
    normal x1 noiseT >>= \x2 ->
    weight (undefined x2 noiseE m2) >> -- TODO by disintegration
    dirac (pair noiseT noiseE) -- BUG: can't use ($) because of precedence clashing with (>>)


easierRoadmapProg2', easierRoadmapProg2'out
    :: (ABT abt)
    => abt '[] (HPair 'HReal 'HReal ':-> 'HMeasure (HPair 'HProb 'HProb))
easierRoadmapProg2' =
    error "TODO" {-
    (head $ runDisintegrate $ \_ -> easierRoadmapProg1) `app` unit
    -- Using the irrefutable pattern @[d] = runDisintegrate...@ fails for me. ~wrengr
    -}
easierRoadmapProg2'out =
    (lam $ \_ -> -- TODO: this extraneous administrative redex should go away
    lam  $ \x1 ->
    x1 `unpair` \x2 x3 ->
    unsafeProb <$> uniform (real_ 3) (real_ 8) >>= \x4 ->
    unsafeProb <$> uniform (real_ 1) (real_ 4) >>= \x5 ->
    lebesgue >>= \x6 ->
    weight (exp (negate (x3 - x6) * (x3 - x6)
                   / fromProb (prob_ 2 * x5 ^ nat_ 2))
           / x5
           / sqrt (prob_ 2 * pi)) >>
    lebesgue >>= \x7 ->
    weight (exp (negate (x6 - x7) * (x6 - x7)
                   / fromProb (prob_ 2 * x4 ^ nat_ 2))
           / x4
           / sqrt (prob_ 2 * pi)) >>
    weight (exp (negate (x2 - x7) * (x2 - x7)
                   / fromProb (prob_ 2 * x5 ^ nat_ 2))
           / x5
           / sqrt (prob_ 2 * pi)) >>
    weight (exp (negate x7 * x7
                   / fromProb (prob_ 2 * x4 ^ nat_ 2))
           / x4
           / sqrt (prob_ 2 * pi)) >>
    dirac (pair x4 x5))
    `app` unit


easierRoadmapProg3
    :: (ABT abt)
    => abt '[] (HPair 'HReal 'HReal ':-> 'HMeasure (HPair 'HProb 'HProb))
easierRoadmapProg3 =
    lam $ \m1m2 ->
    m1m2 `unpair` \m1 m2 ->
    unsafeProb <$> uniform (real_ 3) (real_ 8) >>= \noiseT ->
    unsafeProb <$> uniform (real_ 1) (real_ 4) >>= \noiseE ->
    weight (undefined noiseT noiseE m1 m2) >> -- TODO by simplification
    dirac (pair noiseT noiseE)


{- TODO
easierRoadmapProg3'
    :: IO (Any (HPair 'HReal 'HReal ':-> 'HMeasure (HPair 'HProb 'HProb)))
easierRoadmapProg3' = simplify easierRoadmapProg2'
-}


easierRoadmapProg3'out
    :: (ABT abt)
    => abt '[] (HPair 'HReal 'HReal)
    -> abt '[] ('HMeasure (HPair 'HProb 'HProb))
easierRoadmapProg3'out m1m2 =
    weight (prob_ 5) >>
    -- HACK: N.B., this is the one place we don't use @(unsafeProb <$>)@
    uniform (real_ 3) (real_ 8) >>= \noiseT' ->
    uniform (real_ 1) (real_ 4) >>= \noiseE' ->
    weight (recip pi
        * exp ((fst m1m2 * fst m1m2 * (noiseT' * noiseT') * real_ 2
             + noiseT' * noiseT' * fst m1m2 * snd m1m2 * real_ (-2)
             + snd m1m2 * snd m1m2 * (noiseT' * noiseT')
             + noiseE' * noiseE' * (fst m1m2 * fst m1m2)
             + noiseE' * noiseE' * (snd m1m2 * snd m1m2))
            * recip (noiseT' * noiseT' * (noiseT' * noiseT')
             + noiseE' * noiseE' * (noiseT' * noiseT') * real_ 3
             + noiseE' * noiseE' * (noiseE' * noiseE'))
            * real_ (-0.5))
        * (unsafeProb
            ( noiseT' ^ nat_ 4
            + noiseE' ^ nat_ 2
                * noiseT' ^ nat_ 2
                * real_ 3
            + noiseE' ^ nat_ 4
            )) ** real_ (-0.5)
        * prob_ 0.1) >>
    dirac (pair (unsafeProb noiseT') (unsafeProb noiseE'))


-- This should be given by the client, not auto-generated by Hakaru.
proposal
    :: (ABT abt)
    => abt '[] (HPair 'HReal 'HReal)
    -> abt '[] (HPair 'HProb 'HProb)
    -> abt '[] ('HMeasure (HPair 'HProb 'HProb))
proposal _ ntne =
    ntne `unpair` \noiseTOld noiseEOld ->
    superpose
        [ (prob_ 0.5,
            unsafeProb <$> uniform (real_ 3) (real_ 8) >>= \noiseT ->
            dirac (pair noiseT noiseEOld))
        , (prob_ 0.5,
            unsafeProb <$> uniform (real_ 1) (real_ 4) >>= \noiseE ->
            dirac (pair noiseTOld noiseE))
        ]


-- The env thing is just a hack for dealing with the fact that free variables may change types. It's a huge tuple of all the freevars— eewww!! If we can get rid of that, then do so
--
-- BUG: the @env@ and @a@ types should be pure types (aka @t ~ Expect' t@ in the old parlance).
-- BUG: we also need @Backward a a@ for 'density'
-- BUG: get rid of the SingI requirements from using 'lam'
mh  :: (ABT abt, SingI env, SingI a)
    => (abt '[] env -> abt '[] a -> abt '[] ('HMeasure a))
    -> (abt '[] env -> abt '[] ('HMeasure a))
    -> abt '[] (env ':-> a ':-> 'HMeasure (HPair a 'HProb))
mh prop target =
    lam $ \env ->
    let_ (lam (d env)) $ \mu ->
    lam $ \old ->
        prop env old >>= \new ->
        dirac (pair new (mu `app` {-pair-} new {-old-} / mu `app` {-pair-} old {-new-}))
    where
    d:_ = error "TODO: density" (\env -> {-bindx-} (target env) {-(prop env)-})

sq :: (ABT abt, HSemiring_ a) => abt '[] a -> abt '[] a
sq x = x * x -- TODO: use 'square' instead

easierRoadmapProg4
    :: (ABT abt)
    => abt '[]
        (    HPair 'HReal 'HReal
        ':-> HPair 'HProb 'HProb
        ':-> 'HMeasure (HPair 'HProb 'HProb))
easierRoadmapProg4 = 
    lam $ \m1m2 ->
    lam $ \ntne ->
    m1m2 `unpair` \m1 m2 ->
    ntne `unpair` \noiseTOld noiseEOld ->
    bern (prob_ 0.5) >>= \b ->
    (if_ b
      ( unsafeProb <$> uniform (real_ 3) (real_ 8) >>= \noiseT ->
        dirac $ pair noiseT noiseEOld)
      ( unsafeProb <$> uniform (real_ 1) (real_ 4) >>= \noiseE ->
        dirac $ pair noiseTOld noiseE)
    ) >>= \ntne' ->
    bern (min (prob_ 1) (easyDens m1 m2 ntne' / easyDens m1 m2 ntne)) >>= \accept ->
    dirac $ if_ accept ntne' ntne
    where
    easyDens m1 m2 ntne =
        ntne `unpair` \nt ne ->
        let_ (fromProb nt) $ \nt' ->
        let_ (fromProb ne) $ \ne' ->
        recip pi
        * exp ((sq m1 * sq nt' * real_ 2
                    - sq nt' * m1 * m2 * real_ 2
                    + sq m2  * sq nt'
                    + sq ne' * sq m1
                    + sq ne' * sq m2)
                * recip (sq nt' * sq nt'
                    + sq ne' * sq nt' * real_ 3
                    + sq ne' * sq ne')
            * real_ (-0.5))
        * (unsafeProb
                ( nt' ^ nat_ 4
                + ne' ^ nat_ 2 * nt' ^ nat_ 2 * real_ 3
                + ne' ^ nat_ 4))
            ** prob_ (-0.5)
        * prob_ 0.1


easierRoadmapProg4'
    :: (ABT abt)
    => abt '[]
        (    HPair 'HReal 'HReal
        ':-> HPair 'HProb 'HProb
        ':-> 'HMeasure (HPair (HPair 'HProb 'HProb) 'HProb))
easierRoadmapProg4' = mh proposal easierRoadmapProg3'out

easierRoadmapProg4'out
    :: (ABT abt)
    => abt '[]
        (    HPair 'HReal 'HReal
        ':-> HPair 'HProb 'HProb
        ':-> 'HMeasure (HPair (HPair 'HProb 'HProb) 'HProb))
easierRoadmapProg4'out =
    lam $ \m1m2 ->
    lam $ \ntne ->
    m1m2 `unpair` \m1 m2 ->
    ntne `unpair` \noiseTOld noiseEOld ->
    let noiseTOld' = fromProb noiseTOld
        noiseEOld' = fromProb noiseEOld
    in superpose
        [(prob_ 0.5,
            uniform (real_ 1) (real_ 4) >>= \noiseE' ->
            dirac . pair (pair noiseTOld (unsafeProb noiseE')) $
                sqrt
                    (noiseTOld * noiseTOld * (noiseTOld * noiseTOld)
                    + noiseEOld * noiseEOld * (noiseTOld * noiseTOld) * prob_ 3
                    + noiseEOld * noiseEOld * (noiseEOld * noiseEOld)
                    )
                * if_
                    (if_ (noiseTOld < prob_ 3)
                        true
                        (noiseTOld == prob_ 3))
                    (prob_ 0)
                    (if_ (noiseTOld < prob_ 8)
                        (prob_ 1)
                        (prob_ 0))
                * exp
                    (   (noiseE' * noiseE' * (m1 * m1)
                        + noiseE' * noiseE' * (m2 * m2)
                        + m1 * m1 * fromProb (noiseTOld * noiseTOld * prob_ 2)
                        + m1 * m2 * fromProb (noiseTOld * noiseTOld) * real_ (-2)
                        + m2 * m2 * fromProb (noiseTOld * noiseTOld)
                        )
                    * recip
                        ( noiseE' * noiseE' * (noiseE' * noiseE')
                        + noiseE' * noiseE' * fromProb (noiseTOld * noiseTOld * prob_ 3)
                        + noiseTOld' * noiseTOld' * (noiseTOld' * noiseTOld')
                        )
                    * real_ (-0.5))
                * recip
                    (sqrt
                        (unsafeProb
                            (noiseE' ^ nat_ 4
                            + noiseE' ^ nat_ 2 * fromProb (noiseTOld * noiseTOld * prob_ 3)
                            + noiseTOld' ^ nat_ 4)))
                * if_
                    (if_ (noiseEOld < prob_ 4)
                        (if_ (prob_ 1 < noiseEOld)
                            (if_ (noiseTOld < prob_ 8)
                                (prob_ 3 < noiseTOld)
                                false)
                            false)
                        false)
                    (exp
                        (   ( m1 ^ nat_ 2 * fromProb (noiseTOld * noiseTOld * prob_ 2)
                            + m1 * m2 * fromProb (noiseTOld * noiseTOld) * real_ (-2)
                            + m2 ^ nat_ 2 * fromProb (noiseTOld * noiseTOld)
                            + m1 ^ nat_ 2 * fromProb (noiseEOld * noiseEOld)
                            + m2 ^ nat_ 2 * fromProb (noiseEOld * noiseEOld)
                            )
                        /   ( noiseTOld' ^ nat_ 4
                            + fromProb (noiseEOld * noiseEOld * (noiseTOld * noiseTOld) * prob_ 3)
                            + noiseEOld' ^ nat_ 4
                            )
                        * real_ (0.5))
                    )
                    infinity
        ), (prob_ 0.5,
            uniform (real_ 3) (real_ 8) >>= \noiseT' ->
            dirac . pair (pair (unsafeProb noiseT') noiseEOld) $
                sqrt
                    ( noiseTOld * noiseTOld * (noiseTOld * noiseTOld)
                    + noiseEOld * noiseEOld * (noiseTOld * noiseTOld) * prob_ 3
                    + noiseEOld * noiseEOld * (noiseEOld * noiseEOld)
                    )
                * if_
                    (if_ (noiseEOld < prob_ 1)
                        true
                        (noiseEOld == prob_ 1))
                    (prob_ 0)
                    (if_ (noiseEOld < prob_ 4)
                        (prob_ 1)
                        (prob_ 0))
                * exp (
                    ( noiseT' * noiseT' * (m1 * m1) * real_ 2
                    + noiseT' * noiseT' * m1 * m2 * real_ (-2)
                    + noiseT' * noiseT' * (m2 * m2)
                    + m1 * m1 * fromProb (noiseEOld * noiseEOld)
                    + m2 * m2 * fromProb (noiseEOld * noiseEOld)
                    )
                    * recip
                        ( noiseT' * noiseT' * (noiseT' * noiseT')
                        + noiseT' * noiseT' * fromProb (noiseEOld * noiseEOld * prob_ 3)
                        + noiseEOld' * noiseEOld' * (noiseEOld' * noiseEOld')
                        )
                    * real_ (-0.5))
                * recip
                    (sqrt
                        (unsafeProb
                            (noiseT' ^ nat_ 4
                            + noiseT' ^ nat_ 2 * fromProb (noiseEOld * noiseEOld * prob_ 3)
                            + noiseEOld' ^ nat_ 4)))
                * if_
                    (if_ (noiseEOld < prob_ 4)
                        (if_ (prob_ 1 < noiseEOld)
                            (if_ (noiseTOld < prob_ 8)
                                (prob_ 3 < noiseTOld)
                                false)
                            false)
                        false)
                    (exp (
                        ( m1 ^ nat_ 2 * fromProb (noiseTOld * noiseTOld * prob_ 2)
                        + m1 * m2 * fromProb (noiseTOld * noiseTOld) * real_ (-2)
                        + m2 ^ nat_ 2 * fromProb (noiseTOld * noiseTOld)
                        + m1 ^ nat_ 2 * fromProb (noiseEOld * noiseEOld)
                        + m2 ^ nat_ 2 * fromProb (noiseEOld * noiseEOld)
                        )
                        /   ( noiseTOld' ^ nat_ 4
                            + fromProb (noiseEOld * noiseEOld * (noiseTOld * noiseTOld) * prob_ 3)
                            + noiseEOld' ^ nat_ 4
                            )
                        * real_ 0.5)
                    )
                    infinity
        )]

-- BUG: remove the SingI requirement coming from (>>=)
-- TODO: this is essentially @replicateM@, just with a better argument order. When adding this to whatever library, we should call it something like that.
makeChain
    :: (ABT abt, SingI a)
    => abt '[] 'HNat
    -> abt '[] a
    -> abt '[] (a ':-> 'HMeasure a)
    -> abt '[] ('HMeasure ('HArray a))
makeChain n s0 m =
    fst <$>
        chain (array n $ \ _ ->
            lam $ \s' ->
            dup <$> (m `app` s'))
        `app` s0
    where
    dup x = pair x x

-- "Language.Hakaru.Sample"
runSample
    :: (ABT abt)
    => abt '[] ('HMeasure a)
    -> IO (Maybe (abt '[] a))
runSample = error "TODO: runSample"

runEasierRoadmapProg4
    :: (ABT abt)
    => IO (Maybe (abt '[] ('HArray (HPair 'HProb 'HProb))))
runEasierRoadmapProg4 =
    runSample $
        makeChain (nat_ 20) (pair (prob_ 4) (prob_ 2))
            (easierRoadmapProg4 `app` pair (real_ 0) (real_ 1))
