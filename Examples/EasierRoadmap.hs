{-# LANGUAGE GADTs
           , EmptyCase
           , KindSignatures
           , DataKinds
           , TypeOperators
           , FlexibleContexts
           , NoImplicitPrelude
           , ScopedTypeVariables
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.29
-- |
-- Module      :  Examples.EasierRoadmap
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- TODO: come up with a story for @simplify@, @runSample@
-- TODO: actually finish implementing "Language.Hakaru.Syntax.Disintegrate"
----------------------------------------------------------------
module Examples.EasierRoadmap where

import Prelude (($), (.), return,
                undefined, error, IO, Maybe(..))

import qualified System.Random.MWC     as MWC
import qualified Data.Number.LogFloat  as LF()
import qualified Data.Vector           as V()
import Text.PrettyPrint (Doc)

import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Sing (SingI)
import Language.Hakaru.Syntax.HClasses (HSemiring_)
import Language.Hakaru.Syntax.ABT2
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Prelude
import Language.Hakaru.Disintegrate

import Language.Hakaru.Sample hiding (runSample)
import Language.Hakaru.PrettyPrint
import Language.Hakaru.Expect

{-
import Language.Hakaru.Syntax
import Language.Hakaru.Lazy (Backward, runDisintegrate, density)
import Language.Hakaru.Simplify (simplify)
import Language.Hakaru.Any (Any)
-}

easierRoadmapProg1
    :: (ABT AST abt)
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

easierRoadmapProg1', easierRoadmapProg1'' ::
    TrivialABT AST '[]
                ('HMeasure (HPair (HPair 'HReal 'HReal)
                                  (HPair 'HProb 'HProb)))

easierRoadmapProg1'  = easierRoadmapProg1
easierRoadmapProg1'' = normalize easierRoadmapProg1'

prettyEasierRoadmap1'' :: Doc
prettyEasierRoadmap1'' = pretty easierRoadmapProg1''

easierRoadmapProg2
    :: (ABT AST abt)
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
    :: (ABT AST abt)
    => abt '[] (HPair 'HReal 'HReal ':-> 'HMeasure (HPair 'HProb 'HProb))
easierRoadmapProg2' =
    determine (disintegrate easierRoadmapProg1)
    -- nee @head $ runDisintegrate $ \_ -> easierRoadmapProg1) `app` unit@
easierRoadmapProg2'out =
    (lam $ \_ -> -- TODO: this extraneous administrative redex should go away
    lam $ \x1 ->
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
    :: (ABT AST abt)
    => abt '[] (HPair 'HReal 'HReal ':-> 'HMeasure (HPair 'HProb 'HProb))
easierRoadmapProg3 =
    lam $ \m1m2 ->
    m1m2 `unpair` \m1 m2 ->
    unsafeProb <$> uniform (real_ 3) (real_ 8) >>= \noiseT ->
    unsafeProb <$> uniform (real_ 1) (real_ 4) >>= \noiseE ->
    weight (undefined noiseT noiseE m1 m2) >> -- TODO by simplification
    dirac (pair noiseT noiseE)


-- TODO: is this type even possible? Or must we put it into some monad?
simplify :: (ABT AST abt) => abt '[] a -> abt '[] a
simplify = error "TODO: simplify"

{- TODO
easierRoadmapProg3'
    :: IO (Any (HPair 'HReal 'HReal ':-> 'HMeasure (HPair 'HProb 'HProb)))
easierRoadmapProg3' = simplify easierRoadmapProg2'
-}


easierRoadmapProg3'out
    :: (ABT AST abt)
    => abt '[] (HPair 'HReal 'HReal)
    -> abt '[] ('HMeasure (HPair 'HProb 'HProb))
easierRoadmapProg3'out m1m2 =
    weight (prob_ 5) >>
    -- HACK: N.B., this is the one place we don't use @(unsafeProb <$>)@. Is only a concern for when implementing Prob as actually in the log-domain
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
    :: (ABT AST abt)
    => abt '[] (HPair 'HProb 'HProb)
    -> abt '[] ('HMeasure (HPair 'HProb 'HProb))
proposal ntne =
    ntne `unpair` \noiseTOld noiseEOld ->
    superpose
        [ (prob_ 0.5,
            unsafeProb <$> uniform (real_ 3) (real_ 8) >>= \noiseT ->
            dirac (pair noiseT noiseEOld))
        , (prob_ 0.5,
            unsafeProb <$> uniform (real_ 1) (real_ 4) >>= \noiseE ->
            dirac (pair noiseTOld noiseE))
        ]



-- We don't do the accept\/reject part of MCMC here, because @min@ and @bern@ don't do well in @simplify@! So we'll be passing the resulting AST of 'mh' to 'simplify' before plugging that into @mcmc@; that's why 'easierRoadmapProg4' and 'easierRoadmapProg4'' have different types.
-- TODO: the @a@ type should be pure (aka @a ~ Expect' a@ in the old parlance).
-- BUG: get rid of the SingI requirements due to using 'lam'
mh  :: (ABT AST abt, SingI a, Backward a a)
    => (abt '[] a -> abt '[] ('HMeasure a))
    -> abt '[] ('HMeasure a)
    -> abt '[] (a ':-> 'HMeasure (HPair a 'HProb))
mh prop target =
    let_ (determine $ density target) $ \mu ->
    lam $ \old ->
        prop old >>= \new ->
        dirac $ pair new (mu `app` new / mu `app` old)


sq :: (ABT AST abt, HSemiring_ a) => abt '[] a -> abt '[] a
sq x = x * x -- TODO: use 'square' instead


easierRoadmapProg4
    :: (ABT AST abt)
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
    :: (ABT AST abt)
    => abt '[]
        (    HPair 'HReal 'HReal
        ':-> HPair 'HProb 'HProb
        ':-> 'HMeasure (HPair (HPair 'HProb 'HProb) 'HProb))
easierRoadmapProg4' =
    lam $ \m1m2 ->
    mh proposal (easierRoadmapProg3'out m1m2)

easierRoadmapProg4'out
    :: (ABT AST abt)
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
    :: (ABT AST abt, SingI a)
    => abt '[] 'HNat
    -> abt '[] a
    -> abt '[] (a ':-> 'HMeasure a)
    -> abt '[] ('HMeasure ('HArray a))
makeChain n s0 m =
    fst <$>
        chain
            (array n $ \ _ ->
                lam $ \s' ->
                dup <$> m `app` s')
            s0
    where
    dup x = pair x x

runSample ::
    MWC.GenIO -> TrivialABT AST '[] ('HMeasure a)
    -> IO (Maybe (Sample IO a))
runSample g prog = do
  Just (s, _) <- unS (sample (LC_ prog) emptyEnv) 1 g
  return (Just s)

runEasierRoadmapProg4, runEasierRoadmapProg4'
    :: IO (Maybe (Sample IO ('HArray (HPair 'HProb 'HProb))))
runEasierRoadmapProg4 = do
    g <- MWC.create
    runSample g $
        makeChain (nat_ 20) (pair (prob_ 4) (prob_ 2))
            (easierRoadmapProg4 `app` pair (real_ 0) (real_ 1))

runEasierRoadmapProg4' = do
    g <- MWC.create
    runSample g $
        let_ (pair (real_ 0) (real_ 1)) $ \m1m2 ->
        let_
            ( simplify
            . determine
            . disintegrate
            $ easierRoadmapProg1
            ) $ \target ->
        let_ (mh proposal (target `app` m1m2)) $ \f ->
        makeChain (nat_ 20) (pair (prob_ 4) (prob_ 2)) $
            lam (\ntne -> fst <$> f `app` ntne)
            {-
            -- TODO:
            lam $ \ntne -> 
            (f `app` ntne) `unpair` \ntne' ratio ->
            bern (prob_ 1 `min` ratio) >>= \accept ->
            dirac $ if_ accept ntne' ntne
            -}
