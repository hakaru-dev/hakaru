{-# LANGUAGE NoImplicitPrelude, DataKinds #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Examples.HMMContinuous where

import Prelude ((.), id, ($))

import Language.Hakaru.Syntax.Prelude
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Syntax.AST   (Term)
import Language.Hakaru.Syntax.ABT   (ABT)

import Language.Hakaru.Simplify
import Language.Hakaru.Any
import Language.Hakaru.Maple

--------------------------------------------------------------------------------

type Time  = Int

-- Model: A one-dimensional random walk among real numbers (but time still
--        elapses in discrete steps) starting at state 10 at time 0.
-- Query: Given that the state is observed noisily to be 8 at time 6,
--        what's the posterior distribution over states at time 12?

hmmContinuous :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
hmmContinuous =
    snd `liftM` app (chain (vector (12+1) $ \t ->
        lam $ \s ->
        emissionContinuous t s >>
        transitionContinuous s >>= \s' ->
        dirac (pair unit s')))
    10

emissionContinuous
    :: (ABT Term abt)
    => abt '[] Time
    -> abt '[] 'HReal
    -> abt '[] ('HMeasure HUnit)
emissionContinuous t s =
    if_ (t == 6)
        (factor (exp_ (- (s - 8) ^ (2 :: Int))))
        (dirac unit)

transitionContinuous
    :: (ABT Term abt) => abt '[] 'HReal -> abt '[] ('HMeasure 'HReal)
transitionContinuous s = normal s one

-- To compute hmmContinuous efficiently, again we should specialize "bindo" to
-- values of type "Real -> Measure Real" that are of a certain form.  The form
-- is something like "lam (\s -> weight (? * exp_ (? * (s - ?) ** 2))
--                                      (normal (? * s + ?) ?))"
-- in which each ? is a real number.

type M = HPair 'HProb (HPair 'HProb (HPair 'HReal (HPair 'HReal (HPair 'HReal 'HProb))))

reflect
    :: (ABT Term abt) => abt '[] M -> abt '[] ('HReal ':-> 'HMeasure 'HReal)
reflect m =
    m `unpair` \a m ->
    m `unpair` \b m ->
    m `unpair` \c m ->
    m `unpair` \d m ->
    m `unpair` \e f ->
    lam $ \s ->
    weight (a * exp (negate (fromProb b) * (s - c) ** 2)) $
    normal (d * s + e) f

-- We can use "simplify" to help with writing bindo':
--  > simplify (lam $ \m -> lam $ \n -> reflect m `bindo` reflect n)
-- The output is the following, after collecting "unpair"s:
--  lam $ \m ->
--  lam $ \n ->
--  lam $ \s ->
--  unpair m $ \ma m ->
--  unpair m $ \mb m ->
--  unpair m $ \mc m ->
--  unpair m $ \md m ->
--  unpair m $ \me mf ->
--  unpair n $ \na n ->
--  unpair n $ \nb n ->
--  unpair n $ \nc n ->
--  unpair n $ \nd n ->
--  unpair n $ \ne nf ->
--  weight (ma * na
--          * recip (sqrt_ (mf * mf * nb * 2 + 1))
--          * unsafeProb (exp ((s ** 2 * fromProb (mb * (mf * mf) * nb * 2)
--                              + s * mc * fromProb (mb * (mf * mf) * nb) * (-4)
--                              + mc ** 2 * fromProb (mb * (mf * mf) * nb * 2)
--                              + s ** 2 * md ** 2 * fromProb nb
--                              + s * md * me * fromProb (nb * 2)
--                              + s * md * nc * fromProb nb * (-2)
--                              + s ** 2 * fromProb mb
--                              + s * mc * fromProb mb * (-2)
--                              + mc ** 2 * fromProb mb
--                              + me ** 2 * fromProb nb
--                              + me * nc * fromProb nb * (-2)
--                              + nc ** 2 * fromProb nb)
--                             * (fromProb (mf * mf * nb * 2) + 1) ** (-1)
--                             * (-1)))) $
--  normal ((nd * nc * fromProb (mf * mf * nb) * (-2)
--           + ne * fromProb (mf * mf * nb) * (-2)
--           + nd * s * md * (-1)
--           + nd * me * (-1)
--           + ne * (-1))
--          * recip (fromProb (mf * mf * nb * 2) + 1)
--          * (-1))
--         (sqrt_ (recip (mf * mf * nb * 2 + 1)
--                 * unsafeProb (fromProb (nf * nf * (mf * mf) * nb * 2)
--                               + nd ** 2 * fromProb (mf * mf)
--                               + fromProb nf ** 2)))
