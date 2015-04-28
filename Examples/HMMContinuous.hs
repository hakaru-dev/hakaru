{-# OPTIONS -Wall #-}
module Examples.HMMContinuous where

import Prelude hiding (Real)
import Language.Hakaru.Syntax
import Language.Hakaru.Simplify
import Language.Hakaru.Any
import Language.Hakaru.Maple

--------------------------------------------------------------------------------

type Time  = Int

-- Model: A one-dimensional random walk among real numbers (but time still
--        elapses in discrete steps) starting at state 10 at time 0.
-- Query: Given that the state is observed noisily to be 8 at time 6,
--        what's the posterior distribution over states at time 12?

hmmContinuous :: (Mochastic repr, Lambda repr) => repr (Measure Real)
hmmContinuous = liftM snd_ (app (chain (vector (12+1) $ \t ->
                                        lam $ \s ->
                                        emissionContinuous t s `bind_`
                                        transitionContinuous s `bind` \s' ->
                                        dirac (pair unit s')))
                                10)

emissionContinuous :: (Mochastic repr) =>
                      repr Time -> repr Real -> repr (Measure ())
emissionContinuous t s = if_ (equal t 6)
                             (factor (exp_ (- (s - 8) ^ (2 :: Int))))
                             (dirac unit)

transitionContinuous :: (Mochastic repr) => repr Real -> repr (Measure Real)
transitionContinuous s = normal s 1

-- To compute hmmContinuous efficiently, again we should specialize "bindo" to
-- values of type "Real -> Measure Real" that are of a certain form.  The form
-- is something like "lam (\s -> weight (? * exp_ (? * (s - ?) ** 2))
--                                      (normal (? * s + ?) ?))"
-- in which each ? is a real number.

type M = (Prob, (Real, (Real, (Real, (Real, Prob)))))

reflect :: (Mochastic repr, Lambda repr) =>
           repr M -> repr (Real -> Measure Real)
reflect m =
  unpair m $ \a m ->
  unpair m $ \b m ->
  unpair m $ \c m ->
  unpair m $ \d m ->
  unpair m $ \e f ->
  lam $ \s ->
  weight (a * exp_ (b * (s - c) ** 2)) $
  normal (d * s + e) f

-- Unfortunately Maple currently refuses to write bindo'' for us:
--  > simplify (lam $ \m -> lam $ \n -> reflect m `bindo` reflect n)
--  *** Exception: MapleException:
--  Error, (in SLO:-AST) non-zero constant (infinity) encountered as a measure
