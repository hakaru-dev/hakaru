{-# OPTIONS -Wall #-}
module Examples.HMM where

import Prelude hiding (Real)
import Language.Hakaru.Syntax
import Language.Hakaru.Expect (Expect(..))
import Language.Hakaru.Sample (Sample(..))
import System.Random.MWC (withSystemRandom)
import Control.Monad (replicateM)
import Data.Number.LogFloat (LogFloat)

-- Kleisli composition
-- bindo f g = \x -> do y <- f x
--                      z <- g y
--                      return z

bindo :: (Mochastic repr, Lambda repr) =>
         repr (a -> Measure b) ->
         repr (b -> Measure c) ->
         repr (a -> Measure c)
bindo f g = lam (\x -> app f x `bind` app g)

-- Conditional probability tables (ignore Expect and unExpect on first reading)

type Table = Vector (Vector Prob)

reflect :: (Mochastic repr, Lambda repr, Integrate repr) =>
           repr Table -> Expect repr (Int -> Measure Int)
reflect m = lam (\i -> let v = index (Expect m) i
                       in weight (summateV v) (categorical v))

reify :: (Mochastic repr, Lambda repr, Integrate repr) =>
         repr Int -> repr Int ->
         Expect repr (Int -> Measure Int) -> repr Table
reify domainSize rangeSize m =
  vector domainSize (\i ->
  vector rangeSize  (\j ->
  app (snd_ (app (unExpect m) i)) (lam (\j' -> if_ (equal j j') 1 0))))

--------------------------------------------------------------------------------

-- Model: A one-dimensional random walk among 20 discrete states (numbered
--        0 through 19 and arranged in a row) starting at state 10 at time 0.
-- Query: Given that the state is less than 8 at time 6,
--        what's the posterior distribution over states at time 12?

type Time  = Int
type State = Int

-- hmm is a model that disintegration might produce: it already incorporates
-- the observed data, hence "emission ... bind_ ... unit".

hmm :: (Mochastic repr, Lambda repr) => repr (Measure State)
hmm = liftM snd_ (app (chain (vector (12+1) $ \t ->
                              lam $ \s ->
                              emission t s `bind_`
                              transition s `bind` \s' ->
                              dirac (pair unit s')))
                      10)

emission :: (Mochastic repr) =>
            repr Time -> repr State -> repr (Measure ())
emission t s = if_ (equal t 6)
                   (if_ (less s 8) (dirac unit) (superpose []))
                   (dirac unit)

transition :: (Mochastic repr) => repr State -> repr (Measure State)
transition s = categorical (vector 20 (\s' ->
               if_ (and_ [less (s-2) s', less s' (s+2)]) 1 0))

-- Because our observed data has substantial probability (unlike in practice),
-- we can even sample blindly to answer the query approximately.

try :: IO [Maybe (Int, LogFloat)]
try = replicateM 100
    $ withSystemRandom
    $ unSample (hmm :: Sample IO (Measure State)) 1

-- Using the default implementation of "chain" in terms of "reduce",
-- and eliminating the "unit"s, we can simplify "hmm" to

hmm' :: (Mochastic repr, Lambda repr) => repr (Measure State)
hmm' = app (chain' (vector 13 $ \t ->
                    lam $ \s ->
                    emission t s `bind_`
                    transition s `bind` \s' ->
                    dirac s'))
           10

chain' :: (Mochastic repr, Lambda repr) =>
          repr (Vector (a -> Measure a)) -> repr (a -> Measure a)
chain' = reduce bindo (lam dirac)

-- in which the type of reduced elements is "State -> Measure State".
-- To compute this exactly in polynomial time, we just need to represent these
-- elements as tables instead.  That is, we observe that all our values of type
-- "State -> Measure State" have the form "reflect m", and
--          bindo (reflect m) (reflect n)  ==  reflect (bindo' m n)
-- in which bindo', defined below, runs in polynomial time given m and n.
-- So we can simplify "hmm'" to

hmm'' :: (Mochastic repr, Lambda repr, Integrate repr) =>
         Expect repr (Measure State)
hmm'' = app (reflect (chain'' (vector 13 $ \t ->
                               reify 20 20 $
                               lam $ \s ->
                               emission (Expect t) s `bind_`
                               transition s `bind` \s' ->
                               dirac s')))
            10

chain'' :: (Mochastic repr, Lambda repr, Integrate repr) =>
           repr (Vector Table) -> repr Table
chain'' = reduce bindo' (reify 20 20 (lam dirac))

bindo' :: (Mochastic repr, Lambda repr, Integrate repr) =>
          repr Table -> repr Table -> repr Table
bindo' m n = reify 20 20 (bindo (reflect m) (reflect n))

-- Of course bindo' can be optimized a lot further internally, but this is the
-- main idea.  We are effectively multiplying matrix*matrix*...*matrix*vector,
-- so it would also be better to associate these multiplications to the right.

--------------------------------------------------------------------------------

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
-- is something like "lam (\s -> weight (? * exp_ (? * (s - ?) ^ 2))
--                                      (normal (? * s + ?) ?))"
-- in which each ? is a real number.
