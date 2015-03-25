{-# OPTIONS -Wall #-}
-- Simplified copy of Example.HMM.  The whole point here is to go from the
-- straightforward definition to a "simpler" one, step-by-step, where we
-- justify each step fully.

module Examples.HMMDeriv where

import Prelude hiding (Real)
import Language.Hakaru.Syntax
import Language.Hakaru.Expect (Expect(..))

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

-- Comment on the above: the snd_ is an artifact of Expect, and can be mostly ignored

-- Transformation #1:
-- - inline weight, summateV in reflect
reflect' :: (Mochastic repr, Lambda repr, Integrate repr) =>
           repr Table -> Expect repr (Int -> Measure Int)
reflect' m = lam (\i -> let v = index (Expect m) i in
                        let s = summate 0 (fromInt (size v - 1)) (index v) in
                        superpose [(s,(categorical v))])

-- Transformation #2:
-- The above occurences of (lam, index, summate, size, index, superpose, categorical)
-- are all from the Expect interpretation.  Most of them are straight wrapper-unwrapper
-- pairs.  However, categorical and superpose are not.  Let's inline all of that.
-- However, for clarity, all the let_ bindings done there will not be applied here.
reflect'' :: (Mochastic repr, Lambda repr, Integrate repr) =>
           repr Table -> repr (Int -> (Measure Int, (Int -> Prob) -> Prob))
reflect'' m = 
  lam (\i ->
    let v = index m i in
    let s = summate 0 (fromInt (size v - 1)) (index v) in
    let cv = pair (categorical v)
             (lam (\c -> let_ (summate 0 (fromInt (size v - 1)) (index v)) $ \tot ->
                         if_ (less 0 tot)
                             (let vv = (mapWithIndex (\i' p -> p * app c i') v) in
                                   summate 0 (fromInt (size vv - 1)) (index vv) / tot)
                             0)) in
    let pms = [(s, cv)] in
    pair (superpose [ (p, fst_ m') | (p, m') <- pms ])
         (lam (\c -> sum [p * app (snd_ m') c | (p, m') <- pms])) )
    
-- before moving on, let's do a bit of partial evaluation on the above.
-- in particular, we can inline pms, so that the last 3 lines become
--    pair (superpose [ (s, fst_ cv) ])
--         (lam (\c -> s * app (snd_ cv) c )) )
-- where we "ran" the single-item list comprehension and single-term sum.

-- We now need that reify a b (reflect m) ~~ m
-- where "magically", a and b are just right for m.
-- In other words, we must have that
-- 1. a == size m - 1
-- 2. forall i. 0 <= i <= a => size (index m i) == b

-- This all translates to:
rr :: (Mochastic repr, Lambda repr, Integrate repr) =>
  repr Int -> repr Int -> repr Table -> repr Table
rr a b m = 
  vector a (\i ->
  vector b  (\j ->
    app (snd_ (app m' i)) (lam (\j' -> if_ (equal j j') 1 0)) ) )
  where
    m' = lam (\k ->
         let v = index m k in
         let s = summate 0 (fromInt (size v - 1)) (index v) in
         let cv = pair (categorical v)
                (lam (\c -> let_ (summate 0 (fromInt (size v - 1)) (index v)) $ \tot ->
                            if_ (less 0 tot)
                                (let vv = (mapWithIndex (\i' p -> p * app c i') v) in
                                      summate 0 (fromInt (size vv - 1)) (index vv) / tot)
                                0)) in
         pair (superpose [ (s, fst_ cv) ]) 
              (lam (\c -> s * app (snd_ cv) c )))
-- is in fact an identity function (for m).
-- Assumption #1: app (unExpect (lam (\k -> f))) i) ~~ f [ k <- Expect i ]
--    note that i :: repr Int, k :: Expect repr Int
-- Assumption #2: unExpect is just an unWrap [something Haskell guarantees]

{-
-- so we can inline and get something which does not typecheck, namely:
-- rr' a b m = 
--   vector a (\i ->
--   vector b  (\j ->
--   app (let v = index (Expect m) (Expect i) in
--        let s = summate 0 (fromInt (size v - 1)) (index v) in
--        (superpose [(s, categorical v)])) (lam (\j' -> if_ (equal j j') 1 0))))
--
-- The problem is that the above wants the superpose to be of type
--  repr0 ((Int -> b0) -> a0)
-- but it is in fact
--  repr0 (Measure Int)
-- So this exposes the deep details of Expect, namely that
-- Expect' (Measure q) = (Measure (Expect' q), (Expect' q -> Prob) -> Prob)

-- This means that snd_ (Expect m) 'acts like' a function, and the app above
-- feeds an argument to it.  So
-- let v = index (Expect m) (Expect i) in
-- acts like
-- let v = index (m (lam (\j' -> if_ (equal j j') 1 0))) (Expect i)
-- Assumption #4: app (index (Expect m) (Expect i)) c ~~ index m (app c i)
--
-- HOWEVER, m is not the only measure expression in the above!  So are
-- superpose and categorical.  So they also need to be 'fed' a "c".
--
-- Assumption #5: app (lam (\k -> b)) i ~~ b i
--
-- which now gives
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

-}
--------------------------------------------------------------------------------

{-

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

bindo'' :: (Simplifiable a, Simplifiable b, Simplifiable c) =>
           Expect Maple (a -> Measure b) ->
           Expect Maple (b -> Measure c) ->
           IO (Expect Maple (a -> Measure c))
bindo'' m n = do 
   p <- simplify (bindo m n)
   return (unAny p)
-}
