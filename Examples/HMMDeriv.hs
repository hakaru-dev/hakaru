{-# OPTIONS -Wall #-}
{-# LANGUAGE TypeFamilies #-} -- just for a single type constraint!
-- Simplified copy of Example.HMM.  The whole point here is to go from the
-- straightforward definition to a "simpler" one, step-by-step, where we
-- justify each step fully.

module Examples.HMMDeriv where

import Prelude hiding (Real)
import Language.Hakaru.Syntax
import Language.Hakaru.Expect (Expect(..),Expect')

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

-- We now need to verify that reify a b (reflect m) ~~ m
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

-- Assumption #1: app (lam f) x ~~ f x
-- Assumption #2: snd_ (pair a b) ~~ b
-- [and may as well] fst_ (pair a b) ~~ a
--
-- Perform these as rewrites with lam f = m', x = i, to get

rr1 :: (Mochastic repr, Lambda repr, Integrate repr) =>
  repr Int -> repr Int -> repr Table -> repr Table
rr1 a b m = 
  vector a (\i ->
  vector b  (\j ->
    let v = index m i in
    let s = summate 0 (fromInt (size v - 1)) (index v) in
    let cv = pair (categorical v)
           (lam (\c -> let_ (summate 0 (fromInt (size v - 1)) (index v)) $ \tot ->
                       if_ (less 0 tot)
                           (let vv = (mapWithIndex (\i' p -> p * app c i') v) in
                                 summate 0 (fromInt (size vv - 1)) (index vv) / tot)
                           0)) in
    app (lam (\c -> s * app (snd_ cv) c)) (lam (\j' -> if_ (equal j j') 1 0)) ) )

-- Now do the app@lam on the last line.  Also simplify the "snd_ cv", but keep the let

rr2 :: (Mochastic repr, Lambda repr, Integrate repr) =>
  repr Int -> repr Int -> repr Table -> repr Table
rr2 a b m = 
  vector a (\i ->
  vector b  (\j ->
    let v = index m i in
    let s = summate 0 (fromInt (size v - 1)) (index v) in
    let cc = (lam (\c -> let_ (summate 0 (fromInt (size v - 1)) (index v)) $ \tot ->
                         if_ (less 0 tot)
                             (let vv = (mapWithIndex (\i' p -> p * app c i') v) in
                                   summate 0 (fromInt (size vv - 1)) (index vv) / tot)
                             0)) in
    s * app cc (lam (\j' -> if_ (equal j j') 1 0)) ) )

-- now inline the "app cc" part, but let bind the body for less messyness
rr3 :: (Mochastic repr, Lambda repr, Integrate repr) =>
  repr Int -> repr Int -> repr Table -> repr Table
rr3 a b m = 
  vector a (\i ->
  vector b  (\j ->
    let v = index m i in
    let s = summate 0 (fromInt (size v - 1)) (index v) in
    let charf = lam (\j' -> if_ (equal j j') 1 0) in
    let rest = let_ (summate 0 (fromInt (size v - 1)) (index v)) $ \tot ->
                   if_ (less 0 tot)
                       (let vv = (mapWithIndex (\i' p -> p * app charf i') v) in
                             summate 0 (fromInt (size vv - 1)) (index vv) / tot)
                       0 in
    s * rest ) )

-- inline mapWithIndex; beta-reduce result
rr4 :: (Mochastic repr, Lambda repr, Integrate repr) =>
  repr Int -> repr Int -> repr Table -> repr Table
rr4 a b m = 
  vector a (\i ->
  vector b  (\j ->
    let v = index m i in
    let s = summate 0 (fromInt (size v - 1)) (index v) in
    let charf = lam (\j' -> if_ (equal j j') 1 0) in
    let rest = let_ (summate 0 (fromInt (size v - 1)) (index v)) $ \tot ->
                   if_ (less 0 tot)
                       (let vv = vector (size v) (\k -> (index v k) * (app charf k)) in
                             summate 0 (fromInt (size vv - 1)) (index vv) / tot)
                       0 in
    s * rest ) )

-- inline "app charf k"; 
-- Assumption #3: x * if_ cond a b ~~ if_ cond (a * x) (b * x)
-- Assumption #4: 0 * x ~~ 0
-- Assumption #5: 1 * x ~~ x

rr5 :: (Mochastic repr, Lambda repr, Integrate repr) =>
  repr Int -> repr Int -> repr Table -> repr Table
rr5 a b m = 
  vector a (\i ->
  vector b  (\j ->
    let v = index m i in
    let s = summate 0 (fromInt (size v - 1)) (index v) in
    let rest = let_ (summate 0 (fromInt (size v - 1)) (index v)) $ \tot ->
                   if_ (less 0 tot)
                       (let vv = vector (size v) (\k -> (if_ (equal j k) (index v k) 0)) in
                             summate 0 (fromInt (size vv - 1)) (index vv) / tot)
                       0 in
    s * rest ) )

-- Note how vv is only defined at j = k.  
-- Assumption #6: summate transforms a vector into the sum of its non-zero parts

rr6 :: (Mochastic repr, Lambda repr, Integrate repr) =>
  repr Int -> repr Int -> repr Table -> repr Table
rr6 a b m = 
  vector a (\i ->
  vector b  (\j ->
    let v = index m i in
    let s = summate 0 (fromInt (size v - 1)) (index v) in
    let rest = let_ (summate 0 (fromInt (size v - 1)) (index v)) $ \tot ->
                   if_ (less 0 tot)
                       (index v j / tot)
                       0 in
    s * rest ) )

-- Note how s and tot are in fact the same.
-- Assumption #7: let_ x f ~~ f x

rr7 :: (Mochastic repr, Lambda repr, Integrate repr) =>
  repr Int -> repr Int -> repr Table -> repr Table
rr7 a b m = 
  vector a (\i ->
  vector b  (\j ->
    let v = index m i in
    let s = summate 0 (fromInt (size v - 1)) (index v) in
    let rest = if_ (less 0 s) (index v j / s) 0 in
    s * rest ) )

-- Assumption #8: size v - 1 == a
-- inline "let rest" and push multiplication in
rr8 :: (Mochastic repr, Lambda repr, Integrate repr) =>
  repr Int -> repr Int -> repr Table -> repr Table
rr8 a b m = 
  vector a (\i ->
  vector b  (\j ->
    let v = index m i in
    let s = summate 0 (fromInt (size v - 1)) (index v) in
    if_ (less 0 s) (s * index v j / s) 0 ) )

-- Assumption #9: x * y / x ~~ y if x <> 0
rr9 :: (Mochastic repr, Lambda repr, Integrate repr) =>
  repr Int -> repr Int -> repr Table -> repr Table
rr9 a b m = 
  vector a (\i ->
  vector b  (\j ->
    let v = index m i in
    let s = summate 0 (fromInt (size v - 1)) (index v) in
    if_ (less 0 s) (index v j) 0 ) )

-- Assumption #10: Prob >= 0.  Which has for corrollary
-- Cor: s == 0 iff forall 0 <= j <= size v -1. index v j ==0.
-- Thus, in fact, if_ (less 0 s) (index v j) 0 == index v j regardless.

rr10 :: (Mochastic repr, Lambda repr, Integrate repr) =>
  repr Int -> repr Int -> repr Table -> repr Table
rr10 a b m = 
  vector a (\i ->
  vector b  (\j ->
    let v = index m i in
    index v j ) )

-- Assumption #11: vector a (\i -> vector b (\j -> index (index m i) j)) == m
-- (also known as tabulate-lookup in Agda)
rr11 :: (Mochastic repr, Lambda repr, Integrate repr) =>
  repr Int -> repr Int -> repr Table -> repr Table
rr11 _ _ m =  m

--------------------------------------------------------------------------------
--
-- Suggestion for alternate model for reify/reflect

type LinearOperator a = (a -> Prob) -> Prob

reflectOp :: (Mochastic repr, Lambda repr, Integrate repr) =>
           repr Table -> repr (Int -> LinearOperator Int)
reflectOp m = 
  lam (\i -> let v = index m i in
    lam (\c -> summateV (vector (size v) (\k -> (index v k) * (app c i)))))
    
reifyOp :: (Mochastic repr, Lambda repr, Integrate repr) =>
         repr Int -> repr Int ->
         repr (Int -> LinearOperator Int) -> repr Table
reifyOp domainSize rangeSize m =
  vector domainSize (\i ->
  vector rangeSize  (\j ->
  app (app m i) (lam (\j' -> if_ (equal j j') 1 0))))

bindOp :: (Lambda repr) => repr (a -> LinearOperator b) ->
  repr (b -> LinearOperator c) -> repr (a -> LinearOperator c)
bindOp f g = lam (\a -> lam (\c -> 
  (app (app f a) (lam (\b -> app (app g b) c)))))

bindOp' :: (Mochastic repr, Lambda repr, Integrate repr) =>
  repr Table -> repr Table -> repr Table
bindOp' m n = reifyOp 20 20 (bindOp (reflectOp m) (reflectOp n))

fromM :: (a ~ Expect' a, Mochastic repr) => Expect repr (Measure a) -> repr (LinearOperator a)
fromM m = snd_ (unExpect m)

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

-- Transformation #1: Inline the definition of "chain" in terms of "reduce"
-- from Language.Hakaru.Syntax into hmm.  Note that the type "s" is "State"
-- and the type "a" is "()".

hmm1 :: (Mochastic repr, Lambda repr) => repr (Measure State)
hmm1 = liftM snd_ (app (reduce r z $
                        mapV m $
                        vector (12+1) $ \t ->
                        lam $ \s ->
                        emission t s `bind_`
                        transition s `bind` \s' ->
                        dirac (pair unit s'))
                      10)
    where r x y = lam (\s -> app x s `bind` \v1s1 ->
                             unpair v1s1 $ \v1 s1 ->
                             app y s1 `bind` \v2s2 ->
                             unpair v2s2 $ \v2 s2 ->
                             dirac (pair (concatV v1 v2) s2))
          z     = lam (\s -> dirac (pair empty s))
          m a   = lam (\s -> liftM (`unpair` pair . vector 1 . const)
                                   (app a s))

-- Transformation #2: Expand "mapV m $ ..." above using the
-- definitions of "mapV" and "liftM", the monad laws, and the
-- assumptions
--  app (lam f) x ~~ f x
--  size (vector n f) ~~ n
--  index (vector n f) i ~~ f i
--  unpair (pair x y) f ~~ f x y

hmm2 :: (Mochastic repr, Lambda repr) => repr (Measure State)
hmm2 = liftM snd_ (app (reduce r z $
                        vector (12+1) $ \t ->
                        lam $ \s ->
                        emission t s `bind_`
                        transition s `bind` \s' ->
                        dirac (pair (vector 1 (const unit)) s'))
                      10)
    where r x y = lam (\s -> app x s `bind` \v1s1 ->
                             unpair v1s1 $ \v1 s1 ->
                             app y s1 `bind` \v2s2 ->
                             unpair v2s2 $ \v2 s2 ->
                             dirac (pair (concatV v1 v2) s2))
          z     = lam (\s -> dirac (pair empty s))

-- Transformation #3: note that every value above of type
--  (Vector (), State)
-- has the form
--  (pair (vector n (const unit)) s)
-- for some n and s.  (In particular, we can show
--  concatV (vector n1 (const unit)) (vector n2 (const unit))
--  ~~ vector (n1+n2) (const unit)
-- from the definition of "concatV".)  And we never use the n, so
-- let's represent (pair (vector n (const unit)) s) by simply "s".

hmm3 :: (Mochastic repr, Lambda repr) => repr (Measure State)
hmm3 = app (reduce r z $
            vector (12+1) $ \t ->
            lam $ \s ->
            emission t s `bind_`
            transition s `bind` \s' ->
            dirac s')
          10
    where r x y = lam (\s -> app x s `bind` \s1 ->
                             app y s1 `bind` \s2 ->
                             dirac s2)
          z     = lam (\s -> dirac s)

-- Transformation #4: By the monad laws and eta-reduction, "r" above
-- is exactly "bindo", and "z" is exactly "lam dirac".  So hmm ~~ hmm'

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

{-
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
