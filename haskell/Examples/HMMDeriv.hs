{-# LANGUAGE NoImplicitPrelude, DataKinds, TypeFamilies #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
-- Simplified copy of Example.HMM.  The whole point here is to go from the
-- straightforward definition to a "simpler" one, step-by-step, where we
-- justify each step fully.
module Examples.HMMDeriv where

import Prelude ((.), id, ($))

import Language.Hakaru.Syntax.Prelude
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Syntax.AST   (Term)
import Language.Hakaru.Syntax.ABT   (ABT)

import Language.Hakaru.Expect (Expect(..),Expect')

-- Conditional probability tables (ignore Expect and unExpect on first reading)

type Table = 'HArray ('HArray 'HProb)

reflect
    :: (ABT Term abt)
    => abt '[] Table
    -> Expect (abt '[]) ('HInt ':-> 'HMeasure 'HInt)
reflect m =
    lam $ \i ->
    let v = index (Expect m) i in
    weight (summateV v) (categorical v)

reify
    :: (ABT Term abt)
    => abt '[] 'HInt
    -> abt '[] 'HInt
    -> Expect (abt '[]) ('HInt ':-> 'HMeasure 'HInt)
    -> abt '[] Table
reify domainSize rangeSize m =
    array domainSize $ \i ->
    array rangeSize  $ \j ->
    snd (unExpect m `app` i) `app` (lam $ \j' -> if_ (j == j') one zero)

-- Comment on the above: the snd is an artifact of Expect, and can be mostly ignored

-- Transformation #1:
-- - inline weight, summateV in reflect
reflect'
    :: (ABT Term abt)
    => abt '[] Table
    -> Expect (abt '[]) ('HInt ':-> 'HMeasure 'HInt)
reflect' m =
    lam $ \i ->
    let v = index (Expect m) i in
    let s = summate zero (fromInt (size v - one)) (index v) in
    superpose [(s,(categorical v))])

-- Transformation #2:
-- The above occurences of (lam, index, summate, size, index, superpose, categorical)
-- are all from the Expect interpretation.  Most of them are straight wrapper-unwrapper
-- pairs.  However, categorical and superpose are not.  Let's inline all of that.
-- However, for clarity, all the let_ bindings done there will not be applied here.
reflect''
    :: (ABT Term abt)
    => abt '[] Table
    -> abt '[]
        ('HInt ':-> HPair ('HMeasure Int) (('HInt ':-> 'HProb) ':-> 'HProb))
reflect'' m = 
    lam $ \i ->
    let v = index m i in
    let s = summate zero (fromInt (size v - one)) (index v) in
    let cv = pair (categorical v)
             (lam $ \c ->
             let_ (summate zero (fromInt (size v - one)) (index v)) $ \tot ->
             if_ (zero < tot)
                (let vv = mapWithIndex (\i' p -> p * app c i') v in
                summate zero (fromInt (size vv - one)) (index vv) / tot)
                zero) in
    let pms = [(s, cv)] in
    pair (superpose [ (p, fst m') | (p, m') <- pms ])
         (lam $ \c -> sum [p * app (snd m') c | (p, m') <- pms])
    
-- before moving on, let's do a bit of partial evaluation on the above.
-- in particular, we can inline pms, so that the last 3 lines become
--    pair (superpose [ (s, fst cv) ])
--         (lam (\c -> s * app (snd cv) c )) )
-- where we "ran" the single-item list comprehension and single-term sum.

-- We now need to verify that reify a b (reflect m) ~~ m
-- where "magically", a and b are just right for m.
-- In other words, we must have that
-- 1. a == size m - 1
-- 2. forall i. 0 <= i <= a => size (index m i) == b

-- This all translates to:
rr, rr1, rr2, rr3, rr4, rr5, rr6, rr7, rr8, rr9, rr10, rr11
    :: (ABT Term abt)
    => abt '[] 'HInt
    -> abt '[] 'HInt
    -> abt '[] Table
    -> abt '[] Table
rr a b m = 
    array a $ \i ->
    array b $ \j ->
    snd (m' `app` i) `app` (lam $ \j' -> if_ (j == j') one zero)
    where
    m' =
        lam $ \k ->
        let v = index m k in
        let s = summate zero (fromInt (size v - one)) (index v) in
        let cv = pair (categorical v)
                (lam $ \c ->
                let_ (summate zero (fromInt (size v - one)) (index v)) $ \tot ->
                if_ (zero < tot)
                    (let vv = (mapWithIndex (\i' p -> p * app c i') v) in
                    summate zero (fromInt (size vv - one)) (index vv) / tot)
                    zero) in
        pair (superpose [ (s, fst cv) ]) 
              (lam $ \c -> s * app (snd cv) c)
-- is in fact an identity function (for m).

-- Assumption #1: app (lam f) x ~~ f x
-- Assumption #2: snd (pair a b) ~~ b
-- [and may as well] fst (pair a b) ~~ a
--
-- Perform these as rewrites with lam f = m', x = i, to get
rr1 a b m = 
    array a $ \i ->
    array b $ \j ->
    let v = index m i in
    let s = summate zero (fromInt (size v - one)) (index v) in
    let cv = pair (categorical v)
            (lam $ \c ->
            let_ (summate zero (fromInt (size v - one)) (index v)) $ \tot ->
            if_ (zero < tot)
                (let vv = (mapWithIndex (\i' p -> p * app c i') v) in
                summate zero (fromInt (size vv - one)) (index vv) / tot)
            zero) in
    app (lam $ \c -> s * app (snd cv) c)
        (lam $ \j' -> if_ (j == j') one zero)

-- Now do the app@lam on the last line.  Also simplify the "snd cv", but keep the let
rr2 a b m = 
    array a $ \i ->
    array b $ \j ->
    let v = index m i in
    let s = summate zero (fromInt (size v - one)) (index v) in
    let cc = lam $ \c ->
            let_ (summate zero (fromInt (size v - one)) (index v)) $ \tot ->
            if_ (zero < tot)
                (let vv = (mapWithIndex (\i' p -> p * app c i') v) in
                summate zero (fromInt (size vv - one)) (index vv) / tot)
                zero in
    s * app cc (lam $ \j' -> if_ (j == j') one zero)

-- now inline the "app cc" part, but let bind the body for less messyness
rr3 a b m = 
    array a $ \i ->
    array b $ \j ->
    let v = index m i in
    let s = summate zero (fromInt (size v - one)) (index v) in
    let charf = lam $ \j' -> if_ (j == j') one zero in
    let rest =
            let_ (summate zero (fromInt (size v - one)) (index v)) $ \tot ->
            if_ (zero < tot)
                (let vv = (mapWithIndex (\i' p -> p * app charf i') v) in
                summate zero (fromInt (size vv - one)) (index vv) / tot)
                zero in
    s * rest

-- inline mapWithIndex; beta-reduce result
rr4 a b m = 
    array a $ \i ->
    array b $ \j ->
    let v = index m i in
    let s = summate zero (fromInt (size v - one)) (index v) in
    let charf = lam $ \j' -> if_ (j == j') one zero in
    let rest =
            let_ (summate zero (fromInt (size v - one)) (index v)) $ \tot ->
            if_ (zero < tot)
                (let vv = array (size v) (\k -> index v k * app charf k) in
                summate zero (fromInt (size vv - one)) (index vv) / tot)
                zero in
    s * rest

-- inline "app charf k"; 
-- Assumption #3: x * if_ cond a b ~~ if_ cond (a * x) (b * x)
-- Assumption #4: 0 * x ~~ 0
-- Assumption #5: 1 * x ~~ x
rr5 a b m = 
    array a $ \i ->
    array b $ \j ->
    let v = index m i in
    let s = summate zero (fromInt (size v - one)) (index v) in
    let rest =
            let_ (summate zero (fromInt (size v - one)) (index v)) $ \tot ->
            if_ (zero < tot)
                (let vv = array (size v) $\k -> if_ (j == k) (index v k) zero in
                summate zero (fromInt (size vv - one)) (index vv) / tot)
                zero in
    s * rest

-- Note how vv is only defined at j = k.  
-- Assumption #6: summate transforms an array into the sum of its non-zero parts
rr6 a b m = 
    array a $ \i ->
    array b $ \j ->
    let v = index m i in
    let s = summate zero (fromInt (size v - one)) (index v) in
    let rest =
            let_ (summate zero (fromInt (size v - one)) (index v)) $ \tot ->
            if_ (zero < tot)
                (index v j / tot)
                zero in
    s * rest

-- Note how s and tot are in fact the same.
-- Assumption #7: let_ x f ~~ f x

rr7 a b m = 
    array a $ \i ->
    array b $ \j ->
    let v = index m i in
    let s = summate zero (fromInt (size v - one)) (index v) in
    let rest = if_ (zero < s) (index v j / s) zero in
    s * rest

-- Assumption #8: size v - 1 == a
-- inline "let rest" and push multiplication in
rr8 a b m = 
    array a $ \i ->
    array b $ \j ->
    let v = index m i in
    let s = summate zero (fromInt (size v - one)) (index v) in
    if_ (zero < s) (s * index v j / s) zero

-- Assumption #9: x * y / x ~~ y if x <> 0
rr9 a b m = 
    array a $ \i ->
    array b $ \j ->
    let v = index m i in
    let s = summate zero (fromInt (size v - one)) (index v) in
    if_ (zero < s) (index v j) zero

-- Assumption #10: Prob >= 0.  Which has for corrollary
-- Cor: s == 0 iff forall 0 <= j <= size v -1. index v j ==0.
-- Thus, in fact, if_ (zero < s) (index v j) zero == index v j regardless.

rr10 a b m = 
    array a $ \i ->
    array b $ \j ->
    let v = index m i in
    index v j

-- Assumption #11: array a (\i -> array b (\j -> index (index m i) j)) == m
-- (also known as tabulate-lookup in Agda)
rr11 _ _ m =  m

--------------------------------------------------------------------------------
--
-- Suggestion for alternate model for reify/reflect

type LinearOperator a = (a ':-> 'HProb) ':-> 'HProb

reflectOp
    :: (ABT Term abt)
    => abt '[] Table
    -> abt '[] ('HInt ':-> LinearOperator 'HInt)
reflectOp m = 
    lam $ \i ->
    let v = index m i in
    lam $ \c ->
    summateV (array (size v) (\k -> index v k * app c i)
    
reifyOp
    :: (ABT Term abt)
    => abt '[] 'HInt
    -> abt '[] 'HInt
    -> abt '[] ('HInt ':-> LinearOperator 'HInt)
    -> abt '[] Table
reifyOp domainSize rangeSize m =
    array domainSize $ \i ->
    array rangeSize  $ \j ->
    m `app` i `app` (lam $ \j' -> if_ (j == j') one zero)

bindOp
    :: (ABT Term abt)
    => abt '[] (a ':-> LinearOperator b)
    -> abt '[] (b ':-> LinearOperator c)
    -> abt '[] (a ':-> LinearOperator c)
bindOp f g =
    lam $ \a ->
    lam $ \c -> 
    f `app` a `app` (lam $ \b -> g `app` b `app` c)

bindOp' :: (ABT Term abt) => abt '[] Table -> abt '[] Table -> abt '[] Table
bindOp' m n = reifyOp 20 20 (bindOp (reflectOp m) (reflectOp n))

fromM
    :: (ABT Term abt, a ~ Expect' a)
    => Expect (abt '[]) ('HMeasure a)
    -> abt '[] (LinearOperator a)
fromM m = snd (unExpect m)

--------------------------------------------------------------------------------

-- Model: A one-dimensional random walk among 20 discrete states (numbered
--        0 through 19 and arranged in a row) starting at state 10 at time 0.
-- Query: Given that the state is less than 8 at time 6,
--        what's the posterior distribution over states at time 12?

type Time  = 'HInt
type State = 'HInt

-- hmm is a model that disintegration might produce: it already incorporates
-- the observed data, hence "emission ... bind_ ... unit".

hmm, hmm1, hmm2, hmm3, hmm'
    :: (ABT Term abt) => abt '[] ('HMeasure State)
hmm = snd `liftM` app (chain (array (12+one) $ \t ->
        lam $ \s ->
        emission t s >>
        transition s >>= \s' ->
        dirac (pair unit s')))
    10

emission
    :: (ABT Term abt)
    => abt '[] Time -> abt '[] State -> abt '[] ('HMeasure HUnit)
emission t s =
    if_ (t == 6)
        (if_ (s < 8) (dirac unit) (superpose []))
        (dirac unit)

transition :: (ABT Term abt) => abt '[] State -> abt '[] ('HMeasure State)
transition s =
    categorical . array (nat_ 20) $ \s' ->
        if_ (s-2 < s' && s' < s+2) one zero

-- Transformation #1: Inline the definition of "chain" in terms of "reduce"
-- from Language.Hakaru.Syntax into hmm.  Note that the type "s" is "State"
-- and the type "a" is "()".
hmm1 = snd `liftM` app (reduce r z $
                        mapV m $
                        array (12+one) $ \t ->
                        lam $ \s ->
                        emission t s >>
                        transition s >>= \s' ->
                        dirac (pair unit s'))
                      10
    where
    r x y = lam $ \s ->
        app x s >>= \v1s1 ->
        v1s1 `unpair` \v1 s1 ->
        app y s1 >>= \v2s2 ->
        v2s2 `unpair` \v2 s2 ->
        dirac (pair (concatV v1 v2) s2)
    z     = lam $ \s -> dirac (pair empty s)
    m a   = lam $ \s -> liftM (`unpair` pair . array one . const) (app a s)

-- Transformation #2: Expand "mapV m $ ..." above using the
-- definitions of "mapV" and "liftM", the monad laws, and the
-- assumptions
--  app (lam f) x ~~ f x
--  size (array n f) ~~ n
--  index (array n f) i ~~ f i
--  unpair (pair x y) f ~~ f x y
hmm2 = snd `liftM` app (reduce r z $
                        array (12+one) $ \t ->
                        lam $ \s ->
                        emission t s >>
                        transition s >>= \s' ->
                        dirac (pair (array one (const unit)) s'))
                      10
    where
    r x y = lam $ \s ->
        app x s >>= \v1s1 ->
        v1s1 `unpair` \v1 s1 ->
        app y s1 >>= \v2s2 ->
        v2s2 `unpair` \v2 s2 ->
        dirac (pair (concatV v1 v2) s2)
    z     = lam $ \s -> dirac (pair empty s)

-- Transformation #3: note that every value above of type
--  ('HArray (), State)
-- has the form
--  (pair (array n (const unit)) s)
-- for some n and s.  (In particular, we can show
--  concatV (array n1 (const unit)) (array n2 (const unit))
--  ~~ array (n1+n2) (const unit)
-- from the definition of "concatV".)  And we never use the n, so
-- let's represent (pair (array n (const unit)) s) by simply "s".

hmm3 = app (reduce r z $
            array (12+one) $ \t ->
            lam $ \s ->
            emission t s >>
            transition s >>= \s' ->
            dirac s')
          10
    where
    r x y = lam $ \s ->
        app x s >>= \s1 ->
        app y s1 >>= \s2 ->
        dirac s2
    z     = lam dirac

-- Transformation #4: By the monad laws and eta-reduction, "r" above
-- is exactly "bindo", and "z" is exactly "lam dirac".  So hmm ~~ hmm'

-- Using the default implementation of "chain" in terms of "reduce",
-- and eliminating the "unit"s, we can simplify "hmm" to

hmm' = app (chain' (array 13 $ \t ->
        lam $ \s ->
        emission t s >>
        transition s >>= \s' ->
        dirac s'))
    10

chain'
    :: (ABT Term abt)
    => abt '[] ('HArray (a -> Measure a)) -> abt '[] (a -> Measure a)
chain' = reduce bindo (lam dirac)

{-
-- in which the type of reduced elements is "State -> Measure State".
-- To compute this exactly in polynomial time, we just need to represent these
-- elements as tables instead.  That is, we observe that all our values of type
-- "State -> Measure State" have the form "reflect m", and
--          bindo (reflect m) (reflect n)  ==  reflect (bindo' m n)
-- in which bindo', defined below, runs in polynomial time given m and n.
-- So we can simplify "hmm'" to

hmm'' :: (ABT Term abt) => Expect repr (Measure State)
hmm'' = app (reflect (chain'' (array 13 $ \t ->
                               reify 20 20 $
                               lam $ \s ->
                               emission (Expect t) s >>
                               transition s >>= \s' ->
                               dirac s')))
            10

chain'' :: (ABT Term abt) => abt '[] ('HArray Table) -> repr Table
chain'' = reduce bindo' (reify 20 20 (lam dirac))

bindo' :: (ABT Term abt) => abt '[] Table -> repr Table -> repr Table
bindo' m n = reify 20 20 (bindo (reflect m) (reflect n))

-- Of course bindo' can be optimized a lot further internally, but this is the
-- main idea.  We are effectively multiplying matrix*matrix*...*matrix*vector,
-- so it would also be better to associate these multiplications to the right.

-}
