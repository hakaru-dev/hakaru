{-# LANGUAGE NoImplicitPrelude, DataKinds #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Examples.HMM where

import Prelude ((.), id, ($))

import Language.Hakaru.Syntax.Prelude
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Syntax.AST   (Term)
import Language.Hakaru.Syntax.ABT   (ABT)


import Language.Hakaru.Expect (Expect(..))
import Language.Hakaru.Sample (Sample(..))

import System.Random.MWC (withSystemRandom)
import Control.Monad (replicateM)
import Data.Number.LogFloat (LogFloat)

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
    app (snd (app (unExpect m) i)) (lam $ \j' -> if_ (equal j j') 1 0)

--------------------------------------------------------------------------------

-- Model: A one-dimensional random walk among 20 discrete states (numbered
--        0 through 19 and arranged in a row) starting at state 10 at time 0.
-- Query: Given that the state is less than 8 at time 6,
--        what's the posterior distribution over states at time 12?

type Time  = Int
type State = Int

-- hmm is a model that disintegration might produce: it already incorporates
-- the observed data, hence "emission ... bind_ ... unit".

hmm :: (ABT Term abt) => abt '[] ('HMeasure State)
hmm = liftM snd_ (app (chain (array (12+1) $ \t ->
                              lam $ \s ->
                              emission t s `bind_`
                              transition s `bind` \s' ->
                              dirac (pair unit s')))
                      10)

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

-- Because our observed data has substantial probability (unlike in practice),
-- we can even sample blindly to answer the query approximately.

try :: IO [Maybe (Int, LogFloat)]
try = replicateM 100
    . withSystemRandom
    . unSample (hmm :: Sample IO (Measure State))
    $ 1

-- Using the default implementation of "chain" in terms of "reduce",
-- and eliminating the "unit"s, we can simplify "hmm" to

hmm' :: (ABT Term abt) => abt '[] (Measure State)
hmm' = app (chain' (array 13 $ \t ->
                    lam $ \s ->
                    emission t s >>
                    transition s >>= \s' ->
                    dirac s'))
           10

chain'
    :: (ABT Term abt)
    => abt '[] ('HArray (a ':-> 'HMeasure a))
    -> abt '[] (a ':-> 'HMeasure a)
chain' = reduce bindo (lam dirac)

-- in which the type of reduced elements is "State -> Measure State".
-- To compute this exactly in polynomial time, we just need to represent these
-- elements as tables instead.  That is, we observe that all our values of type
-- "State -> Measure State" have the form "reflect m", and
--          bindo (reflect m) (reflect n)  ==  reflect (bindo' m n)
-- in which bindo', defined below, runs in polynomial time given m and n.
-- So we can simplify "hmm'" to

hmm'' :: (ABT Term abt) => Expect (abt '[]) ('HMeasure State)
hmm'' = app (reflect (chain'' (array 13 $ \t ->
                               reify 20 20 $
                               lam $ \s ->
                               emission (Expect t) s `bind_`
                               transition s `bind` \s' ->
                               dirac s')))
            10

chain'' :: (ABT Term abt) => abt '[] ('HArray Table) -> abt '[] Table
chain'' = reduce bindo' (reify 20 20 (lam dirac))

bindo' :: (ABT Term abt) => abt '[] Table -> abt '[] Table -> abt '[] Table
bindo' m n = reify 20 20 (bindo (reflect m) (reflect n))

-- Of course bindo' can be optimized a lot further internally, but this is the
-- main idea.  We are effectively multiplying matrix*matrix*...*matrix*vector,
-- so it would also be better to associate these multiplications to the right.
