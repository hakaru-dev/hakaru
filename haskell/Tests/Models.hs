{-# LANGUAGE DataKinds
           , NoImplicitPrelude
           , OverloadedStrings
           , FlexibleContexts #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.04.22
-- |
-- Module      :  Tests.Models
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Some common models used in many different tests.
--
-- TODO: we might should adjust our use of 'pair' to include a type
-- annotation, to avoid issues about 'Language.Hakaru.Syntax.TypeOf.typeOf'
-- on 'Datum'.
----------------------------------------------------------------
module Tests.Models where

import Data.Text
import qualified Data.List.NonEmpty as L

import Language.Hakaru.Types.DataKind
import Language.Hakaru.Syntax.AST (Term)
import Language.Hakaru.Syntax.ABT (ABT)
import Language.Hakaru.Syntax.Prelude


----------------------------------------------------------------
----------------------------------------------------------------
uniform_0_1 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
uniform_0_1 = uniform zero one

-- build uniform with nats and coercions
uniformC :: (ABT Term abt)
         => abt '[] 'HNat
         -> abt '[] 'HNat
         -> abt '[] ('HMeasure 'HReal)
uniformC lo hi = uniform (nat2real lo) (nat2real hi)

normal_0_1 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
normal_0_1 = normal zero one

-- build normal with nats and coercions
normalC  :: (ABT Term abt)
         => abt '[] 'HNat
         -> abt '[] 'HNat
         -> abt '[] ('HMeasure 'HReal)
normalC mu sd = normal (nat2real mu) (nat2prob sd)

gamma_1_1 :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
gamma_1_1 = gamma one one

beta_1_1 :: (ABT Term abt) => abt '[] ('HMeasure 'HProb)
beta_1_1 = beta one one


-- TODO: a better name for this
t4 :: (ABT Term abt) => abt '[] ('HMeasure (HPair 'HProb HBool))
t4 =
    beta one one >>= \bias ->
    bern bias >>= \coin ->
    dirac (pair bias coin)

t4' :: (ABT Term abt) => abt '[] ('HMeasure (HPair 'HProb HBool))
t4' =
    uniform zero one >>= \x ->
    let x' = unsafeProb x in
    superpose (L.fromList
        [ (x'                  , dirac (pair x' true))
        , (unsafeProb (one - x), dirac (pair x' false))
        ])

norm :: (ABT Term abt) => abt '[] ('HMeasure (HPair 'HReal 'HReal))
norm =
    normal zero one >>= \x ->
    normal x one >>= \y ->
    dirac (pair x y)

unif2 :: (ABT Term abt) => abt '[] ('HMeasure (HPair 'HReal 'HReal))
unif2 =
    uniform (negate one) one >>= \x ->
    uniform (x - one) (x + one) >>= \y ->
    dirac (pair x y)

match_norm_unif :: Text
match_norm_unif = unlines
    [ "x <~ bern(0.5)"
    , "y <~ match x:"
    , "       true:  normal(0,1)"
    , "       false: uniform(0,1)"
    , "return ((y,x). pair(real, bool))"
    ]

match_norm_bool :: Text
match_norm_bool = unlines
    [ "x <~ normal(3,2)"
    , "return (match x < 0:"
    , "          true:  (-x, ())"
    , "          false: ( x, ()))"
    ]

easyRoad :: Text
easyRoad = unlines
    ["noiseT_ <~ uniform(3, 8)"
    ,"noiseE_ <~ uniform(1, 4)"
    ,"noiseT = unsafeProb(noiseT_)"
    ,"noiseE = unsafeProb(noiseE_)"
    ,"x1 <~ normal(0,  noiseT)"
    ,"m1 <~ normal(x1, noiseE)"
    ,"x2 <~ normal(x1, noiseT)"
    ,"m2 <~ normal(x2, noiseE)"
    ,"return ((m1, m2), (noiseT, noiseE))"
    ]

plate_norm :: Text
plate_norm = unlines
    [ "x <~ normal(0,1)"
    , "y <~ plate _ of 5:"
    , "       normal(x,1)"
    , "return (y, x)"
    ]

negate_prob :: Text
negate_prob = "unsafeProb(1.0 + negate(2.0))"

----------------------------------------------------------------
----------------------------------------------------------- fin.
