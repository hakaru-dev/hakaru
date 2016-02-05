{-# LANGUAGE DataKinds, NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.12.16
-- |
-- Module      :  Tests.Models
-- Copyright   :  Copyright (c) 2015 the Hakaru team
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

import Language.Hakaru.Types.DataKind
import Language.Hakaru.Syntax.AST (Term)
import Language.Hakaru.Syntax.ABT (ABT)
import Language.Hakaru.Syntax.Prelude

import Data.Text

----------------------------------------------------------------
----------------------------------------------------------------
uniform_0_1 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
uniform_0_1 = uniform zero one

normal_0_1 :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
normal_0_1 = normal zero one

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
    superpose
        [ (x'                  , dirac (pair x' true))
        , (unsafeProb (one - x), dirac (pair x' false))
        ]

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
    , "true:  normal(0,1)"
    , "false: uniform(0,1)"
    , "return ((y,x) :: pair(real, bool))"
    ]

match_norm_bool :: Test
match_norm_bool = unlines
    [ "x <~ normal(3,2)"
    , "return (match x < 0:"
    , "          true:  (-x, ())"
    , "          false: ( x, ()))"
    ]

----------------------------------------------------------------
----------------------------------------------------------- fin.
