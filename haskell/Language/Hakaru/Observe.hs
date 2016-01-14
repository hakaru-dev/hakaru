{-# LANGUAGE DataKinds
           , GADTs
           , FlexibleContexts
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.12.15
-- |
-- Module      :  Language.Hakaru.Observe
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  ppaml@indiana.edu
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- A simpler version of the work done in 'Language.Hakaru.Disintegrate'
--
-- In principle, this module's functionality is entirely subsumed
-- by the work done in Language.Hakaru.Disintegrate, so we can hope
-- to define observe in terms of disintegrate. This is still useful
-- as a guide to those that want something more in line with what other
-- probabilisitc programming systems support.
----------------------------------------------------------------
module Language.Hakaru.Observe where

import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.HClasses
import qualified Language.Hakaru.Syntax.Prelude as P

observe
    :: (ABT Term abt, HEq_ a)
    => abt '[] ('HMeasure a)
    -> abt '[] a 
    -> abt '[] ('HMeasure HUnit)
observe m a = observeAST (LC_ m) (LC_ a)

observeAST
    :: (ABT Term abt, HEq_ a)
    => LC_ abt ('HMeasure a)
    -> LC_ abt a
    -> abt '[] ('HMeasure HUnit)
observeAST (LC_ m) (LC_ a) =
    caseVarSyn m observeVar $ \ast ->
        case ast of
        Dirac :$ (e :* End) -> P.if_ (e P.== a) (P.dirac P.unit) P.reject
        MeasureOp_ op :$ es -> observeMeasureOp op es a
        _ -> error "observe can only be applied to measure primitives"

observeVar = error "observe can only be applied measure primitives"

observeMeasureOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => MeasureOp typs a
    -> SArgs abt args
    -> abt '[] a
    -> abt '[] ('HMeasure HUnit)
observeMeasureOp Normal  (mu :* sd :* End) x =
    P.weight
        (P.exp (P.negate (x P.- mu) P.^ P.nat_ 2
        P./ P.fromProb (P.prob_ 2 P.* sd P.^ (P.nat_ 2)))
        P./ sd
        P./ P.sqrt (P.prob_ 2 P.* P.pi))
observeMeasureOp Uniform (lo :* hi :* End) x =
    P.if_ (lo P.<= x P.&& x P.<= hi)
          (P.weight $ P.unsafeProb $ P.recip $ hi P.- lo)
          P.reject
observeMeasureOp _ _ _ = error "Add other cases"
