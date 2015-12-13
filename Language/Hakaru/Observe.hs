{-# LANGUAGE DataKinds
           , GADTs
           , FlexibleContexts
           #-}

module Language.Hakaru.Observe where

import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.HClasses
import qualified Language.Hakaru.Syntax.Prelude as P
import qualified Language.Hakaru.Expect         as E

observe :: (ABT Term abt, HEq_ a)
        => abt '[] ('HMeasure a)
        -> abt '[] a 
        -> abt '[] ('HMeasure HUnit)
observe m a = observeAST (LC_ m) (LC_ a)

observeAST :: (ABT Term abt, HEq_ a)
           => LC_ abt ('HMeasure a)
           -> LC_ abt a
           -> abt '[] ('HMeasure HUnit)
observeAST (LC_ m) (LC_ a) =
    caseVarSyn m observeVar $ \ast ->
        case ast of
          Dirac :$ (e :* End) -> P.if_ (e P.== a) (P.dirac P.unit) P.reject
          MeasureOp_ op :$ es -> observeMeasureOp op es a
          _ -> error "observe can only be applied to measure primitive"

observeVar = error "observe can only be applied measure primitive"

observeMeasureOp :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
                 => MeasureOp typs a
                 -> SArgs abt args
                 -> abt '[] a
                 -> abt '[] ('HMeasure HUnit)
observeMeasureOp Normal  (mu :* sd :* End) x =
    P.weight
            (P.exp (P.negate (x P.- mu) P.^ P.nat_ 2
                P./ P.fromProb (P.prob_ 2 P.* sd P.** (P.real_ 2)))
            P./ sd
            P./ P.sqrt (P.prob_ 2 P.* P.pi))
observeMeasureOp Uniform (lo :* hi :* End) x =
    P.if_ (lo P.<= x P.&& x P.<= hi)
          (P.weight $ P.unsafeProb $ P.recip $ hi P.- lo)
          P.reject

observeMeasureOp _      _                 _ = error "Add other cases"
