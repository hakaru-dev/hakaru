{-# LANGUAGE DataKinds
           , GADTs
           , FlexibleContexts
           #-}

module Language.Hakaru.Observe where

import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.DataKind
import qualified Language.Hakaru.Syntax.Prelude as P
import qualified Language.Hakaru.Expect         as E

observe :: (ABT AST abt)
        => abt '[] ('HMeasure a)
        -> abt '[] a 
        -> abt '[] ('HMeasure HUnit)
observe m a = observeAST (LC_ m) (LC_ a)

observeAST :: (ABT AST abt)
           => LC_ abt ('HMeasure a)
           -> LC_ abt a
           -> abt '[] ('HMeasure HUnit)
observeAST (LC_ m) (LC_ a) =
    caseVarSyn m observeVar $ \ast ->
        case ast of
          MeasureOp_ op :$ es -> observeMeasureOp op es a
          _ -> error "observe can only be applied to measure primitive"

observeVar = error "observe can only be applied measure primitive"

observeMeasureOp :: (ABT AST abt, typs ~ UnLCs args, args ~ LCs typs)
                 => MeasureOp typs a
                 -> SArgs abt args
                 -> abt '[] a
                 -> abt '[] ('HMeasure HUnit)
observeMeasureOp Normal (mu :* sd :* End) x =
    P.weight
            (P.exp (P.negate (x P.- mu) P.^ P.nat_ 2
                P./ P.fromProb (P.prob_ 2 P.* sd P.** (P.real_ 2)))
            P./ sd
            P./ P.sqrt (P.prob_ 2 P.* P.pi))
observeMeasureOp _      _                 _ = error "Add other cases"
