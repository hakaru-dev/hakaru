{-# LANGUAGE DataKinds, NoImplicitPrelude, NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Tests.Sample (runPriorProg) where

import Prelude ((.), id, ($), asTypeOf)
import Language.Hakaru.Syntax.Prelude
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Syntax.AST (Term)
import Language.Hakaru.Syntax.ABT (ABT)
import Language.Hakaru.Sample

import qualified System.Random.MWC as MWC
import qualified Data.Number.LogFloat as LF

half :: (ABT Term abt, HFractional_ a) => abt '[] a
half = one / (one + one)

testPriorProp'
    :: (ABT Term abt)
    => abt '[] (HPair 'HReal 'HReal
        ':-> 'HMeasure (HPair (HPair 'HReal 'HReal) 'HProb))
testPriorProp' =
    lam $ \old ->
    superpose
        [ (half,
            normal zero one >>= \x1 ->
            dirac (pair (pair x1 (snd old))
                (exp
                    ( (fst old - x1)
                    * (fst old - 2 * snd old + x1)
                    * half))))
        , (half,
            normal zero (sqrt (prob_ 2)) >>= \x1 ->
            dirac (pair (pair (fst old) x1)
                (exp
                    ( (snd old - x1)
                    * (4 * fst old - x1 - snd old)
                    * real_ (-1/4)))))
        ]

runPriorProg :: IO (Maybe (((Double,Double), LF.LogFloat), LF.LogFloat))
runPriorProg = do
    g <- MWC.create
    unSample (testPriorProp' `app` pair one one) 1 g
