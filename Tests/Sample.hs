{-# LANGUAGE  NoMonomorphismRestriction #-}
module Tests.Sample (runPriorProg) where

import Prelude hiding (Real)
import Language.Hakaru.Syntax
import Language.Hakaru.Sample
import qualified System.Random.MWC as MWC
import qualified Data.Number.LogFloat as LF

testPriorProp' :: (Integrate repr, Mochastic repr, Lambda repr) =>
                 repr ((Real, Real) -> Measure ((Real, Real), Prob))
testPriorProp' =
      (lam $ \old ->
       superpose [(fromRational (1/2),
                   normal 0 1 `bind` \x1 ->
                   dirac (pair (pair x1 (snd_ old))
                               (exp_ ((x1 * (-1) + fst_ old)
                                      * (fst_ old + snd_ old * (-2) + x1)
                                      * fromRational (1 / 2))))),
                  (fromRational (1/2),
                   normal 0 (sqrt_ 2) `bind` \x1 ->
                   dirac (pair (pair (fst_ old) x1)
                               (exp_ ((x1 * (-1) + snd_ old)
                                      * (snd_ old * (-1) + fst_ old * 4 + x1 * (-1))
                                      * fromRational (-1/4)))))])

runPriorProg :: IO (Maybe (((Double,Double), LF.LogFloat), LF.LogFloat))
runPriorProg = do
   g <- MWC.create
   unSample (app testPriorProp' (pair 1 1)) 1 g
