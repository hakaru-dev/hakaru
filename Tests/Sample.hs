module Tests.Sample (runPriorProg) where

import Prelude hiding (Real)
import Language.Hakaru.Syntax
import Language.Hakaru.Sample
import qualified System.Random.MWC as MWC
import qualified Data.Number.LogFloat as LF
import Tests.RoundTrip (testPriorProp)

runPriorProg :: IO (Maybe ((Double,Double), LF.LogFloat))
runPriorProg = do
   g <- MWC.create
   unSample (app testPriorProp (pair 1 1)) 1 g
