module Examples.EasierRoadmap where

import Prelude hiding (Real)
import Language.Hakaru.Syntax

easierRoadmapProg1 :: (Mochastic repr) =>
                      repr (Measure ((Real, Real), (Prob, Prob)))
easierRoadmapProg1 =
  uniform 3 8 `bind` \noiseT' -> -- let_ (unsafeProb noiseT') $ \noiseT ->
  uniform 1 4 `bind` \noiseE' -> -- let_ (unsafeProb noiseE') $ \noiseE ->
  dirac (unsafeProb noiseT') `bind` \noiseT ->
  dirac (unsafeProb noiseE') `bind` \noiseE ->
  normal  0 noiseT `bind` \x1 ->
  normal x1 noiseE `bind` \m1 ->
  normal x1 noiseT `bind` \x2 ->
  normal x2 noiseE `bind` \m2 ->
  dirac (pair (pair m1 m2) (pair noiseT noiseE))

easierRoadmapProg2 :: (Mochastic repr) =>
                      repr (Real, Real) -> repr (Measure (Prob, Prob))
easierRoadmapProg2 = \m1m2 -> 
  -- lam $ \m1m2 ->
  unpair m1m2 $ \m1 m2 ->
  uniform 3 8 `bind` \noiseT' -> -- let_ (unsafeProb noiseT') $ \noiseT ->
  uniform 1 4 `bind` \noiseE' -> -- let_ (unsafeProb noiseE') $ \noiseE ->
  dirac (unsafeProb noiseT') `bind` \noiseT ->
  dirac (unsafeProb noiseE') `bind` \noiseE ->
  normal  0 noiseT `bind` \x1 ->
  weight (undefined x1 noiseE m1) $ -- TODO by disintegration
  normal x1 noiseT `bind` \x2 ->
  weight (undefined x2 noiseE m2) $ -- TODO by disintegration
  dirac (pair noiseT noiseE)

easierRoadmapProg3 ::
  (Lambda repr, Mochastic repr) =>
  repr ((Real, Real) -> Measure (Prob, Prob))
easierRoadmapProg3 =
  lam $ \m1m2 ->
  unpair m1m2 $ \m1 m2 ->
  uniform 3 8 `bind` \noiseT' -> let_ (unsafeProb noiseT') $ \noiseT ->
  uniform 1 4 `bind` \noiseE' -> let_ (unsafeProb noiseE') $ \noiseE ->
  weight (undefined noiseT noiseE m1 m2) $ -- TODO by simplification
  dirac (pair noiseT noiseE)

easierRoadmapProg4 ::
  (Lambda repr, Mochastic repr) =>
  repr ((Real, Real) -> (Prob, Prob) -> Measure (Prob, Prob))
easierRoadmapProg4 = 
  lam2 $ \m1m2 ntne ->
  unpair m1m2 $ \m1 m2 ->
  unpair ntne $ \nt ne ->
  bern (1/2) `bind` \b ->
  bind (if_ b
        (uniform 3 8 `bind` \nt' -> dirac (pair (unsafeProb nt') ne))
        (uniform 1 4 `bind` \ne' -> dirac (pair nt (unsafeProb ne')))) (\ntne' ->
  (bern $ min_ 1 (easyDens ntne' / easyDens ntne)) `bind` \accept ->
  dirac $ if_ accept ntne' ntne)
 where easyDens = undefined
