{-# LANGUAGE RankNTypes, TypeFamilies #-}

module Examples.EasierRoadmap where

import Prelude hiding (Real)
import Language.Hakaru.Syntax
import Language.Hakaru.Lazy (Backward, runDisintegrate, density)
import Language.Hakaru.Expect (Expect')
import Language.Hakaru.Simplify (simplify)
import Language.Hakaru.Any (Any)

easierRoadmapProg1 ::
  (Mochastic repr) =>
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

easierRoadmapProg2 ::
  (Mochastic repr) =>
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

easierRoadmapProg2', easierRoadmapProg2'out ::
  (Mochastic repr, Lambda repr) =>
  repr ((Real, Real) -> Measure (Prob, Prob))
easierRoadmapProg2' = d `app` unit
  where [d] = runDisintegrate (\_ -> easierRoadmapProg1)
easierRoadmapProg2'out =
    (lam $ \x0 ->
     lam $ \x1 ->
     x1 `unpair` \x2 x3 ->
     weight 1 $
     weight 1 $
     superpose [(1,
                 weight 1 $
                 lebesgue `bind` \x4 ->
                 superpose [(1,
                             weight 1 $
                             lebesgue `bind` \x5 ->
                             weight 1 $
                             lebesgue `bind` \x6 ->
                             weight (exp_ (-(x3 - x6) * (x3 - x6)
                                            * recip (fromProb (2 * exp_ (log_ (unsafeProb x5) * 2))))
                                     * recip (unsafeProb x5)
                                     * recip (exp_ (log_ (2 * pi_) * (1/2)))) $
                             weight 1 $
                             lebesgue `bind` \x7 ->
                             weight (exp_ (-(x6 - x7) * (x6 - x7)
                                            * recip (fromProb (2 * exp_ (log_ (unsafeProb x4) * 2))))
                                     * recip (unsafeProb x4)
                                     * recip (exp_ (log_ (2 * pi_) * (1/2)))) $
                             weight (exp_ (-(x2 - x7) * (x2 - x7)
                                            * recip (fromProb (2 * exp_ (log_ (unsafeProb x5) * 2))))
                                     * recip (unsafeProb x5)
                                     * recip (exp_ (log_ (2 * pi_) * (1/2)))) $
                             weight (exp_ (-x7 * x7
                                            * recip (fromProb (2 * exp_ (log_ (unsafeProb x4) * 2))))
                                     * recip (unsafeProb x4)
                                     * recip (exp_ (log_ (2 * pi_) * (1/2)))) $
                             weight (recip (unsafeProb 3)) $
                             superpose [(1,
                                         if_ (x5 `less` 4)
                                             (if_ (1 `less` x5)
                                                  (weight (recip (unsafeProb 5)) $
                                                   superpose [(1,
                                                               if_ (x4 `less` 8)
                                                                   (if_ (3 `less` x4)
                                                                        (dirac (pair (unsafeProb x4)
                                                                                     (unsafeProb x5)))
                                                                        (superpose []))
                                                                   (superpose [])),
                                                              (1, superpose [])])
                                                  (superpose []))
                                             (superpose [])),
                                        (1, superpose [])]),
                            (1, superpose [])]),
                (1, superpose [])])
    `app` unit

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

easierRoadmapProg3' :: IO (Any ((Real, Real) -> Measure (Prob, Prob)))
easierRoadmapProg3' = simplify easierRoadmapProg2'

easierRoadmapProg3'out ::
  (Mochastic repr) =>
  repr (Real, Real) -> repr (Measure (Prob, Prob))
easierRoadmapProg3'out x0 =
    weight 5 $
    uniform 3 8 `bind` \x1 ->
    uniform 1 4 `bind` \x2 ->
    weight (recip pi_
	    * exp_ (((fst_ x0) * (fst_ x0) * (x1 * x1) * 2
		     + x1 * x1 * (fst_ x0) * (snd_ x0) * (-2)
		     + (snd_ x0) * (snd_ x0) * (x1 * x1)
		     + x2 * x2 * ((fst_ x0) * (fst_ x0))
		     + x2 * x2 * ((snd_ x0) * (snd_ x0)))
		    * recip (x1 * x1 * (x1 * x1) + x2 * x2 * (x1 * x1) * 3 + x2 * x2 * (x2 * x2))
		    * (-1/2))
	    * pow_ (unsafeProb (x1 ** 4 + x2 ** 2 * x1 ** 2 * 3 + x2 ** 4)) (-1/2)
	    * (1/10)) $
    dirac (pair (unsafeProb x1) (unsafeProb x2))

proposal ::
  (Mochastic repr) =>
  repr (Real, Real) -> repr (Prob, Prob) -> repr (Measure (Prob, Prob))
proposal _m1m2 ntne =
  unpair ntne $ \noiseTOld noiseEOld ->
  superpose [(1/2, uniform 3 8 `bind` \noiseT' ->
                   dirac (pair (unsafeProb noiseT') noiseEOld)),
             (1/2, uniform 1 4 `bind` \noiseE' ->
                   dirac (pair noiseTOld (unsafeProb noiseE')))]

mh :: (Mochastic repr, Integrate repr, Lambda repr,
       env ~ Expect' env, a ~ Expect' a, Backward a a) =>
      (forall repr'. (Mochastic repr') => repr' env -> repr' a -> repr' (Measure a)) ->
      (forall repr'. (Mochastic repr') => repr' env -> repr' (Measure a)) ->
      repr (env -> a -> Measure (a, Prob))
mh proposal target =
  lam $ \env ->
  let_ (lam (d env)) $ \mu ->
  lam $ \old ->
    proposal env old `bind` \new ->
    dirac (pair new (mu `app` {-pair-} new {-old-} / mu `app` {-pair-} old {-new-}))
  where d:_ = density (\env -> {-bindx-} (target env) {-(proposal env)-})

easierRoadmapProg4 ::
  (Lambda repr, Mochastic repr) =>
  repr ((Real, Real) -> (Prob, Prob) -> Measure (Prob, Prob))
easierRoadmapProg4 = 
  lam2 $ \m1m2 ntne ->
  unpair m1m2 $ \m1 m2 ->
  unpair ntne $ \noiseTOld noiseEOld ->
  bern (1/2) `bind` \b ->
  bind (if_ b
        (uniform 3 8 `bind` \noiseT' ->
         let_ (unsafeProb noiseT') $ \noiseT ->
         dirac $ pair noiseT noiseEOld)
        (uniform 1 4 `bind` \noiseE' ->
         let_ (unsafeProb noiseE') $ \noiseE ->
         dirac $ pair noiseTOld noiseE)) (\ntne' ->
  (bern $ min_ 1 (easyDens m1 m2 ntne' / easyDens m1 m2 ntne)) `bind` \accept ->
  dirac $ if_ accept ntne' ntne)
 where easyDens m1 m2 ntne = unpair ntne $ \nt' ne' ->
                       let_ (fromProb nt') (\nt ->
                       let_ (fromProb ne') (\ne ->
                       recip pi_
	               * exp_ ((m1 * m1 * (nt * nt) * 2
		                + nt * nt * m1 * m2 * (-2)
		                + m2 * m2 * (nt * nt)
		                + ne * ne * (m1 * m1)
		                + ne * ne * (m2 * m2))
		               * recip (nt * nt * (nt * nt)
                                        + ne * ne * (nt * nt) * 3
                                        + ne * ne * (ne * ne))
		               * (-1/2))
	               * pow_ (unsafeProb (nt ** 4 + ne ** 2 * nt ** 2 * 3 + ne ** 4)) (-1/2)
	               * (1/10)))

easierRoadmapProg4' ::
  (Mochastic repr, Integrate repr, Lambda repr) =>
  repr ((Real, Real) -> (Prob, Prob) -> Measure ((Prob, Prob), Prob))
easierRoadmapProg4' = mh proposal easierRoadmapProg3'out
