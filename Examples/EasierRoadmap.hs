{-# LANGUAGE RankNTypes, TypeFamilies, DataKinds #-}

module Examples.EasierRoadmap where

import Prelude hiding (Real)
import Language.Hakaru.Syntax
import Language.Hakaru.Lazy (Backward, runDisintegrate, density)
import Language.Hakaru.Expect (Expect')
import Language.Hakaru.Simplify (simplify)
import Language.Hakaru.Any (Any)

import Language.Hakaru.Sample

easierRoadmapProg1
    :: (Mochastic repr)
    => repr (HMeasure (HPair (HPair HReal HReal) (HPair HProb HProb)))
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

easierRoadmapProg2
    :: (Mochastic repr)
    => repr (HPair HReal HReal)
    -> repr (HMeasure (HPair HProb HProb))
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

easierRoadmapProg2', easierRoadmapProg2'out
    :: (Mochastic repr, Lambda repr)
    => repr (HFun (HPair HReal HReal) (HMeasure (HPair HProb HProb)))
easierRoadmapProg2' = d `app` unit
  where [d] = runDisintegrate (\_ -> easierRoadmapProg1)
easierRoadmapProg2'out =
    (lam $ \_ ->
     lam $ \m1m2 ->
     m1m2 `unpair` \m1 m2 ->
     weight 1 $
     weight 1 $
     superpose [(1,
                 weight 1 $
                 lebesgue `bind` \noiseT' ->
                 superpose [(1,
                             weight 1 $
                             lebesgue `bind` \noiseE' ->
                             weight 1 $
                             lebesgue `bind` \x2 ->
                             weight (exp_ (-(m2 - x2) * (m2 - x2)
                                            * recip (fromProb (2 * exp_ (log_ (unsafeProb noiseE') * 2))))
                                     * recip (unsafeProb noiseE')
                                     * recip (exp_ (log_ (2 * pi_) * (1/2)))) $
                             weight 1 $
                             lebesgue `bind` \x1 ->
                             weight (exp_ (-(x2 - x1) * (x2 - x1)
                                            * recip (fromProb (2 * exp_ (log_ (unsafeProb noiseT') * 2))))
                                     * recip (unsafeProb noiseT')
                                     * recip (exp_ (log_ (2 * pi_) * (1/2)))) $
                             weight (exp_ (-(m1 - x1) * (m1 - x1)
                                            * recip (fromProb (2 * exp_ (log_ (unsafeProb noiseE') * 2))))
                                     * recip (unsafeProb noiseE')
                                     * recip (exp_ (log_ (2 * pi_) * (1/2)))) $
                             weight (exp_ (-x1 * x1
                                            * recip (fromProb (2 * exp_ (log_ (unsafeProb noiseT') * 2))))
                                     * recip (unsafeProb noiseT')
                                     * recip (exp_ (log_ (2 * pi_) * (1/2)))) $
                             weight (recip (unsafeProb 3)) $
                             superpose [(1,
                                         if_ (noiseE' `less` 4)
                                             (if_ (1 `less` noiseE')
                                                  (weight (recip (unsafeProb 5)) $
                                                   superpose [(1,
                                                               if_ (noiseT' `less` 8)
                                                                   (if_ (3 `less` noiseT')
                                                                        (dirac (pair (unsafeProb noiseT')
                                                                                     (unsafeProb noiseE')))
                                                                        (superpose []))
                                                                   (superpose [])),
                                                              (1, superpose [])])
                                                  (superpose []))
                                             (superpose [])),
                                        (1, superpose [])]),
                            (1, superpose [])]),
                (1, superpose [])])
    `app` unit

easierRoadmapProg3
    :: (Lambda repr, Mochastic repr)
    => repr (HFun (HPair HReal HReal) (HMeasure (HPair HProb HProb)))
easierRoadmapProg3 =
  lam $ \m1m2 ->
  unpair m1m2 $ \m1 m2 ->
  uniform 3 8 `bind` \noiseT' -> let_ (unsafeProb noiseT') $ \noiseT ->
  uniform 1 4 `bind` \noiseE' -> let_ (unsafeProb noiseE') $ \noiseE ->
  weight (undefined noiseT noiseE m1 m2) $ -- TODO by simplification
  dirac (pair noiseT noiseE)

easierRoadmapProg3'
    :: IO (Any (HFun (HPair HReal HReal) (HMeasure (HPair HProb HProb))))
easierRoadmapProg3' = simplify easierRoadmapProg2'

easierRoadmapProg3'out
    :: (Mochastic repr)
    => repr (HPair HReal HReal)
    -> repr (HMeasure (HPair HProb HProb))
easierRoadmapProg3'out m1m2 =
    weight 5 $
    uniform 3 8 `bind` \noiseT' ->
    uniform 1 4 `bind` \noiseE' ->
    weight (recip pi_
	    * exp_ (((fst_ m1m2) * (fst_ m1m2) * (noiseT' * noiseT') * 2
		     + noiseT' * noiseT' * (fst_ m1m2) * (snd_ m1m2) * (-2)
		     + (snd_ m1m2) * (snd_ m1m2) * (noiseT' * noiseT')
		     + noiseE' * noiseE' * ((fst_ m1m2) * (fst_ m1m2))
		     + noiseE' * noiseE' * ((snd_ m1m2) * (snd_ m1m2)))
		    * recip (noiseT' * noiseT' * (noiseT' * noiseT') + noiseE' * noiseE' * (noiseT' * noiseT') * 3 + noiseE' * noiseE' * (noiseE' * noiseE'))
		    * (-1/2))
	    * pow_ (unsafeProb (noiseT' ** 4 + noiseE' ** 2 * noiseT' ** 2 * 3 + noiseE' ** 4)) (-1/2)
	    * (1/10)) $
    dirac (pair (unsafeProb noiseT') (unsafeProb noiseE'))

proposal
    :: (Mochastic repr)
    => repr (HPair HReal HReal)
    -> repr (HPair HProb HProb)
    -> repr (HMeasure (HPair HProb HProb))
proposal _m1m2 ntne =
  unpair ntne $ \noiseTOld noiseEOld ->
  superpose [(1/2, uniform 3 8 `bind` \noiseT' ->
                   dirac (pair (unsafeProb noiseT') noiseEOld)),
             (1/2, uniform 1 4 `bind` \noiseE' ->
                   dirac (pair noiseTOld (unsafeProb noiseE')))]

mh  :: (Mochastic repr, Integrate repr, Lambda repr,
        env ~ Expect' env, a ~ Expect' a, Backward a a)
    => (forall r'. (Mochastic r') => r' env -> r' a -> r' (HMeasure a))
    -> (forall r'. (Mochastic r') => r' env -> r' (HMeasure a))
    -> repr (HFun env (HFun a (HMeasure (HPair a HProb))))
mh prop target =
  lam $ \env ->
  let_ (lam (d env)) $ \mu ->
  lam $ \old ->
    prop env old `bind` \new ->
    dirac (pair new (mu `app` {-pair-} new {-old-} / mu `app` {-pair-} old {-new-}))
  where d:_ = density (\env -> {-bindx-} (target env) {-(prop env)-})

easierRoadmapProg4
    :: (Lambda repr, Mochastic repr)
    => repr (HFun (HPair HReal HReal)
            (HFun (HPair HProb HProb)
                (HMeasure (HPair HProb HProb))))
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
 where easyDens m1 m2 ntne = unpair ntne $ \nt ne ->
                       let_ (fromProb nt) (\nt' ->
                       let_ (fromProb ne) (\ne' ->
                       recip pi_
	               * exp_ ((m1 * m1 * (nt' * nt') * 2
		                + nt' * nt' * m1 * m2 * (-2)
		                + m2 * m2 * (nt' * nt')
		                + ne' * ne' * (m1 * m1)
		                + ne' * ne' * (m2 * m2))
		               * recip (nt' * nt' * (nt' * nt')
                                        + ne' * ne' * (nt' * nt') * 3
                                        + ne' * ne' * (ne' * ne'))
		               * (-1/2))
	               * pow_ (unsafeProb (nt' ** 4 + ne' ** 2 * nt' ** 2 * 3 + ne' ** 4)) (-1/2)
	               * (1/10)))

easierRoadmapProg4'
    :: (Mochastic repr, Integrate repr, Lambda repr)
    => repr (HFun (HPair HReal HReal)
            (HFun (HPair HProb HProb)
                (HMeasure (HPair (HPair HProb HProb) HProb))))
easierRoadmapProg4' = mh proposal easierRoadmapProg3'out

easierRoadmapProg4'out
    :: (Mochastic repr, Lambda repr)
    => repr (HFun (HPair HReal HReal)
            (HFun (HPair HProb HProb)
                (HMeasure (HPair (HPair HProb HProb) HProb))))
easierRoadmapProg4'out =
  lam $ \m1m2 ->
  lam $ \ntne ->
  unpair m1m2 $ \m1 m2 ->
  unpair ntne $ \noiseTOld noiseEOld ->
  let noiseTOld' = fromProb noiseTOld
      noiseEOld' = fromProb noiseEOld in
  superpose [(1/2,
              uniform 1 4 `bind` \noiseE' ->
              dirac (pair (pair noiseTOld (unsafeProb noiseE'))
                          (sqrt_ (noiseTOld * noiseTOld * (noiseTOld * noiseTOld)
                                  + noiseEOld * noiseEOld * (noiseTOld * noiseTOld) * 3
                                  + noiseEOld * noiseEOld * (noiseEOld * noiseEOld))
                           * if_ (if_ (noiseTOld `less` 3) true (noiseTOld `equal` 3))
                                 0
                                 (if_ (noiseTOld `less` 8) 1 0)
                           * exp_ ((noiseE' * noiseE' * (m1 * m1)
                                    + noiseE' * noiseE' * (m2 * m2)
                                    + m1 * m1 * fromProb (noiseTOld * noiseTOld * 2)
                                    + m1 * m2 * fromProb (noiseTOld * noiseTOld) * (-2)
                                    + m2 * m2 * fromProb (noiseTOld * noiseTOld))
                                   * recip (noiseE' * noiseE' * (noiseE' * noiseE')
                                            + noiseE' * noiseE' * fromProb (noiseTOld * noiseTOld * 3)
                                            + noiseTOld' * noiseTOld' * (noiseTOld' * noiseTOld'))
                                   * (-1/2))
                           * recip (sqrt_ (unsafeProb (noiseE' ** 4
                                                       + noiseE' ** 2 * fromProb (noiseTOld * noiseTOld * 3)
                                                       + noiseTOld' ** 4)))
                           * unsafeProb (if_ (if_ (noiseEOld `less` 4)
                                                  (if_ (1 `less` noiseEOld)
                                                       (if_ (noiseTOld `less` 8)
                                                            (3 `less` noiseTOld)
                                                            false)
                                                       false)
                                                  false)
                                             (exp ((m1 ** 2 * fromProb (noiseTOld * noiseTOld * 2)
                                                    + m1 * m2 * fromProb (noiseTOld * noiseTOld) * (-2)
                                                    + m2 ** 2 * fromProb (noiseTOld * noiseTOld)
                                                    + m1 ** 2 * fromProb (noiseEOld * noiseEOld)
                                                    + m2 ** 2 * fromProb (noiseEOld * noiseEOld))
                                                   * (noiseTOld' ** 4
                                                      + fromProb (noiseEOld * noiseEOld * (noiseTOld * noiseTOld) * 3)
                                                      + noiseEOld' ** 4)
                                                     ** (-1)
                                                   * (1/2)))
                                             infinity)))),
             (1/2,
              uniform 3 8 `bind` \noiseT' ->
              dirac (pair (pair (unsafeProb noiseT') noiseEOld)
                          (sqrt_ (noiseTOld * noiseTOld * (noiseTOld * noiseTOld)
                                  + noiseEOld * noiseEOld * (noiseTOld * noiseTOld) * 3
                                  + noiseEOld * noiseEOld * (noiseEOld * noiseEOld))
                           * if_ (if_ (noiseEOld `less` 1) true (noiseEOld `equal` 1))
                                 0
                                 (if_ (noiseEOld `less` 4) 1 0)
                           * exp_ ((noiseT' * noiseT' * (m1 * m1) * 2
                                    + noiseT' * noiseT' * m1 * m2 * (-2)
                                    + noiseT' * noiseT' * (m2 * m2)
                                    + m1 * m1 * fromProb (noiseEOld * noiseEOld)
                                    + m2 * m2 * fromProb (noiseEOld * noiseEOld))
                                   * recip (noiseT' * noiseT' * (noiseT' * noiseT')
                                            + noiseT' * noiseT' * fromProb (noiseEOld * noiseEOld * 3)
                                            + noiseEOld' * noiseEOld' * (noiseEOld' * noiseEOld'))
                                   * (-1/2))
                           * recip (sqrt_ (unsafeProb (noiseT' ** 4
                                                       + noiseT' ** 2 * fromProb (noiseEOld * noiseEOld * 3)
                                                       + noiseEOld' ** 4)))
                           * unsafeProb (if_ (if_ (noiseEOld `less` 4)
                                                  (if_ (1 `less` noiseEOld)
                                                       (if_ (noiseTOld `less` 8)
                                                            (3 `less` noiseTOld)
                                                            false)
                                                       false)
                                                  false)
                                             (exp ((m1 ** 2 * fromProb (noiseTOld * noiseTOld * 2)
                                                    + m1 * m2 * fromProb (noiseTOld * noiseTOld) * (-2)
                                                    + m2 ** 2 * fromProb (noiseTOld * noiseTOld)
                                                    + m1 ** 2 * fromProb (noiseEOld * noiseEOld)
                                                    + m2 ** 2 * fromProb (noiseEOld * noiseEOld))
                                                   * (noiseTOld' ** 4
                                                      + fromProb (noiseEOld * noiseEOld * (noiseTOld * noiseTOld) * 3)
                                                      + noiseEOld' ** 4)
                                                     ** (-1)
                                                   * (1/2)))
                                             infinity))))]

makeChain
    :: (Lambda repr, Mochastic repr)
    => repr (HFun a (HMeasure a))
    -> repr HInt
    -> repr a
    -> repr (HMeasure (HArray a))
makeChain m n s = app (chain (vector n (\ _ ->
                                        lam $ \ss ->
                                        app m ss `bind` \s' ->
                                        dirac $ (pair s' s')))) s `bind` \vs' ->
                  dirac (fst_ vs')

runEasierRoadmapProg4 =
    runSample $ makeChain
        (app easierRoadmapProg4 (pair 0 1))
        20
        (pair 4 2)
