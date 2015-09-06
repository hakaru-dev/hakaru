{-# LANGUAGE TypeFamilies, RankNTypes, FlexibleContexts, DataKinds #-}
module Language.Hakaru.Inference where

import Prelude hiding (Real)

import Language.Hakaru.Lazy
import Language.Hakaru.Compose
import Language.Hakaru.Syntax
import Language.Hakaru.Expect (Expect(..), Expect', normalize)

priorAsProposal
    :: Mochastic repr
    => repr ('HMeasure ('HPair a b))
    -> repr ('HPair a b)
    -> repr ('HMeasure ('HPair a b))
priorAsProposal p x =
    bern (1/2) `bind` \c ->
    p `bind` \x' ->
    dirac (if_ c
        (pair (fst_ x ) (snd_ x'))
        (pair (fst_ x') (snd_ x )))


mh  :: (Mochastic repr, Integrate repr, Lambda repr,
        a ~ Expect' a, Order_ a, Backward a a)
    => (forall repr'. (Mochastic repr') => repr' a -> repr' ('HMeasure a))
    -> (forall repr'. (Mochastic repr') => repr' ('HMeasure a))
    -> repr ('HFun a ('HMeasure ('HPair a 'HProb)))
mh proposal target =
  let_ (lam (d unit)) $ \mu ->
  lam $ \old ->
    proposal old `bind` \new ->
    dirac (pair new (mu `app` pair new old / mu `app` pair old new))
  where d:_ = density (\dummy -> ununit dummy $ bindx target proposal)


mcmc :: (Mochastic repr, Integrate repr, Lambda repr,
         a ~ Expect' a, Order_ a, Backward a a)
    => (forall repr'. (Mochastic repr') => repr' a -> repr' ('HMeasure a))
    -> (forall repr'. (Mochastic repr') => repr' ('HMeasure a))
    -> repr ('HFun a ('HMeasure a))
mcmc proposal target =
  let_ (mh proposal target) $ \f ->
  lam $ \old ->
    app f old `bind` \new_ratio ->
    unpair new_ratio $ \new ratio ->
    bern (min_ 1 ratio) `bind` \accept ->
    dirac (if_ accept new old)

gibbsProposal
    :: (Expect' a ~ a, Expect' b ~ b, Backward a a, Order_ a, 
        Mochastic repr, Integrate repr, Lambda repr)
    => Cond (Expect repr) 'HUnit ('HMeasure ('HPair a b))
    -> repr ('HPair a b)
    -> repr ('HMeasure ('HPair a b))
gibbsProposal p x = q (fst_ x) `bind` \x' -> dirac (pair (fst_ x) x')
  where d:_ = runDisintegrate p
        q y = normalize (app (app d unit) (Expect y))              

-- Slice sampling can be thought of:
--
-- slice target x = do
--      u  <- uniform(0, density(target, x))  
--      x' <- lebesgue
--      condition (density(target, x') >= u) true
--      return x'

slice
    :: (Mochastic repr, Integrate repr, Lambda repr)
    => (forall repr' . (Mochastic repr') => repr' ('HMeasure 'HReal))
    -> repr ('HFun 'HReal ('HMeasure 'HReal))
slice target = lam $ \x ->
               uniform 0 (densAt x) `bind` \u ->
               normalize $
               lebesgue `bind` \x' ->
               if_ (Expect (u `less_` densAt (unExpect x')))
                   (dirac x')
                   (superpose [])
  where d:_ = density (\dummy -> ununit dummy target)
        densAt x = fromProb $ d unit x


sliceX
    :: (Mochastic repr, Integrate repr, Lambda repr,
        a ~ Expect' a, Order_ a, Backward a a)
    => (forall repr' . (Mochastic repr') => repr' ('HMeasure a))
    -> repr ('HMeasure ('HPair a 'HReal))
sliceX target = target `bindx` \x ->
                uniform 0 (densAt x)
  where d:_ = density (\dummy -> ununit dummy target)
        densAt x = fromProb $ d unit x

incompleteBeta
    :: Integrate repr
    => repr 'HProb -> repr 'HProb -> repr 'HProb -> repr 'HProb
incompleteBeta x a b = integrate 0 (fromProb x)
                       (\t -> pow_ (unsafeProb t    ) (fromProb a-1) *
                              pow_ (unsafeProb $ 1-t) (fromProb b-1))

regBeta
    :: Integrate repr
    => repr 'HProb -> repr 'HProb -> repr 'HProb -> repr 'HProb
regBeta x a b = incompleteBeta x a b / betaFunc a b

tCDF :: Integrate repr => repr 'HReal -> repr 'HProb -> repr 'HProb
tCDF x v = 1 - (1/2)*regBeta (v / (unsafeProb (x*x) + v)) (v/2) (1/2)

approxMh
    :: (Mochastic repr, Integrate repr, Lambda repr,
        a ~ Expect' a, Order_ a, Backward a a)
    =>  (forall repr' . (Mochastic repr') => repr'  a -> repr' ('HMeasure a)) ->
        (forall repr' . (Mochastic repr') => repr' ('HMeasure a)) ->
        [repr a -> repr ('HMeasure a)] ->
        repr ('HFun a ('HMeasure a))
approxMh proposal prior (x:xs) =
  lam $ \old ->
  let_ (lam (d unit)) $ \mu ->
  liftM unsafeProb (uniform 0 1) `bind` \u ->
  proposal old `bind` \new ->
  let_ (u * mu `app` pair new old / mu `app` pair old new) $ \u0 ->
  let_ ((l new new) / (l old old)) $ \l0 ->
  let_ (tCDF (n - 1) (l0 - u0)) $ \delta ->
  if_ (delta `less` eps)
  (if_ (u0 `less` l0) (dirac new) (dirac old))
  (app (approxMh proposal prior xs) old)
  where n = 2000
        eps = 1/20
        d:_ = density (\dummy -> ununit dummy $ bindx prior proposal)
        l:_ = [(\d1 d2 -> 2)] -- density (\theta -> x theta)      
