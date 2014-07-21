{-# LANGUAGE RankNTypes #-}
{-# OPTIONS -W #-}

module Language.Hakaru.Sampler (Sampler, deterministic, sbind, smap) where

import Language.Hakaru.Mixture (Mixture, mnull, empty, scale, point)
import Language.Hakaru.RandomChoice (choose)
import System.Random (RandomGen)

-- Sampling procedures that produce one sample

type Sampler a = forall g. (RandomGen g) => g -> (Mixture a, g)

deterministic :: Mixture a -> Sampler a
deterministic m g = (m, g)

sbind :: Sampler a -> (a -> Sampler b) -> Sampler b
sbind s k g0 =
  case s g0 of { (m1, g1) ->
    if mnull m1 then (empty, g1) else
      case choose m1 g1 of { (a, v, g2) ->
        case k a g2 of { (m2, g) ->
          (scale v m2, g) } } }

smap :: (a -> b) -> Sampler a -> Sampler b
smap f s = sbind s (\a -> deterministic (point (f a) 1))
