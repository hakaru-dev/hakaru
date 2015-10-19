{-# LANGUAGE RankNTypes #-}
{-# OPTIONS -W #-}

module Language.Hakaru.Sampling.Sampler (Sampler, deterministic, sbind, smap) where

import Language.Hakaru.Sampling.Mixture (Mixture, mnull, empty, scale, point)
import Language.Hakaru.Sampling.Distribution (choose)
import Language.Hakaru.Sampling.Types
import Control.Monad.Primitive

-- Sampling procedures that produce one sample

type Sampler a = PrimMonad m => PRNG m -> m (Mixture a)

deterministic :: Mixture a -> Sampler a
deterministic m _ = return m

sbind :: Sampler a -> (a -> Sampler b) -> Sampler b
sbind s k g = do
  m1 <- s g
  if mnull m1 then 
      return empty
  else do (a, v) <- choose m1 g
          m2 <- k a g
          return (scale v m2)

smap :: (a -> b) -> Sampler a -> Sampler b
smap f s = sbind s (\a -> deterministic (point (f a) 1))
