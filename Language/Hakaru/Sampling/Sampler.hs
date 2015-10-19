{-# LANGUAGE RankNTypes #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.18
-- |
-- Module      :  Language.Hakaru.Sampling.Sampler
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- TODO: is this still actually used anywhere? If so, we should eliminate the redundancy with "Language.Hakaru.Sampling.Metropolis"
----------------------------------------------------------------
module Language.Hakaru.Sampling.Sampler
    ( Sampler, deterministic, sbind, smap
    ) where

import Data.Functor ((<$>))
import Control.Monad.Primitive
import Language.Hakaru.Sampling.Mixture (Mixture, mnull, empty, scale, point)
import Language.Hakaru.Sampling.Distribution (choose)
import Language.Hakaru.Sampling.Types
----------------------------------------------------------------

-- | Sampling procedures that produce one sample
type Sampler a = (Functor m, PrimMonad m) => PRNG m -> m (Mixture a)

deterministic :: Mixture a -> Sampler a
deterministic m _ = return m

sbind :: Sampler a -> (a -> Sampler b) -> Sampler b
sbind s k g = do
    m1 <- s g
    if mnull m1
        then return empty
        else do
            (a, v) <- choose m1 g
            scale v <$> k a g

smap :: (a -> b) -> Sampler a -> Sampler b
smap f s =
    s `sbind` \a ->
    deterministic (point (f a) 1)

----------------------------------------------------------------
----------------------------------------------------------- fin.