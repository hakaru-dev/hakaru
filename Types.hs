{-# LANGUAGE RankNTypes, BangPatterns #-}
{-# OPTIONS -W #-}

module Types where

import Sampler (Sampler)

import Data.Dynamic

-- Basic types for conditioning and conditioned sampler
data Cond = Unconditioned | Lebesgue !Dynamic | Discrete !Dynamic
  deriving (Show)
newtype CSampler a = CSampler (Cond -> Sampler a)
