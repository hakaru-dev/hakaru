{-# LANGUAGE RankNTypes, BangPatterns #-}
{-# OPTIONS -W #-}

module Language.Hakaru.Sampling.Mixture (Prob, point, empty, scale,
  Mixture(..), toList, mnull, mmap, cross, mode) where

import Data.Monoid
import Data.Ord (comparing)
import Data.List (maximumBy)
import qualified Data.Map.Strict as M
import Data.Number.LogFloat hiding (isInfinite)
import Text.Show (showListWith)
import Numeric (showFFloat)

type Prob = LogFloat

-- Mixtures (the results of importance sampling)

newtype Mixture k = Mixture { unMixture :: M.Map k Prob }

instance (Show k) => Show (Mixture k) where
  showsPrec d (Mixture m) = showParen (d > 0) $
    showString "Mixture $ fromList " . showListWith s (M.toList m)
    where s (k,p) = showChar '('
                  . shows k
                  . showChar ','
                  . (if isInfinite l || -42 < l && l < 42
                     then showFFloat Nothing (fromLogFloat p :: Double)
                     else showString "logToLogFloat " . showsPrec 11 l)
                  . showChar ')'
            where l = logFromLogFloat p :: Double

instance (Ord k) => Monoid (Mixture k) where
  mempty        = empty
  mappend m1 m2 = Mixture (M.unionWith (+) (unMixture m1) (unMixture m2))
  mconcat ms    = Mixture (M.unionsWith (+) (map unMixture ms))

empty :: Mixture k
empty = Mixture M.empty

toList :: Mixture k -> [(k, Prob)]
toList = M.toList . unMixture

mnull :: Mixture k -> Bool
mnull = all (0>=) . M.elems . unMixture

point :: k -> Prob -> Mixture k
point k !v = Mixture (M.singleton k v)

scale :: Prob -> Mixture k -> Mixture k
scale !v = Mixture . M.map (v *) . unMixture

mmap :: (Ord k2) => (k1 -> k2) -> Mixture k1 -> Mixture k2
mmap f = Mixture . M.mapKeysWith (+) f . unMixture

cross :: (Ord k) => (k1 -> k2 -> k) -> Mixture k1 -> Mixture k2 -> Mixture k
cross f m1 m2 = mconcat [ mmap (`f` k) (scale v m1)
                        | (k,v) <- M.toList (unMixture m2) ]

mode :: Mixture k -> (k, Prob)
mode (Mixture m) = maximumBy (comparing snd) (M.toList m)
