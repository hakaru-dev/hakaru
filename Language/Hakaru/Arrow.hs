{-# LANGUAGE TypeOperators #-}
module Language.Hakaru.Arrow where

import Language.Hakaru.Metropolis (CSampler)

type a ~~> b = a -> CSampler b
