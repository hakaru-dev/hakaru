{-# LANGUAGE TypeOperators #-}
module Language.Hakaru.Arrow where

import Language.Hakaru.Distribution (Dist)

type a ~~> b = a -> Dist b
