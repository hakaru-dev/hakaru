{-# LANGUAGE TypeOperators #-}
module Language.Hakaru.Arrow where

import Language.Hakaru.Types (Dist)

type a ~~> b = a -> Dist b
