{-# LANGUAGE TypeOperators #-}
module Arrow where

import InterpreterMH (Measure)

type a ~~> b = a -> Measure b
