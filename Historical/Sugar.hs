{-# LANGUAGE DataKinds, TypeOperators, RebindableSyntax #-}
{-# OPTIONS -W #-}

module Historical.Sugar where

import Historical.Interpreter
import Prelude

test_do :: Measure '[Lebesgue Double] Bool
test_do = let f >>= x = bind f x
              f >> x = bind f (\_ -> x)
              return x = unconditioned (dirac x)
          in do 
            coin <- unconditioned (uniform False True)
            conditioned (if coin then normal 1 1 else uniform 0 3)
            return coin
