{- These are here because they are shared between tests -}
module Tests.Models where

import Prelude hiding (Real)

import Language.Hakaru.Syntax

t4 :: Mochastic repr => repr (Measure (Prob, Bool))
t4 = beta 1 1 `bind` \bias -> bern bias `bind` \coin -> dirac (pair bias coin)

t4' :: Mochastic repr => repr (Measure (Prob, Bool))
t4' = (uniform  0 1) `bind` \x3 ->
      superpose [((unsafeProb x3)               ,(dirac (pair (unsafeProb x3) true))),
                 ((unsafeProb (1 + (x3 * (-1)))),(dirac (pair (unsafeProb x3) false)))]

norm :: Mochastic repr => repr (Measure (Real, Real))
norm = normal 0 1 `bind` \x ->
       normal x 1 `bind` \y ->
       dirac (pair x y)

unif2 :: Mochastic repr => repr (Measure (Real, Real))
unif2 = uniform (-1) 1 `bind` \x ->
        uniform (x-1) (x+1) `bind` \y ->
        dirac (pair x y)

