{-# LANGUAGE NoMonomorphismRestriction, GADTs #-}
module Tests.Models where

import Prelude hiding (Real)

import Language.Hakaru.Syntax2
import Language.Hakaru.Lambda
import qualified Language.Hakaru.Types as T

-- if we want to forgo the (D m) constraint, need to decorate the
-- program a little more.
prog_mixture :: (Meas m, D m ~ T.Dist ) => m Bool
prog_mixture = do
  c <- unconditioned (bern 0.5)
  _ <- conditioned (ifThenElse c (normal 1 1)
                                 (uniform 0 3))
  return c

prog_multiple_conditions :: (Meas m, D m ~ T.Dist) => m Double
prog_multiple_conditions = do
  b <- unconditioned (beta 1 1)
  _ <- conditioned (bern b)
  _ <- conditioned (bern b)
  return b


