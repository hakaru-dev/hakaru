{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleContexts #-}

-- This alternate, much simpler syntax, is aimed at unifying our current
-- interpreters, so as to lessen the code duplication in the tests.
-- It is not meant to be 'general', that is what Syntax is for.
module Language.Hakaru.Syntax2 where

-- We want to our own Real
import           Prelude hiding (Real)
import Data.Dynamic (Typeable)

-- The syntax
import Language.Hakaru.Lambda
import qualified Language.Hakaru.Distribution as D

-- TODO: The pretty-printing semantics
-- import qualified Text.PrettyPrint as PP

-- The importance-sampling semantics

import qualified Language.Hakaru.Types as T
-- import qualified Data.Number.LogFloat as LF
import qualified Language.Hakaru.ImportanceSampler as IS

-- The Metropolis-Hastings semantics
import qualified Language.Hakaru.Metropolis as MH

-- The syntax

data Prob
data Measure a
data Dist a

-- A language of distributions
class Distrib d where
  type Real d :: *
  dirac       :: Eq a => a -> d a
  categorical :: Eq a => [(a, Real d)] -> d a
  bern        :: Real d -> d Bool
  normal, uniform :: Real d -> Real d -> d (Real d)
  poisson     :: Real d -> d Integer
  uniformD    :: Integer -> Integer -> d Integer

-- Measures m 'over' distributions d
class (Monad m) => Meas m where
  type D m :: * -> *
  conditioned, unconditioned :: (Typeable a, Distrib (D m)) => D m a -> m a

instance Distrib T.Dist where
  type Real T.Dist = Double
  dirac = D.dirac
  categorical = D.categorical
  bern = D.bern
  uniform = D.uniform
  uniformD = D.uniformD
  normal = D.normal
  poisson = D.poisson

-- The importance-sampling semantics
instance Meas IS.Measure where
  type D IS.Measure = T.Dist
  conditioned = IS.conditioned
  unconditioned = IS.unconditioned

-- The Metropolis-Hastings semantics
instance Meas MH.Measure where
  type D MH.Measure = T.Dist
  conditioned = MH.conditioned
  unconditioned = MH.unconditioned

-- if we want to forgo the (D m) constraint, need to decorate the
-- program a little more.
prog_mixture :: (Meas m, D m ~ T.Dist) => m Bool
prog_mixture = do
  c <- unconditioned (bern 0.5)
  _ <- conditioned (ifThenElse c (normal 1 1)
                                 (uniform 0 3))
  return c
{-
-- TODO: The pretty-printing semantics
newtype PP a = PP (Int -> PP.Doc)

-- TODO: The initial (AST) "semantics"

data AST (repr :: * -> *) a where

eval :: (Mochastic repr) => AST repr a -> repr a
eval (Real x) = real x
eval (Unbool b x y) = unbool (eval b) (eval x) (eval y)
eval (Categorical xps) = categorical (eval xps)
-- ...
-}
