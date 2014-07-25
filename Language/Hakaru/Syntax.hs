{-# LANGUAGE TypeFamilies, ConstraintKinds, GADTs, FlexibleContexts #-}

module Language.Hakaru.Syntax where

-- We want to our own Real
import           Prelude hiding (Real)

-- The syntax

import GHC.Exts (Constraint)
import Data.Dynamic (Typeable)

-- TODO: The pretty-printing semantics

import qualified Text.PrettyPrint as PP

-- The importance-sampling semantics

import qualified Language.Hakaru.Types as T
import qualified Data.Number.LogFloat as LF
import qualified Language.Hakaru.ImportanceSampler as IS

-- The Metropolis-Hastings semantics
import qualified Language.Hakaru.Distribution as D
import qualified Language.Hakaru.Metropolis as MH

-- The syntax

data Real
data Prob
data Measure a
data Dist a

class Mochastic repr where
  type Type repr a :: Constraint
  type MEq repr a :: Constraint
  real        :: Rational -> repr Real
  bool        :: Bool -> repr Bool
  add, mul    :: repr Real -> repr Real -> repr Real
  neg         :: repr Real -> repr Real
  neg         =  mul (real (-1))
  logFloat, logToLogFloat
              :: repr Real -> repr Prob
  unbool      :: repr Bool -> repr c -> repr c
              -> repr c
  pair        :: repr a -> repr b -> repr (a, b)
  unpair      :: repr (a, b) -> (repr a -> repr b -> repr c)
              -> repr c
  inl         :: repr a -> repr (Either a b)
  inr         :: repr b -> repr (Either a b)
  uneither    :: repr (Either a b) -> (repr a -> repr c) -> (repr b -> repr c)
              -> repr c
  nil         :: repr [a]
  cons        :: repr a -> repr [a] -> repr [a]
  unlist      :: repr [a] -> repr c -> (repr a -> repr [a] -> repr c)
              -> repr c
  ret         :: repr a -> repr (Measure a)
  bind        :: repr (Measure a) -> (repr a -> repr (Measure b))
              -> repr (Measure b)
  conditioned, unconditioned :: (Type repr a) => repr (Dist a) -> repr (Measure a)
  factor      :: repr Prob -> repr (Measure ())
  dirac       :: MEq repr a => repr a -> repr (Dist a)
  categorical :: (MEq repr a) => repr [(a, Real)] -> repr (Dist a)
  bern        :: (MEq repr Bool) => repr Real -> repr (Dist Bool)
  bern p      =  categorical $
                 cons (pair (bool True) p) $
                 cons (pair (bool False) (add (real 1) (neg p))) $
                 nil
  normal, uniform
              :: repr Real -> repr Real -> repr (Dist Real)
  poisson     :: repr Real -> repr (Dist Int)

-- TODO: The initial (AST) "semantics"
-- (Hey Oleg, is there any better way to deal with the Type constraint, so that
-- the AST constructor doesn't have to take a repr constructor argument?)

data AST (repr :: * -> *) a where
  Real :: Rational -> AST repr Real
  Unbool :: AST repr Bool -> AST repr c -> AST repr c -> AST repr c
  Categorical :: (MEq repr a) => AST repr [(a, Real)] -> AST repr (Dist a)
  -- ...

instance (Mochastic repr) => Mochastic (AST repr) where
  type Type (AST repr) a = Type repr a
  type MEq (AST repr) a = MEq repr a
  real = Real
  unbool = Unbool
  categorical = Categorical
  -- ...

eval :: (Mochastic repr) => AST repr a -> repr a
eval (Real x) = real x
eval (Unbool b x y) = unbool (eval b) (eval x) (eval y)
eval (Categorical xps) = categorical (eval xps)
-- ...

-- TODO: The pretty-printing semantics

newtype PP a = PP (Int -> PP.Doc)

-- The importance-sampling semantics

newtype IS a = IS (IS' a)
type family IS' a
type instance IS' (Measure a)  = IS.Measure (IS' a)
type instance IS' (Dist a)     = T.Dist (IS' a)
type instance IS' [a]          = [IS' a]
type instance IS' (a, b)       = (IS' a, IS' b)
type instance IS' (Either a b) = Either (IS' a) (IS' b)
type instance IS' ()           = ()
type instance IS' Bool         = Bool
type instance IS' Real         = Double
type instance IS' Prob         = LF.LogFloat
type instance IS' Int          = Int

instance Mochastic IS where
  type Type IS a = Typeable (IS' a)
  type MEq IS a = Eq (IS' a)
  real                    = IS . fromRational
  bool                    = IS
  add (IS x) (IS y)       = IS (x + y)
  mul (IS x) (IS y)       = IS (x * y)
  neg (IS x)              = IS (-x)
  logFloat (IS x)         = IS (LF.logFloat x)
  logToLogFloat (IS x)    = IS (LF.logToLogFloat x)
  unbool (IS b) x y       = if b then x else y
  pair (IS x) (IS y)      = IS (x, y)
  unpair (IS (x, y)) c    = c (IS x) (IS y)
  inl (IS x)              = IS (Left x)
  inr (IS x)              = IS (Right x)
  uneither (IS e) c d     = either (c . IS) (d . IS) e
  nil                     = IS []
  cons (IS x) (IS xs)     = IS (x:xs)
  unlist (IS []) n c      = n
  unlist (IS (x:xs)) n c  = c (IS x) (IS xs)
  ret (IS x)              = IS (return x)
  bind (IS m) k           = IS (m >>= \x -> case k (IS x) of IS n -> n)
  conditioned (IS dist)   = IS (IS.conditioned dist)
  unconditioned (IS dist) = IS (IS.unconditioned dist)
  factor (IS p)           = IS (IS.factor p)
  dirac (IS x)            = IS (D.dirac x)
  categorical (IS xps)    = IS (D.categorical xps)
  bern (IS p)             = IS (D.bern p)
  normal (IS m) (IS s)    = IS (D.normal m s)
  uniform (IS lo) (IS hi) = IS (D.uniform lo hi)
  poisson (IS l)          = IS (D.poisson l)

-- The Metropolis-Hastings semantics

newtype MH a = MH (MH' a)
type family MH' a
type instance MH' (Measure a)  = MH.Measure (MH' a)
type instance MH' (Dist a)     = T.Dist (MH' a)
type instance MH' [a]          = [MH' a]
type instance MH' (a, b)       = (MH' a, MH' b)
type instance MH' (Either a b) = Either (MH' a) (MH' b)
type instance MH' ()           = ()
type instance MH' Bool         = Bool
type instance MH' Real         = Double
type instance MH' Prob         = T.LogLikelihood
type instance MH' Int          = Int

instance Mochastic MH where
  type Type MH a = (Typeable (MH' a))
  type MEq MH a = (Eq (MH' a))
  real                    = MH . fromRational
  bool                    = MH
  add (MH x) (MH y)       = MH (x + y)
  mul (MH x) (MH y)       = MH (x * y)
  neg (MH x)              = MH (-x)
  logFloat (MH x)         = MH (LF.logFromLogFloat (LF.logFloat x))
  logToLogFloat (MH x)    = MH (LF.logFromLogFloat (LF.logToLogFloat x))
  unbool (MH b) x y       = if b then x else y
  pair (MH x) (MH y)      = MH (x, y)
  unpair (MH (x, y)) c    = c (MH x) (MH y)
  inl (MH x)              = MH (Left x)
  inr (MH x)              = MH (Right x)
  uneither (MH e) c d     = either (c . MH) (d . MH) e
  nil                     = MH []
  cons (MH x) (MH xs)     = MH (x:xs)
  unlist (MH []) n c      = n
  unlist (MH (x:xs)) n c  = c (MH x) (MH xs)
  ret (MH x)              = MH (return x)
  bind (MH m) k           = MH (m >>= \x -> case k (MH x) of MH n -> n)
  conditioned (MH dist)   = MH (MH.conditioned dist)
  unconditioned (MH dist) = MH (MH.unconditioned dist)
  factor (MH p)           = MH (MH.factor p)
  dirac (MH x)            = MH (D.dirac x)
  categorical (MH xps)    = MH (D.categorical xps)
  bern (MH p)             = MH (D.bern p)
  normal (MH m) (MH s)    = MH (D.normal m s)
  uniform (MH lo) (MH hi) = MH (D.uniform lo hi)
  poisson (MH l)          = MH (D.poisson l) 
