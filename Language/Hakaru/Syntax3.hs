{-# LANGUAGE MultiParamTypeClasses, TypeFamilies,
             FlexibleContexts, FlexibleInstances, DefaultSignatures,
             StandaloneDeriving, GeneralizedNewtypeDeriving #-}

module Syntax3 where

import Prelude hiding (Real)
import qualified Data.Number.LogFloat as LF
import qualified System.Random.MWC as MWC
import Control.Monad.Primitive (PrimState, PrimMonad)

-- A small probabilistic language with conditioning

infixl 1 `bind`, `bind_`

data Real
data Prob
data Measure a

type Bool_ = Either () ()

class Order repr a where
  less :: repr a -> repr a -> repr Bool_
  default less :: (Ord (repr a), Chastic repr) => repr a -> repr a -> repr Bool_
  less x y = if x < y then true else false

class (Order repr Real, Floating (repr Real),
       Order repr Prob, Fractional (repr Prob)) => Chastic repr where
  unit         :: repr ()
  pair         :: repr a -> repr b -> repr (a,b)
  unpair       :: repr (a,b) -> (repr a -> repr b -> repr c) -> repr c
  inl          :: repr a -> repr (Either a b)
  inr          :: repr b -> repr (Either a b)
  uneither     :: repr (Either a b) -> (repr a -> repr c) ->
                                       (repr b -> repr c) -> repr c
  unsafeProb   :: repr Real -> repr Prob
  fromProb     :: repr Prob -> repr Real

true, false :: (Chastic repr) => repr Bool_
true  = inl unit
false = inr unit

fst_ :: (Chastic repr) => repr (a,b) -> repr a
fst_ ab = unpair ab (\a b -> a)

snd_ :: (Chastic repr) => repr (a,b) -> repr b
snd_ ab = unpair ab (\a b -> b)

if_ :: (Chastic repr) => repr Bool_ -> repr c -> repr c -> repr c
if_ i t e = uneither i (\_ -> t) (\_ -> e)

and_ :: (Chastic repr) => [repr Bool_] -> repr Bool_
and_ []     = true
and_ [b]    = b
and_ (b:bs) = if_ b (and_ bs) false

class (Chastic repr) => Mochastic repr where
  dirac        :: repr a -> repr (Measure a)
  bind         :: repr (Measure a) -> (repr a -> repr (Measure b)) ->
                  repr (Measure b)
  lebesgue     :: repr (Measure Real)
  factor       :: repr Prob -> repr (Measure ())
  disintegrate :: repr (Measure a) -> repr (Measure (a,b)) ->
                  repr a -> repr (Measure b)

bind_ :: (Mochastic repr) => repr (Measure a) -> repr (Measure b) ->
                             repr (Measure b)
m `bind_` n = m `bind` \_ -> n

liftM :: (Mochastic repr) => (repr a -> repr b) ->
                             repr (Measure a) -> repr (Measure b)
liftM f m = m `bind` dirac . f

uniform :: (Mochastic repr) => repr Real -> repr Real -> repr (Measure Real)
uniform lo hi = lebesgue `bind` \x ->
                factor (if_ (and_ [less lo x, less x hi])
                            (unsafeProb (recip (hi - lo)))
                            0) `bind_`
                dirac x

bern :: (Mochastic repr) => repr Real -> repr (Measure Bool_)
bern p = uniform 0 1 `bind` \u -> dirac (less u p)

condition :: (Mochastic repr) => repr (Measure (a,b)) ->
                                 repr a -> repr (Measure b)
condition m = disintegrate (liftM fst_ m) m

density :: (Mochastic repr) => repr (Measure a) -> repr (Measure a) ->
                               repr a -> repr (Measure ())
density ambient m = disintegrate ambient (liftM (`pair` unit) m)

-- Importance sampling interpretation

newtype Sample m a = Sample { unSample :: Sample' m a }
type family Sample' (m :: * -> *) (a :: *)
type instance Sample' m Real         = Double
type instance Sample' m Prob         = LF.LogFloat
type instance Sample' m ()           = ()
type instance Sample' m (a, b)       = (Sample' m a, Sample' m b)
type instance Sample' m (Either a b) = Either (Sample' m a) (Sample' m b)
type instance Sample' m (Measure a)  = LF.LogFloat -> MWC.Gen (PrimState m) ->
                                       m (Sample' m a, LF.LogFloat)

instance (Monad m) => Order (Sample m) Real

deriving instance Eq (Sample m Real)
deriving instance Ord (Sample m Real)
deriving instance Num (Sample m Real)
deriving instance Fractional (Sample m Real)
deriving instance Floating (Sample m Real)

instance (Monad m) => Order (Sample m) Prob

deriving instance Eq (Sample m Prob)
deriving instance Ord (Sample m Prob)
deriving instance Num (Sample m Prob)
deriving instance Fractional (Sample m Prob)

instance (Monad m) => Chastic (Sample m) where
  unit                            = Sample ()
  pair (Sample a) (Sample b)      = Sample (a,b)
  unpair (Sample (a,b)) k         = k (Sample a) (Sample b)
  inl (Sample a)                  = Sample (Left a)
  inr (Sample b)                  = Sample (Right b)
  uneither (Sample (Left  a)) k _ = k (Sample a)
  uneither (Sample (Right b)) _ k = k (Sample b)
  unsafeProb (Sample x)           = Sample (LF.logFloat x)
  fromProb (Sample x)             = Sample (LF.fromLogFloat x)

instance (PrimMonad m) => Mochastic (Sample m) where
  dirac (Sample a)                = Sample (\p _ -> return (a,p))
  bind (Sample m) k               = Sample (\p g -> do
                                      (a,p) <- m p g
                                      unSample (k (Sample a)) p g)
  lebesgue                        = Sample (\p g -> do
                                      (u,b) <- MWC.uniform g
                                      let l = log u; n = negate l
                                      return (if b then n else l,
                                              p * LF.logToLogFloat n))
  factor (Sample q)               = Sample (\p _ -> return ((), p * q))
  disintegrate                    = error "disintegrate: not implemented"

-- Trivial example: importance sampling once from the Lebesgue measure

main :: IO ()
main = MWC.withSystemRandom (MWC.asGenST (unSample lebesgue 1)) >>= print
