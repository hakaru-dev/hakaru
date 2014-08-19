{-# LANGUAGE MultiParamTypeClasses, TypeFamilies,
             FlexibleContexts, FlexibleInstances, DefaultSignatures,
             StandaloneDeriving, GeneralizedNewtypeDeriving #-}

module Syntax3 where

import Prelude hiding (Real)
import Data.Ratio
import qualified Data.Number.LogFloat as LF
import qualified System.Random.MWC as MWC
import qualified Numeric.Integration.TanhSinh as TS
import Control.Monad.Primitive (PrimState, PrimMonad)

-- A small probabilistic language with conditioning

infixl 1 `bind`, `bind_`
infixl 9 `app`

data Real
data Prob -- meaning: non-negative real number
data Measure a

type Bool_ = Either () ()

class Order repr a where
  less :: repr a -> repr a -> repr Bool_
  default less :: (Ord (repr a), Base repr) => repr a -> repr a -> repr Bool_
  less x y = if x < y then true else false

class (Order repr Real, Floating (repr Real),
       Order repr Prob, Fractional (repr Prob)) => Base repr where
  unit       :: repr ()
  pair       :: repr a -> repr b -> repr (a,b)
  unpair     :: repr (a,b) -> (repr a -> repr b -> repr c) -> repr c
  inl        :: repr a -> repr (Either a b)
  inr        :: repr b -> repr (Either a b)
  uneither   :: repr (Either a b) -> (repr a -> repr c) ->
                                     (repr b -> repr c) -> repr c
  unsafeProb :: repr Real -> repr Prob
  fromProb   :: repr Prob -> repr Real

true, false :: (Base repr) => repr Bool_
true  = inl unit
false = inr unit

fst_ :: (Base repr) => repr (a,b) -> repr a
fst_ ab = unpair ab (\a b -> a)

snd_ :: (Base repr) => repr (a,b) -> repr b
snd_ ab = unpair ab (\a b -> b)

if_ :: (Base repr) => repr Bool_ -> repr c -> repr c -> repr c
if_ i t e = uneither i (\_ -> t) (\_ -> e)

and_ :: (Base repr) => [repr Bool_] -> repr Bool_
and_ []     = true
and_ [b]    = b
and_ (b:bs) = if_ b (and_ bs) false

class (Base repr) => Mochastic repr where
  dirac        :: repr a -> repr (Measure a)
  bind         :: repr (Measure a) -> (repr a -> repr (Measure b)) ->
                  repr (Measure b)
  lebesgue     :: repr (Measure Real)
  factor       :: repr Prob -> repr (Measure ())

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

class (Mochastic repr) => Disintegrate repr where
  disintegrate :: repr (Measure a) -> repr (Measure (a,b)) ->
                  repr a -> repr (Measure b)

condition :: (Disintegrate repr) => repr (Measure (a,b)) ->
                                    repr a -> repr (Measure b)
condition m = disintegrate (liftM fst_ m) m

density :: (Disintegrate repr) => repr (Measure a) -> repr (Measure a) ->
                                  repr a -> repr (Measure ())
density ambient m = disintegrate ambient (liftM (`pair` unit) m)

class (Base repr) => Integrate repr where
  integrate :: (repr Real -> repr Prob) -> repr Prob

class Lambda repr where
  lam :: (repr a -> repr b) -> repr (a -> b)
  app :: repr (a -> b) -> repr a -> repr b

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
type instance Sample' m (a -> b)     = Sample' m a -> Sample' m b

instance Order (Sample m) Real

deriving instance Eq         (Sample m Real)
deriving instance Ord        (Sample m Real)
deriving instance Num        (Sample m Real)
deriving instance Fractional (Sample m Real)
deriving instance Floating   (Sample m Real)

instance Order (Sample m) Prob

deriving instance Eq         (Sample m Prob)
deriving instance Ord        (Sample m Prob)
deriving instance Num        (Sample m Prob)
deriving instance Fractional (Sample m Prob)

instance Base (Sample m) where
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
                                      (unSample (k (Sample a)) $! p) g)
  lebesgue                        = Sample (\p g -> do
                                      (u,b) <- MWC.uniform g
                                      let l = log u; n = negate l
                                      return (if b then n else l,
                                              p * LF.logToLogFloat n))
  factor (Sample q)               = Sample (\p _ -> return ((), p * q))

instance Integrate (Sample m) where
  integrate f = Sample $ LF.logFloat -- just for kicks -- imprecise
              $ TS.result $ last $ TS.everywhere TS.parTrap
              $ LF.fromLogFloat . unSample . f . Sample

instance Lambda (Sample m) where
  lam f = Sample (unSample . f . Sample)
  app (Sample rator) (Sample rand) = Sample (rator rand)

-- Expectation interpretation

newtype Expect repr a = Expect { unExpect :: repr (Expect' a) }
type family Expect' (a :: *)
type instance Expect' Real         = Real
type instance Expect' Prob         = Prob
type instance Expect' ()           = ()
type instance Expect' (a, b)       = (Expect' a, Expect' b)
type instance Expect' (Either a b) = Either (Expect' a) (Expect' b)
type instance Expect' (Measure a)  = (Expect' a -> Prob) -> Prob
type instance Expect' (a -> b)     = (Expect' a -> Expect' b)

instance (Order repr Real) => Order (Expect repr) Real where
  less (Expect x) (Expect y) = Expect (less x y)

deriving instance (Eq         (repr Real)) => Eq         (Expect repr Real)
deriving instance (Ord        (repr Real)) => Ord        (Expect repr Real)
deriving instance (Num        (repr Real)) => Num        (Expect repr Real)
deriving instance (Fractional (repr Real)) => Fractional (Expect repr Real)
deriving instance (Floating   (repr Real)) => Floating   (Expect repr Real)

instance (Order repr Prob) => Order (Expect repr) Prob where
  less (Expect x) (Expect y) = Expect (less x y)

deriving instance (Eq         (repr Prob)) => Eq         (Expect repr Prob)
deriving instance (Ord        (repr Prob)) => Ord        (Expect repr Prob)
deriving instance (Num        (repr Prob)) => Num        (Expect repr Prob)
deriving instance (Fractional (repr Prob)) => Fractional (Expect repr Prob)

instance (Base repr) => Base (Expect repr) where
  unit                       = Expect unit
  pair (Expect a) (Expect b) = Expect (pair a b)
  unpair (Expect ab) k       = Expect (unpair ab (\a b ->
                               unExpect (k (Expect a) (Expect b))))
  inl (Expect a)             = Expect (inl a)
  inr (Expect b)             = Expect (inr b)
  uneither (Expect ab) ka kb = Expect (uneither ab (unExpect . ka . Expect)
                                                   (unExpect . kb . Expect))
  unsafeProb                 = Expect . unsafeProb . unExpect
  fromProb                   = Expect . fromProb   . unExpect

instance (Integrate repr) => Integrate (Expect repr) where
  integrate f = Expect (integrate (unExpect . f . Expect))

instance (Integrate repr, Lambda repr) => Mochastic (Expect repr) where
  dirac (Expect a)  = Expect (lam (\c -> c `app` a))
  bind (Expect m) k = Expect (lam (\c -> m `app` lam (\a ->
                      unExpect (k (Expect a)) `app` c)))
  lebesgue          = Expect (lam (integrate . app))
  factor (Expect q) = Expect (lam (\c -> q * c `app` unit))

instance (Lambda repr) => Lambda (Expect repr) where
  lam f = Expect (lam (unExpect . f . Expect))
  app (Expect rator) (Expect rand) = Expect (app rator rand)

-- Maple printing interpretation

newtype Maple a = Maple { unMaple :: Int -> String }

mapleFun1 :: String -> Maple a -> Maple b
mapleFun1 fn (Maple x) = Maple (\i -> fn ++ "(" ++ x i ++ ")")

mapleOp2 :: String -> Maple a -> Maple b -> Maple c
mapleOp2 fn (Maple x) (Maple y) = Maple (\i -> "(" ++ x i ++ fn ++ y i ++ ")")

mapleBind :: (Maple a -> Maple b) -> Int -> (String, String)
mapleBind f i = (x, unMaple (f (Maple (\_ -> x))) (i + 1))
  where x = "x" ++ show i

instance Order Maple a where
  less (Maple x) (Maple y) = Maple (\i -> "piecewise((" ++ x i ++ "<" ++ y i ++
                                          "), [true,[]], [false,[]])")

instance Num (Maple a) where
  (+)              = mapleOp2 "+"
  (*)              = mapleOp2 "*"
  (-)              = mapleOp2 "-"
  negate (Maple x) = Maple (\i -> "(-" ++ x i ++ ")")
  abs              = mapleFun1 "abs"
  signum           = mapleFun1 "signum"
  fromInteger x    = Maple (\_ -> show x)

instance Fractional (Maple a) where
  (/)            = mapleOp2 "/"
  fromRational x = Maple (\_ -> "(" ++ show (numerator   x) ++
                                "/" ++ show (denominator x) ++ ")")

instance Floating (Maple a) where
  pi                          = Maple (\_ -> "Pi")
  exp                         = mapleFun1 "exp"
  sqrt                        = mapleFun1 "sqrt"
  log                         = mapleFun1 "log"
  (**)                        = mapleOp2 "^"
  logBase (Maple b) (Maple y) = Maple (\i -> "log[" ++ b i ++ "]" ++
                                                "(" ++ y i ++ ")")
  sin                         = mapleFun1 "sin"
  tan                         = mapleFun1 "tan"
  cos                         = mapleFun1 "cos"
  asin                        = mapleFun1 "asin"
  atan                        = mapleFun1 "atan"
  acos                        = mapleFun1 "acos"
  sinh                        = mapleFun1 "sinh"
  tanh                        = mapleFun1 "tanh"
  cosh                        = mapleFun1 "cosh"
  asinh                       = mapleFun1 "asinh"
  atanh                       = mapleFun1 "atanh"
  acosh                       = mapleFun1 "acosh"

instance Base Maple where
  unit = Maple (\_ -> "[]")
  pair (Maple a) (Maple b) = Maple (\i -> "[" ++ a i ++ "," ++ b i ++ "]")
  unpair (Maple ab) k = k (Maple (\i -> ab i ++ "[1]"))
                          (Maple (\i -> ab i ++ "[2]"))
  inl (Maple a) = Maple (\i -> "[true,"  ++ a i ++ "]")
  inr (Maple b) = Maple (\i -> "[false," ++ b i ++ "]")
  uneither (Maple ab) ka kb = Maple (\i ->
    let continue :: (Maple ab -> Maple c) -> String
        continue k = unMaple (k (Maple (const (ab i ++ "[2]")))) i
    in "piecewise(" ++ ab i ++ "[1]," ++ continue ka ++
                                  "," ++ continue kb ++ ")")
  unsafeProb (Maple x) = Maple x
  fromProb   (Maple x) = Maple x

instance Integrate Maple where
  integrate f = Maple (\i ->
    let (x, body) = mapleBind f i
    in "int(" ++ body ++ "," ++ x ++ "=-infinity..infinity)")

instance Lambda Maple where
  lam f = Maple (\i -> let (x, body) = mapleBind f i
                       in "(" ++ x ++ "->" ++ body ++ ")")
  app (Maple rator) (Maple rand) = Maple (\i -> rator i ++ "(" ++ rand i ++ ")")

-- Trivial example: importance sampling once from a uniform measure

main :: IO ()
main = MWC.withSystemRandom (MWC.asGenST (unSample (uniform 0 1) 1)) >>= print
