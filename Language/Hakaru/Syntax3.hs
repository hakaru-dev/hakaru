{-# LANGUAGE MultiParamTypeClasses, TypeFamilies,
             FlexibleContexts, FlexibleInstances, DefaultSignatures,
             StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# OPTIONS -W #-}

module Language.Hakaru.Syntax3 where

import Prelude hiding (Real)
import Data.Ratio
import qualified Data.Number.LogFloat as LF
import qualified System.Random.MWC as MWC
import qualified System.Random.MWC.Distributions as MWCD
import qualified Numeric.Integration.TanhSinh as TS
import Control.Monad.Primitive (PrimState, PrimMonad)
import Numeric.SpecFunctions (logBeta)

-- A small probabilistic language with conditioning

infixl 1 `bind`, `bind_`
infixl 9 `app`

data Real
data Prob -- meaning: non-negative real number
data Measure a

class Order repr a where
  less :: repr a -> repr a -> repr Bool

class (Order repr Real, Floating (repr Real),
       Order repr Prob, Fractional (repr Prob)) => Base repr where
  unit       :: repr ()
  pair       :: repr a -> repr b -> repr (a,b)
  unpair     :: repr (a,b) -> (repr a -> repr b -> repr c) -> repr c
  inl        :: repr a -> repr (Either a b)
  inr        :: repr b -> repr (Either a b)
  uneither   :: repr (Either a b) -> (repr a -> repr c) ->
                                     (repr b -> repr c) -> repr c

  true, false :: repr Bool
  if_ :: repr Bool -> repr c -> repr c -> repr c

  unsafeProb :: repr Real -> repr Prob
  fromProb   :: repr Prob -> repr Real

  pi_      :: repr Prob
  pi_      =  unsafeProb pi
  exp_     :: repr Real -> repr Prob
  exp_     =  unsafeProb . exp
  log_     :: repr Prob -> repr Real
  log_     =  log . fromProb
  sqrt_    :: repr Prob -> repr Prob
  sqrt_ x  =  pow_ x (1/2)
  pow_     :: repr Prob -> repr Real -> repr Prob
  pow_ x y =  exp_ (log_ x * y)

  betaFunc         ::                     repr Real -> repr Real -> repr Prob
  default betaFunc :: (Integrate repr) => repr Real -> repr Real -> repr Prob
  betaFunc a b = integrate 0 1 $ \x ->
    pow_ (unsafeProb x) (a-1) * pow_ (unsafeProb (1-x)) (b-1)

fst_ :: (Base repr) => repr (a,b) -> repr a
fst_ ab = unpair ab (\a _ -> a)

snd_ :: (Base repr) => repr (a,b) -> repr b
snd_ ab = unpair ab (\_ b -> b)

and_ :: (Base repr) => [repr Bool] -> repr Bool
and_ []     = true
and_ [b]    = b
and_ (b:bs) = if_ b (and_ bs) false

class (Base repr) => Mochastic repr where
  dirac        :: repr a -> repr (Measure a)
  bind         :: repr (Measure a) -> (repr a -> repr (Measure b)) ->
                  repr (Measure b)
  lebesgue     :: repr (Measure Real)
  factor       :: repr Prob -> repr (Measure ())

  uniform      :: repr Real -> repr Real -> repr (Measure Real)
  uniform lo hi = lebesgue `bind` \x ->
                  factor (if_ (and_ [less lo x, less x hi])
                              (unsafeProb (recip (hi - lo)))
                              0) `bind_`
                  dirac x
  normal       :: repr Real -> repr Prob -> repr (Measure Real)
  normal mu sd = lebesgue `bind` \x -> factor (
        (1 / (sd * sqrt_ (2 * pi_))) *
        exp_ (- (x - mu) * (x - mu) / (fromProb (2 * sd * sd))) ) `bind_`
        dirac x

bind_ :: (Mochastic repr) => repr (Measure a) -> repr (Measure b) ->
                             repr (Measure b)
m `bind_` n = m `bind` \_ -> n

liftM :: (Mochastic repr) => (repr a -> repr b) ->
                             repr (Measure a) -> repr (Measure b)
liftM f m = m `bind` dirac . f

beta :: (Mochastic repr) => repr Real -> repr Real -> repr (Measure Real)
beta a b = uniform 0 1 `bind` \x ->
           factor (pow_ (unsafeProb x    ) (a-1) *
                   pow_ (unsafeProb (1-x)) (b-1) / betaFunc a b) `bind_`
           dirac x

bern :: (Mochastic repr) => repr Real -> repr (Measure Bool)
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
  integrate :: repr Real -> repr Real -> (repr Real -> repr Prob) -> repr Prob
  infinity, negativeInfinity :: repr Real

class Lambda repr where
  lam :: (repr a -> repr b) -> repr (a -> b)
  app :: repr (a -> b) -> repr a -> repr b

-- Importance sampling interpretation

newtype Sample m a = Sample { unSample :: Sample' m a }
type family Sample' (m :: * -> *) (a :: *)
type instance Sample' m Real         = Double
type instance Sample' m Prob         = LF.LogFloat
type instance Sample' m Bool         = Bool
type instance Sample' m ()           = ()
type instance Sample' m (a, b)       = (Sample' m a, Sample' m b)
type instance Sample' m (Either a b) = Either (Sample' m a) (Sample' m b)
type instance Sample' m (Measure a)  = LF.LogFloat -> MWC.Gen (PrimState m) ->
                                       m (Sample' m a, LF.LogFloat)
type instance Sample' m (a -> b)     = Sample' m a -> Sample' m b

instance Order (Sample m) Real where
  less (Sample a) (Sample b) = Sample $ a < b

deriving instance Eq         (Sample m Real)
deriving instance Ord        (Sample m Real)
deriving instance Num        (Sample m Real)
deriving instance Fractional (Sample m Real)
deriving instance Floating   (Sample m Real)

instance Order (Sample m) Prob where
  less (Sample a) (Sample b) = Sample $ a < b

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
  true                            = Sample True
  false                           = Sample False
  if_ c a b                       = Sample (if unSample c then unSample a else unSample b)
  unsafeProb (Sample x)           = Sample (LF.logFloat x)
  fromProb (Sample x)             = Sample (LF.fromLogFloat x)
  exp_ (Sample x)                 = Sample (LF.logToLogFloat x)
  log_ (Sample x)                 = Sample (LF.logFromLogFloat x)
  betaFunc (Sample a) (Sample b)  = Sample (LF.logToLogFloat (logBeta a b))

instance (PrimMonad m) => Mochastic (Sample m) where
  dirac (Sample a)                = Sample (\p _ -> return (a,p))
  bind (Sample m) k               = Sample (\p g -> do
                                      (a,p') <- m p g
                                      (unSample (k (Sample a)) $! p') g)
  lebesgue                        = Sample (\p g -> do
                                      (u,b) <- MWC.uniform g
                                      let l = log u; n = negate l
                                      return (if b then n else l,
                                              p * LF.logToLogFloat n))
  factor (Sample q)               = Sample (\p _ -> return ((), p * q))
  uniform (Sample lo) (Sample hi) = Sample (\p g -> do
                                      x <- MWC.uniformR (lo, hi) g
                                      return (x, p))
  normal (Sample mu) (Sample sd) = Sample (\p g -> do
                                      x <- MWCD.normal mu (LF.fromLogFloat sd) g
                                      return (x, p) )

instance Integrate (Sample m) where -- just for kicks -- imprecise
  integrate (Sample lo) (Sample hi)
    | not (isInfinite lo) && not (isInfinite hi)
    = int (\f -> TS.parTrap f lo hi)
    | isInfinite lo && lo < 0 && isInfinite hi && 0 < hi
    = int (TS.everywhere TS.parTrap)
    | not (isInfinite lo) && isInfinite hi && 0 < hi
    = int (\f -> TS.nonNegative TS.parTrap (f . (lo+)))
    | isInfinite lo && lo < 0 && not (isInfinite hi)
    = int (\f -> TS.nonNegative TS.parTrap (f . (hi-)))
    | otherwise
    = error ("Cannot integrate from " ++ show lo ++ " to " ++ show hi)
    where int method f = Sample $ LF.logFloat $ TS.result $ last
                       $ method $ LF.fromLogFloat . unSample . f . Sample
  infinity         = Sample LF.infinity
  negativeInfinity = Sample LF.negativeInfinity

instance Lambda (Sample m) where
  lam f = Sample (unSample . f . Sample)
  app (Sample rator) (Sample rand) = Sample (rator rand)

-- Expectation interpretation

newtype Expect repr a = Expect { unExpect :: repr (Expect' a) }
type family Expect' (a :: *)
type instance Expect' Real         = Real
type instance Expect' Prob         = Prob
type instance Expect' Bool         = Bool
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
  unit                           = Expect unit
  pair (Expect a) (Expect b)     = Expect (pair a b)
  unpair (Expect ab) k           = Expect (unpair ab (\a b ->
                                   unExpect (k (Expect a) (Expect b))))
  inl (Expect a)                 = Expect (inl a)
  inr (Expect b)                 = Expect (inr b)
  uneither (Expect ab) ka kb     = Expect (uneither ab (unExpect . ka . Expect)
                                                       (unExpect . kb . Expect))
  unsafeProb                     = Expect . unsafeProb . unExpect
  fromProb                       = Expect . fromProb   . unExpect
  true                           = Expect true
  false                          = Expect false
  if_ c a b                      = Expect (if_ (unExpect c) (unExpect a) (unExpect b))
  pi_                            = Expect pi_
  exp_                           = Expect . exp_  . unExpect
  log_                           = Expect . log_  . unExpect
  sqrt_                          = Expect . sqrt_ . unExpect
  pow_ (Expect x) (Expect y)     = Expect (pow_ x y)
  betaFunc (Expect a) (Expect b) = Expect (betaFunc a b)

instance (Integrate repr) => Integrate (Expect repr) where
  integrate (Expect lo) (Expect hi) f =
    Expect (integrate lo hi (unExpect . f . Expect))
  infinity         = Expect infinity
  negativeInfinity = Expect negativeInfinity

instance (Integrate repr, Lambda repr) => Mochastic (Expect repr) where
  dirac (Expect a)  = Expect (lam (\c -> c `app` a))
  bind (Expect m) k = Expect (lam (\c -> m `app` lam (\a ->
                      unExpect (k (Expect a)) `app` c)))
  lebesgue          = Expect (lam (integrate negativeInfinity infinity . app))
  factor (Expect q) = Expect (lam (\c -> q * c `app` unit))
  uniform (Expect lo) (Expect hi) = Expect (lam (\f ->
    integrate lo hi (\x -> app f x / unsafeProb (hi - lo))))

instance (Lambda repr) => Lambda (Expect repr) where
  lam f = Expect (lam (unExpect . f . Expect))
  app (Expect rator) (Expect rand) = Expect (app rator rand)

-- Maple printing interpretation

newtype Maple a = Maple { unMaple :: Int -> String }

mapleFun1 :: String -> Maple a -> Maple b
mapleFun1 fn (Maple x) = Maple (\i -> fn ++ "(" ++ x i ++ ")")

mapleFun2 :: String -> Maple a -> Maple b -> Maple c
mapleFun2 fn (Maple x) (Maple y) = Maple (\i -> fn ++ "(" ++ x i ++ ", " ++ y i ++ ")")

mapleOp2 :: String -> Maple a -> Maple b -> Maple c
mapleOp2 fn (Maple x) (Maple y) = Maple (\i -> "(" ++ x i ++ fn ++ y i ++ ")")

mapleBind :: (Maple a -> Maple b) -> Int -> (String, String)
mapleBind f i = (x, unMaple (f (Maple (\_ -> x))) (i + 1))
  where x = "x" ++ show i

instance Order Maple a where
  less = mapleOp2 "<"

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
  unit = Maple (\_ -> "Unit")
  pair = mapleFun2 "Pair"
  unpair (Maple ab) k = k (Maple (\i -> "op(1, " ++ ab i ++ ")"))
                          (Maple (\i -> "op(2, " ++ ab i ++ ")"))
  inl (Maple a) = Maple (\i -> "Left("  ++ a i ++ ")")
  inr (Maple b) = Maple (\i -> "Right(" ++ b i ++ ")")
  uneither (Maple ab) ka kb = Maple (\i ->
    let continue :: (Maple ab -> Maple c) -> String
        continue k = unMaple (k (Maple (const (ab i ++ ")")))) i
    in "`if`( op(0, " ++ ab i ++ ") = Left," ++ continue ka ++
          "`if`( op(0, " ++ ab i ++ ") = Right," ++ continue kb ++
                                  ", error \"expected Either but got something else\"))")
  unsafeProb (Maple x) = Maple x
  fromProb   (Maple x) = Maple x
  true = Maple (\_ -> "true")
  false = Maple (\_ -> "false")
  if_ (Maple c) (Maple a) (Maple b) = Maple (\i ->
    "piecewise(" ++ c i ++ ", " ++ a i ++ ", " ++ b i ++ ")")
  sqrt_ = mapleFun1 "sqrt"
  pow_ = mapleOp2 "^"
  betaFunc (Maple a) (Maple b) = Maple (\i -> "Beta(" ++ a i ++
                                                  "," ++ b i ++ ")")

instance Integrate Maple where
  integrate (Maple lo) (Maple hi) f = Maple (\i ->
    let (x, body) = mapleBind f i
    in "int(" ++ body ++ "," ++ x ++ "=" ++ lo i ++ ".." ++ hi i ++ ")")
  infinity         = Maple (\_ ->  "infinity")
  negativeInfinity = Maple (\_ -> "-infinity")

instance Lambda Maple where
  lam f = Maple (\i -> let (x, body) = mapleBind f i
                       in "(" ++ x ++ "->" ++ body ++ ")")
  app (Maple rator) (Maple rand) = Maple (\i -> rator i ++ "(" ++ rand i ++ ")")

-------------------------------------------------------------------------
-- Tests.  These should all be moved elsewhere!

-- In Maple, should 'evaluate' to "\c -> 1/2*c(Unit)"
t1 :: (Mochastic repr) => repr (Measure ())
t1 = uniform 0 1 `bind` \x -> factor (unsafeProb x)

t2 :: Mochastic repr => repr (Measure Real)
t2 = beta 1 1
t3 :: Mochastic repr => repr (Measure Real)
t3 = normal 0 10
t4 :: Mochastic repr => repr (Measure (Real, Bool))
t4 = beta 1 1 `bind` \bias -> bern bias `bind` \coin -> dirac (pair bias coin)
-- t5 is "the same" as t1.
t5 :: Mochastic repr => repr (Measure ())
t5 = factor (1/2) `bind_` dirac unit
t6 :: Mochastic repr => repr (Measure Real)
t6 = dirac 5
t7 :: Mochastic repr => repr (Measure Real)
t7 = uniform 0 1 `bind` \x -> factor (unsafeProb (x+1)) `bind_` dirac (x*x)
t8 :: Mochastic repr => repr (Measure (Real, Real))
t8 = normal 0 10 `bind` \x -> normal 5 20 `bind` \y -> dirac (pair x y)
t9 :: Mochastic repr => repr (Measure Real)
t9 = lebesgue `bind` \x -> factor (if_ (and_ [less 3 x, less x 7]) (1/2) 0) `bind_` dirac x

tester :: Expect Maple a -> String
tester t = unMaple (unExpect t) 0

-- this can sometimes be more convenient
tester2 :: (Expect' c ~ (b -> a)) => Maple b -> Expect Maple c -> String
tester2 c t = unMaple ((unExpect t) `app` c) 0

p1 :: String
p1 = tester2 (Maple (\_ -> "c")) t1
