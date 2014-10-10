{-# LANGUAGE MultiParamTypeClasses, TypeFamilies,
             FlexibleContexts, FlexibleInstances, DefaultSignatures,
             StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# OPTIONS -W -fno-warn-type-defaults #-}

module Language.Hakaru.Syntax where

import Prelude hiding (Real)
import Data.Ratio
import qualified Data.Number.LogFloat as LF
import qualified System.Random.MWC as MWC
import qualified System.Random.MWC.Distributions as MWCD
import qualified Numeric.Integration.TanhSinh as TS
import Control.Monad (liftM2)
import Control.Monad.Primitive (PrimState, PrimMonad)
import Control.Monad.Trans.Reader (ReaderT(ReaderT), runReaderT)
import Control.Monad.Trans.Cont (Cont, cont, runCont)
import Numeric.SpecFunctions (logBeta)

-- A small probabilistic language with conditioning

infixl 1 `bind`, `bind_`
infixl 9 `app`

data Real
data Prob -- meaning: non-negative real number
data Measure a

class Order repr a where
  less :: repr a -> repr a -> repr Bool

class (Num a, Num b) => Normalize a b where
  normalize :: [a] -> (a, b, [b])
  --  normalize xs == (x, y, ys)
  --  ===>  all (0 <=) ys && sum ys == y && xs == map (x *) ys
  --                               (therefore sum xs == x * y)

instance Normalize Double Double where
  normalize xs = (1, sum xs, xs)

instance Normalize LF.LogFloat Double where
  normalize []  = (0, 0, [])
  normalize [x] = (x, 1, [1])
  normalize xs  = (m, y, ys)
    where m  = maximum xs
          ys = [ LF.fromLogFloat (x/m) | x <- xs ]
          y  = sum ys

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
  dirac         :: repr a -> repr (Measure a)
  bind          :: repr (Measure a) -> (repr a -> repr (Measure b)) ->
                   repr (Measure b)
  lebesgue      :: repr (Measure Real)
  superpose     :: [(repr Prob, repr (Measure a))] -> repr (Measure a)

  uniform       :: repr Real -> repr Real -> repr (Measure Real)
  uniform lo hi =  lebesgue `bind` \x ->
                   if_ (and_ [less lo x, less x hi])
                       (superpose [(recip (unsafeProb (hi - lo)), dirac x)])
                       (superpose [])
  normal        :: repr Real -> repr Prob -> repr (Measure Real)
  normal mu sd  =  lebesgue `bind` \x ->
                   superpose [( exp_ (- (x - mu)^2 / fromProb (2 * pow_ sd 2))
                                 / sd / sqrt_ (2 * pi_)
                              , dirac x )]
  factor        :: repr Prob -> repr (Measure ())
  factor p      =  superpose [(p, dirac unit)]
  mix           :: [(repr Prob, repr (Measure a))] -> repr (Measure a)
  mix pms       =  let total = sum (map fst pms)
                   in superpose [ (p/total, m) | (p,m) <- pms ]

bind_ :: (Mochastic repr) => repr (Measure a) -> repr (Measure b) ->
                             repr (Measure b)
m `bind_` n = m `bind` \_ -> n

liftM :: (Mochastic repr) => (repr a -> repr b) ->
                             repr (Measure a) -> repr (Measure b)
liftM f m = m `bind` dirac . f

beta :: (Mochastic repr) => repr Real -> repr Real -> repr (Measure Prob)
beta a b = uniform 0 1 `bind` \x ->
           superpose [( pow_ (unsafeProb x    ) (a-1) *
                        pow_ (unsafeProb (1-x)) (b-1) / betaFunc a b
                      , dirac (unsafeProb x) )]

bern :: (Mochastic repr) => repr Prob -> repr (Measure Bool)
bern p = superpose [(p, dirac true), (1-p, dirac false)]

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
                                       m (Maybe (Sample' m a, LF.LogFloat))
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
  if_ (Sample c) a b              = if c then a else b
  unsafeProb (Sample x)           = Sample (LF.logFloat x)
  fromProb (Sample x)             = Sample (LF.fromLogFloat x)
  exp_ (Sample x)                 = Sample (LF.logToLogFloat x)
  log_ (Sample x)                 = Sample (LF.logFromLogFloat x)
  betaFunc (Sample a) (Sample b)  = Sample (LF.logToLogFloat (logBeta a b))

instance (PrimMonad m) => Mochastic (Sample m) where
  dirac (Sample a) = Sample (\p _ ->
    return (Just (a,p)))
  bind (Sample m) k = Sample (\p g -> do
    ap' <- m p g
    case ap' of
      Nothing     -> return Nothing
      Just (a,p') -> (unSample (k (Sample a)) $! p') g)
  lebesgue = Sample (\p g -> do
    (u,b) <- MWC.uniform g
    let l = log u
        n = negate l
    return (Just (if b then n else l,
                  p * 2 * LF.logToLogFloat n)))
  superpose [] = Sample (\_ _ -> return Nothing)
  superpose [(Sample q, Sample m)] = Sample (\p g -> (m $! p * q) g)
  superpose pms@((_, Sample m) : _) = Sample (\p g -> do
    let (x,y,ys) = normalize (map (unSample . fst) pms)
    if y <= (0::Double) then return Nothing else do
      u <- MWC.uniformR (0, y) g
      case [ m | (v,(_,m)) <- zip (scanl1 (+) ys) pms, u <= v ]
        of Sample m : _ -> (m $! p * x) g
           []           -> (m $! p * x) g)
  uniform (Sample lo) (Sample hi) = Sample (\p g -> do
    x <- MWC.uniformR (lo, hi) g
    return (Just (x, p)))
  normal (Sample mu) (Sample sd) = Sample (\p g -> do
    x <- MWCD.normal mu (LF.fromLogFloat sd) g
    return (Just (x, p)))
  mix [] = Sample (\_ _ -> return Nothing)
  mix [(_, m)] = m
  mix pms@((_, Sample m) : _) = Sample (\p g -> do
    let (_,y,ys) = normalize (map (unSample . fst) pms)
    if y <= (0::Double) then return Nothing else do
      u <- MWC.uniformR (0, y) g
      case [ m | (v,(_,m)) <- zip (scanl1 (+) ys) pms, u <= v ]
        of Sample m : _ -> (m $! p) g
           []           -> (m $! p) g)

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
  if_ (Expect c) a b             = Expect (if_ c (unExpect a) (unExpect b))
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
  superpose pms     = Expect (lam (\c -> sum [ p * app m c
                                             | (Expect p, Expect m) <- pms ]))
  uniform (Expect lo) (Expect hi) = Expect (lam (\f ->
    integrate lo hi (\x -> app f x / unsafeProb (hi - lo))))

instance (Lambda repr) => Lambda (Expect repr) where
  lam f = Expect (lam (unExpect . f . Expect))
  app (Expect rator) (Expect rand) = Expect (app rator rand)

-- Maple printing interpretation

newtype Maple a = Maple { unMaple :: ReaderT Int (Cont String) String }

-- "piecewise" in Maple only works when the expression has numeric type.
-- So "runMaple" should only be used when the expression has numeric type.
runMaple :: Maple a -> Int -> String
runMaple (Maple x) i = runCont (runReaderT x i) id

mapleFun1 :: String -> Maple a -> Maple b
mapleFun1 fn (Maple x) = Maple (fmap (\y -> fn ++ "(" ++ y ++ ")") x)

mapleFun2 :: String -> Maple a -> Maple b -> Maple c
mapleFun2 fn (Maple x) (Maple y) = Maple (liftM2 (\w z -> fn ++ "(" ++ w ++ ", " ++ z ++ ")") x y)

mapleOp2 :: String -> Maple a -> Maple b -> Maple c
mapleOp2 fn (Maple x) (Maple y) = Maple (liftM2 (\w z -> "(" ++ w ++ fn ++ z ++ ")") x y)

mapleBind :: (Maple a -> Maple b) -> Int -> (String, String)
mapleBind f i = (x, runMaple (f (Maple (return x))) (i + 1))
  where x = "x" ++ show i

instance Order Maple a where
  less = mapleOp2 "<"

instance Num (Maple a) where
  (+)              = mapleOp2 "+"
  (*)              = mapleOp2 "*"
  (-)              = mapleOp2 "-"
  negate (Maple x) = Maple (fmap (\u -> "(-" ++ u ++ ")") x)
  abs              = mapleFun1 "abs"
  signum           = mapleFun1 "signum"
  fromInteger x    = Maple (return (show x))

instance Fractional (Maple a) where
  (/)            = mapleOp2 "/"
  fromRational x = Maple (return ("(" ++ show (numerator   x) ++
                                  "/" ++ show (denominator x) ++ ")"))

instance Floating (Maple a) where
  pi                          = Maple (return "Pi")
  exp                         = mapleFun1 "exp"
  sqrt                        = mapleFun1 "sqrt"
  log                         = mapleFun1 "log"
  (**)                        = mapleOp2 "^"
  logBase (Maple b) (Maple y) = Maple (liftM2 (\b' y' -> "log[" ++ b' ++ "]"
                                                         ++ "(" ++ y' ++ ")") b y)
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
  unit = Maple (return "Unit")
  pair = mapleFun2 "Pair"
  unpair (Maple ab) k = Maple (ab >>= \ab' ->
    let opab n = "op(" ++ show n ++ ", " ++ ab' ++ ")" in
    unMaple (k (Maple (return (opab 1))) (Maple (return (opab 2)))))
  inl (Maple a) = Maple (fmap (\a' -> "Left("  ++ a' ++ ")") a)
  inr (Maple b) = Maple (fmap (\b' -> "Right(" ++ b' ++ ")") b)
  uneither (Maple ab) ka kb = Maple (ab >>= \ab' ->
    ReaderT $ \i -> cont $ \c ->
    let opab n = "op(" ++ show n ++ ", " ++ ab' ++ ")" in
    let arm tag k = opab 0 ++ " = " ++ tag ++ ", " ++
                    runCont (runReaderT (k (return (opab 1))) i) c in
    "piecewise(" ++ arm "Left"  (unMaple . ka . Maple)
         ++ ", " ++ arm "Right" (unMaple . kb . Maple) ++ ")")
  unsafeProb (Maple x) = Maple x
  fromProb   (Maple x) = Maple x
  true  = Maple (return "true" )
  false = Maple (return "false")
  if_ (Maple cond) (Maple a) (Maple b) = Maple (cond >>= \cond' ->
    ReaderT $ \i -> cont $ \c ->
    "piecewise(" ++ cond' ++ ", " ++ runCont (runReaderT a i) c
                          ++ ", " ++ runCont (runReaderT b i) c ++ ")")
  sqrt_ = mapleFun1 "sqrt"
  pow_ = mapleOp2 "^"
  betaFunc = mapleFun2 "Beta"

instance Integrate Maple where
  integrate (Maple lo) (Maple hi) f = Maple (lo >>= \lo' -> hi >>= \hi' ->
    ReaderT $ \i -> return $
    let (x, body) = mapleBind f i
    in "int(" ++ body ++ "," ++ x ++ "=" ++ lo' ++ ".." ++ hi' ++ ")")
  infinity         = Maple (return  "infinity")
  negativeInfinity = Maple (return "-infinity")

instance Lambda Maple where
  lam f = Maple (ReaderT $ \i -> return $
    let (x, body) = mapleBind f i in "(" ++ x ++ "->" ++ body ++ ")")
  app (Maple rator) (Maple rand) =
    Maple (liftM2 (\rator' rand' -> rator' ++ "(" ++ rand' ++ ")") rator rand)

