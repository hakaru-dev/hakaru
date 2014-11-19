{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances,
    TypeFamilies, StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# OPTIONS -W #-}

module Language.Hakaru.Sample (Sample(..), Sample') where

-- Importance sampling interpretation

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Real, Prob, Measure, errorEmpty,
       Order(..), Base(..), Mochastic(..), Integrate(..), Lambda(..))
import Language.Hakaru.Util.Extras (normalize)
import Control.Monad.Primitive (PrimState, PrimMonad)
import Numeric.SpecFunctions (logBeta, logGamma)
import qualified Data.Number.LogFloat as LF
import qualified Numeric.Integration.TanhSinh as TS
import qualified System.Random.MWC as MWC
import qualified System.Random.MWC.Distributions as MWCD

newtype Sample m a = Sample { unSample :: Sample' m a }
type family Sample' (m :: * -> *) (a :: *)
type instance Sample' m Real         = Double
type instance Sample' m Prob         = LF.LogFloat
type instance Sample' m ()           = ()
type instance Sample' m (a, b)       = (Sample' m a, Sample' m b)
type instance Sample' m (Either a b) = Either (Sample' m a) (Sample' m b)
type instance Sample' m (Measure a)  = LF.LogFloat -> MWC.Gen (PrimState m) ->
                                       m (Maybe (Sample' m a, LF.LogFloat))
type instance Sample' m (a -> b)     = Sample' m a -> Sample' m b

instance Order (Sample m) Real where
  less (Sample a) (Sample b) = Sample ((if a < b then Left else Right) ())

deriving instance Eq         (Sample m Real)
deriving instance Ord        (Sample m Real)
deriving instance Num        (Sample m Real)
deriving instance Fractional (Sample m Real)
deriving instance Floating   (Sample m Real)

instance Order (Sample m) Prob where
  less (Sample a) (Sample b) = Sample ((if a < b then Left else Right) ())

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
  exp_ (Sample x)                 = Sample (LF.logToLogFloat x)
  log_ (Sample x)                 = Sample (LF.logFromLogFloat x)
  betaFunc (Sample a) (Sample b)  = Sample (LF.logToLogFloat (logBeta a b))
  gammaFunc (Sample n)            = Sample (LF.logToLogFloat (logGamma n))

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
    return (Just (if b then n else l, p * 2 * LF.logToLogFloat n)))
  superpose [] = Sample (\_ _ -> return Nothing)
  superpose [(Sample q, Sample m)] = Sample (\p g -> (m $! p * q) g)
  superpose pms@((_, Sample m) : _) = Sample (\p g -> do
    let (x,y,ys) = normalize (map (unSample . fst) pms)
    if not (y > (0::Double)) then return Nothing else do
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
  mix [] = errorEmpty
  mix [(_, m)] = m
  mix pms@((_, Sample m) : _) = Sample (\p g -> do
    let (_,y,ys) = normalize (map (unSample . fst) pms)
    if not (y > (0::Double)) then errorEmpty else do
      u <- MWC.uniformR (0, y) g
      case [ m | (v,(_,m)) <- zip (scanl1 (+) ys) pms, u <= v ]
        of Sample m : _ -> (m $! p) g
           []           -> (m $! p) g)
  -- TODO: override poisson, gamma, invgamma to sample more efficiently

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
