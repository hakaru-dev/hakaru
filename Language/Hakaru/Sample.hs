{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances,
    TypeFamilies, StandaloneDeriving, GeneralizedNewtypeDeriving, 
    AllowAmbiguousTypes
    #-}
{-# OPTIONS -W #-}

module Language.Hakaru.Sample (Sample(..), Sample') where

-- Importance sampling interpretation

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Real, Prob, Measure, Vector, errorEmpty,
       Order(..), Base(..), Mochastic(..), Integrate(..), Lambda(..))
import Language.Hakaru.Util.Extras (normalize)
import Language.Hakaru.Distribution (poisson_rng)
import Control.Monad.Primitive (PrimState, PrimMonad)
import Numeric.SpecFunctions (logGamma, logBeta)
import qualified Numeric.SpecFunctions as SF
import qualified Data.Number.LogFloat as LF
import qualified Numeric.Integration.TanhSinh as TS
import qualified System.Random.MWC as MWC
import qualified System.Random.MWC.Distributions as MWCD
import qualified Data.Vector as V
import Data.Maybe (fromJust, isNothing)
import Control.Monad.State
import Control.Monad.Trans.Maybe    
import Language.Hakaru.Embed

newtype Sample m a = Sample { unSample :: Sample' m a }
type family Sample' (m :: * -> *) (a :: *)
type instance Sample' m Int          = Int
type instance Sample' m Real         = Double
type instance Sample' m Prob         = LF.LogFloat
type instance Sample' m Bool         = Bool
type instance Sample' m ()           = ()
type instance Sample' m (a, b)       = (Sample' m a, Sample' m b)
type instance Sample' m (Either a b) = Either (Sample' m a) (Sample' m b)
type instance Sample' m [a]          = [Sample' m a]
type instance Sample' m (Measure a)  = LF.LogFloat -> MWC.Gen (PrimState m) ->
                                       m (Maybe (Sample' m a, LF.LogFloat))
type instance Sample' m (a -> b)     = Sample' m a -> Sample' m b

data Vec a = Vec {low :: Int, high :: Int, vec :: V.Vector a}
type instance Sample' m (Vector a)   = Vec (Sample' m a)

instance Order (Sample m) Real where
  less  (Sample a) (Sample b) = Sample (a <  b)
  equal (Sample a) (Sample b) = Sample (a == b)

deriving instance Eq         (Sample m Real)
deriving instance Ord        (Sample m Real)
deriving instance Num        (Sample m Real)
deriving instance Fractional (Sample m Real)
deriving instance Floating   (Sample m Real)

instance Order (Sample m) Prob where
  less  (Sample a) (Sample b) = Sample (a <  b)
  equal (Sample a) (Sample b) = Sample (a == b)

deriving instance Eq         (Sample m Prob)
deriving instance Ord        (Sample m Prob)
deriving instance Num        (Sample m Prob)
deriving instance Fractional (Sample m Prob)

instance Order (Sample m) Int where
  less  (Sample a) (Sample b) = Sample (a <  b)
  equal (Sample a) (Sample b) = Sample (a == b)

deriving instance Eq         (Sample m Int)
deriving instance Ord        (Sample m Int)
deriving instance Num        (Sample m Int)

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
  if_ (Sample True) et _          = et
  if_ (Sample False) _ ef         = ef
  nil                             = Sample []
  cons (Sample a) (Sample as)     = Sample (a : as)
  unlist (Sample []) k _          = k
  unlist (Sample (a : as)) _ k    = k (Sample a) (Sample as)
  unsafeProb (Sample x)           = Sample (LF.logFloat x)
  fromProb (Sample x)             = Sample (LF.fromLogFloat x)
  fromInt (Sample x)              = Sample (fromIntegral x)
  exp_ (Sample x)                 = Sample (LF.logToLogFloat x)
  erf  (Sample x)                 = Sample (SF.erf x)
  log_ (Sample x)                 = Sample (LF.logFromLogFloat x)
  infinity                        = Sample LF.infinity
  negativeInfinity                = Sample LF.negativeInfinity
  gammaFunc (Sample n)            = Sample (LF.logToLogFloat (logGamma n))
  betaFunc (Sample a) (Sample b)  = Sample (LF.logToLogFloat (logBeta
                                       (LF.fromLogFloat a) (LF.fromLogFloat b)))
  vector (Sample lo) (Sample hi) f = let g i = unSample (f (Sample $ lo + i))
                                     in Sample (Vec lo hi (V.generate (hi-lo+1) g))
  index (Sample v) (Sample i) = if (i < low v || i > high v)
                                then error "index out of bounds"
                                else Sample $ vec v V.! (i - low v)
  loBound (Sample v)          = Sample (low v)
  hiBound (Sample v)          = Sample (high v)

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
        n = -l
    return (Just (if b then n else l, p * 2 * LF.logToLogFloat n)))
  counting = Sample (\p g -> do
    let success = LF.logToLogFloat (-3 :: Double)
    let pow x y = LF.logToLogFloat (LF.logFromLogFloat x *
                                    (fromIntegral y :: Double))
    u <- MWCD.geometric0 (LF.fromLogFloat success) g
    b <- MWC.uniform g
    return (Just (if b then -1-u else u, p * 2 / pow (1-success) u / success)))
  superpose [] = Sample (\_ _ -> return Nothing)
  superpose [(Sample q, Sample m)] = Sample (\p g -> (m $! p * q) g)
  superpose pms@((_, Sample m) : _) = Sample (\p g -> do
    let (x,y,ys) = normalize (map (unSample . fst) pms)
    if not (y > (0::Double)) then return Nothing else do
      u <- MWC.uniformR (0, y) g
      case [ m1 | (v,(_,m1)) <- zip (scanl1 (+) ys) pms, u <= v ]
        of Sample m2 : _ -> (m2 $! p * x) g
           []            -> (m $! p * x) g)
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
      case [ m1 | (v,(_,m1)) <- zip (scanl1 (+) ys) pms, u <= v ]
        of Sample m2 : _ -> (m2 $! p) g
           []            -> (m $! p) g)
  poisson (Sample l) = Sample (\p g -> do
    x <- poisson_rng (LF.fromLogFloat l) g
    return (Just (x, p)))
  gamma (Sample shape) (Sample scale) = Sample (\p g -> do
    x <- MWCD.gamma (LF.fromLogFloat shape) (LF.fromLogFloat scale) g
    return (Just (LF.logFloat x, p)))
  beta a b = gamma a 1 `bind` \x -> gamma b 1 `bind` \y -> dirac (x / (x + y))
  plate (Sample v) = Sample (\p g -> runMaybeT $ do
    samples <- V.mapM (\m -> MaybeT $ m 1 g) (vec v)
    let (v', ps) = V.unzip samples
    return (v{vec = v'}, p * V.product ps))
  chain (Sample v) = Sample (\s p g -> runMaybeT $ do
    let convert f = StateT $ \s -> do ((a,s'),p') <- MaybeT (f s 1 g)
                                      return ((a,p'),s')
    (samples, sout) <- runStateT (V.mapM convert (vec v)) s
    let (v', ps) = V.unzip samples
    return ((v{vec = v'}, sout), p * V.product ps))                                     
  
instance Integrate (Sample m) where -- just for kicks -- inaccurate
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
  summate (Sample lo) (Sample hi) f = integrate (Sample lo') (Sample hi') f'
    where lo' | isInfinite lo = lo
              | otherwise     = fromInteger (ceiling lo)
          hi' | isInfinite hi = hi
              | otherwise     = fromInteger (floor hi + 1)
          f' (Sample x) = f (Sample (fromInteger (floor x)))

instance Lambda (Sample m) where
  lam f = Sample (unSample . f . Sample)
  app (Sample rator) (Sample rand) = Sample (rator rand)


type instance Sample' m (HRep t) = NS (NP (Sample m)) (Code t)

instance Embed (Sample m) where 
  sop' _ x = Sample x 
  case' _ (Sample x) f = apNAry x f 
