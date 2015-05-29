{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances,
    TypeFamilies, StandaloneDeriving, GeneralizedNewtypeDeriving,
    GADTs, RankNTypes, InstanceSigs, DataKinds, TypeOperators, PolyKinds #-}

{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS -Wall #-}

module Language.Hakaru.Sample (Sample(..), Sample', runSample) where

-- Importance sampling interpretation

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Hakaru(..),
       Order(..), Base(..), Mochastic(..), Integrate(..), Lambda(..))
import Language.Hakaru.Util.Extras (normalize, normalizeVector)
import Language.Hakaru.Distribution (poisson_rng)
import Control.Monad.Primitive (PrimState, PrimMonad)
import Numeric.SpecFunctions (logGamma, logBeta)
import qualified Numeric.SpecFunctions as SF
import qualified Data.Number.LogFloat as LF
import qualified Numeric.Integration.TanhSinh as TS
import qualified System.Random.MWC as MWC
import qualified System.Random.MWC.Distributions as MWCD
import qualified Data.Vector as V
import Data.Maybe (fromMaybe)
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Language.Hakaru.Embed

newtype Sample (m :: Hakaru * -> *) (a :: Hakaru *) =
    Sample { unSample :: Sample' m a }
type family   Sample' (m :: Hakaru * -> *) (a :: Hakaru *) :: *
type instance Sample' m HInt          = Int 
type instance Sample' m HReal         = Double 
type instance Sample' m HProb         = LF.LogFloat 
type instance Sample' m HBool         = Bool 
type instance Sample' m HUnit         = () 
type instance Sample' m (HPair a b)   = (Sample' m a, Sample' m b)
type instance Sample' m (HEither a b) = Either (Sample' m a) (Sample' m b)
type instance Sample' m (HList a)     = [Sample' m a] 
-- BUG: need to coerce @m@ into @* -> *@ in order to pass it to 'PrimState'
type instance Sample' m (HMeasure a)  =
    LF.LogFloat -> MWC.Gen (PrimState m) ->
    m (HMaybe (HPair (Sample' m a) HProb))
type instance Sample' m (HFun a b)    = Sample' m a -> Sample' m b
type instance Sample' m (HArray a)    = V.Vector (Sample' m a)

instance Order (Sample m) HReal where
  less  (Sample a) (Sample b) = Sample (a <  b)
  equal (Sample a) (Sample b) = Sample (a == b)

deriving instance Eq         (Sample m HReal)
deriving instance Ord        (Sample m HReal)
deriving instance Num        (Sample m HReal)
deriving instance Fractional (Sample m HReal)
deriving instance Floating   (Sample m HReal)

instance Order (Sample m) HProb where
  less  (Sample a) (Sample b) = Sample (a <  b)
  equal (Sample a) (Sample b) = Sample (a == b)

deriving instance Eq         (Sample m HProb)
deriving instance Ord        (Sample m HProb)
deriving instance Num        (Sample m HProb)
deriving instance Fractional (Sample m HProb)

instance Order (Sample m) HInt where
  less  (Sample a) (Sample b) = Sample (a <  b)
  equal (Sample a) (Sample b) = Sample (a == b)

deriving instance Eq         (Sample m HInt)
deriving instance Ord        (Sample m HInt)
deriving instance Num        (Sample m HInt)

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
  vector (Sample l) f             = let g i = unSample (f (Sample i))
                                    in Sample (V.generate l g)
  empty                           = Sample V.empty
  index  (Sample v) (Sample i)    = Sample (v V.! i)
  size   (Sample v)               = Sample (V.length v)
  reduce f a (Sample v)           = V.foldl' (\acc b -> f acc (Sample b)) a v

-- BUG: need to coerce @m@ into @* -> *@ in order to pass it to 'PrimState'
instance (PrimMonad m) => Mochastic (Sample (m :: Hakaru * -> *)) where
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
        of Sample m2 : _ -> (m2 $! p * x * LF.logFloat y) g
           []            -> (m $! p * x * LF.logFloat y) g)
  uniform (Sample lo) (Sample hi) = Sample (\p g -> do
    x <- MWC.uniformR (lo, hi) g
    return (Just (x, p)))
  normal (Sample mu) (Sample sd) = Sample (\p g -> do
    x <- MWCD.normal mu (LF.fromLogFloat sd) g
    return (Just (x, p)))
  categorical (Sample v) = Sample (\p g -> do
    let (_,y,ys) = normalizeVector v
    if not (y > (0::Double)) then return Nothing else do
      u <- MWC.uniformR (0, y) g
      return (Just (fromMaybe 0 (V.findIndex (u <=) (V.scanl1' (+) ys)), p)))

  poisson (Sample l) = Sample (\p g -> do
    x <- poisson_rng (LF.fromLogFloat l) g
    return (Just (x, p)))
  gamma (Sample shape) (Sample scale) = Sample (\p g -> do
    x <- MWCD.gamma (LF.fromLogFloat shape) (LF.fromLogFloat scale) g
    return (Just (LF.logFloat x, p)))
  beta a b = gamma a 1 `bind` \x -> gamma b 1 `bind` \y -> dirac (x / (x + y))
  plate (Sample v) = Sample (\p g -> runMaybeT $ do
    samples <- V.mapM (\m -> MaybeT $ m 1 g) v
    let (v', ps) = V.unzip samples
    return (v', p * V.product ps))
  chain (Sample v) = Sample (\s p g -> runMaybeT $ do
    let convert f = StateT $ \s' -> do ((a,s''),p') <- MaybeT (f s' 1 g)
                                       return ((a,p'),s'')
    (samples, sout) <- runStateT (V.mapM convert v) s
    let (v', ps) = V.unzip samples
    return ((v', sout), p * V.product ps))

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


type instance Sample' m (HTag t xss) = NS (NP (Sample m)) xss
type instance Sample' m (HSOP xss)   = NS (NP (Sample m)) xss

instance Embed (Sample m) where
  _Nil = Sample (Z Nil)

  _Cons x (Sample (Z xs)) = Sample (Z (x :* xs))
  _Cons _ (Sample (S _ )) = error "type error"

  caseProd (Sample (Z (x :* xs))) f = Sample (unSample $ f x (Sample (Z xs)))
  caseProd (Sample (S _)) _ = error "type error"

  _Z (Sample (Z x)) = Sample (Z x)
  _Z (Sample (S _)) = error "type error"

  _S (Sample x) = Sample (S x)

  caseSum (Sample (Z x)) cS _  = cS (Sample (Z x))
  caseSum (Sample (S x)) _  cZ = cZ (Sample x)

  tag (Sample x) = Sample x
  untag (Sample x) = Sample x
                                   
runSample :: Sample IO (HMeasure a) -> IO (Maybe (Sample' IO a))
runSample m = do g <- MWC.createSystemRandom -- "This is a somewhat expensive function, and is intended to be called only occasionally (e.g. once per thread)."
                 s <- unSample m 1 g
                 return (fmap fst s)
