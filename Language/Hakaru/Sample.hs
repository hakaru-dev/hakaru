{-# LANGUAGE CPP
           , GADTs
           , KindSignatures
           , TypeOperators
           , TypeFamilies
           , DataKinds
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}

module Language.Hakaru.Sample where

import Control.Monad.Primitive                   (PrimState, PrimMonad)
import Numeric.SpecFunctions                     (logGamma, logBeta, logFactorial)
import qualified Data.Number.LogFloat            as LF
--import qualified Numeric.Integration.TanhSinh    as TS
import qualified System.Random.MWC               as MWC
import qualified System.Random.MWC.Distributions as MWCD
import qualified Data.Vector                     as V
import Data.Maybe                                (fromMaybe)
#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..), (<$>))
#endif
import Control.Monad.State
--import Control.Monad.Trans.Maybe

import qualified Data.Text        as T
import qualified Data.IntMap      as IM

import Language.Hakaru.Syntax.Nat      (fromNat, unsafeNat, Nat())
import Language.Hakaru.Syntax.Coercion
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.HClasses
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT

type PRNG m = MWC.Gen (PrimState m)

type family   Sample (a :: Hakaru) :: *
type instance Sample 'HNat          = Nat
type instance Sample 'HInt          = Int 
type instance Sample 'HReal         = Double 
type instance Sample 'HProb         = LF.LogFloat

type instance Sample (HPair a b)    = (Sample a, Sample b)

type instance Sample ('HMeasure a)  = Sample a
type instance Sample (a ':-> b)     = Sample a -> Sample b
type instance Sample ('HArray a)    = V.Vector (Sample a)

---------------------------------------------------------------

data EAssoc where
     EAssoc :: {-# UNPACK #-} !(Variable a) -> !(Sample a) -> EAssoc

newtype Env = Env (IM.IntMap EAssoc)

emptyEnv :: Env
emptyEnv = Env IM.empty

newtype SamplerMonad a =
    SM { unSM :: Env -> Either T.Text a }

runSM :: SamplerMonad a -> Either T.Text a 
runSM m = unSM m emptyEnv

instance Functor SamplerMonad where
    fmap f m = SM $ fmap f . unSM m

instance Applicative SamplerMonad where
    pure      = SM . const . Right
    mf <*> mx = mf >>= \f -> fmap f mx

instance Monad SamplerMonad where
    return   = pure
    mx >>= k = SM $ \env -> unSM mx env >>= \x -> unSM (k x) env

extendEnv :: EAssoc -> SamplerMonad a -> SamplerMonad a
extendEnv x (SM m) =
    SM $ \env -> m $ updateEnv x env

getEnv :: SamplerMonad Env
getEnv = SM Right

failwith :: T.Text -> SamplerMonad a
failwith = SM . const . Left

updateEnv :: EAssoc -> Env -> Env
updateEnv v@(EAssoc x _) (Env xs) =
    Env $ IM.insert (fromNat $ varID x) v xs

lookupVar :: Variable a -> Env -> Maybe (Sample a)
lookupVar x (Env env) = do
  EAssoc x' e' <- IM.lookup (fromNat $ varID x) env
  Refl         <- varEq x x'
  return e'

---------------------------------------------------------------

one :: LF.LogFloat
one = LF.logFloat (1.0 :: Double)

-- Makes use of Atkinson's algorithm as described in:
-- Monte Carlo Statistical Methods pg. 55
--
-- Further discussion at:
-- http://www.johndcook.com/blog/2010/06/14/generating-poisson-random-values/
poisson_rng :: (Functor m, PrimMonad m) => Double -> PRNG m -> m Int
poisson_rng lambda g' = make_poisson g'
    where
    smu   = sqrt lambda
    b     = 0.931 + 2.53*smu
    a     = -0.059 + 0.02483*b
    vr    = 0.9277 - 3.6224/(b - 2)
    arep  = 1.1239 + 1.1368/(b - 3.4)
    lnlam = log lambda

    make_poisson :: (Functor m, PrimMonad m) => PRNG m -> m Int
    make_poisson g = do
        u <- MWC.uniformR (-0.5,0.5) g
        v <- MWC.uniformR (0,1) g
        let us = 0.5 - abs u
            k = floor $ (2*a / us + b)*u + lambda + 0.43
        case () of
            () | us >= 0.07 && v <= vr -> return k
            () | k < 0                 -> make_poisson g
            () | us <= 0.013 && v > us -> make_poisson g
            () | accept_region us v k  -> return k
            _                          -> make_poisson g

    accept_region :: Double -> Double -> Int -> Bool
    accept_region us v k =
        log (v * arep / (a/(us*us)+b))
        <=
        -lambda + fromIntegral k * lnlam - logFactorial k

normalizeVector :: V.Vector LF.LogFloat ->
                   (LF.LogFloat, Double, V.Vector Double)
normalizeVector xs = case V.length xs of
  0 -> (0, 0, V.empty)
  1 -> (V.unsafeHead xs, 1, V.singleton 1)
  _ -> let m  = V.maximum xs
           ys = V.map (\x -> LF.fromLogFloat (x/m)) xs
           y  = V.sum ys
       in (m, y, ys)

---------------------------------------------------------------

sample :: (ABT abt, PrimMonad m, Functor m) =>
          LC_ abt a -> PRNG m -> Env ->
          m (Sample a, LF.LogFloat, Env)
sample (LC_ e) g env =
  caseVarSyn e (sampleVar g env) $ \t ->
    case t of
      o :$ es  -> sampleScon o es g env
      Value_ v -> return (sampleValue v, one, env)

sampleScon :: (ABT abt, PrimMonad m, Functor m) =>
              SCon args a -> SArgs abt args ->
              PRNG m      -> Env ->
              m (Sample a, LF.LogFloat, Env)

sampleScon (CoerceTo_   c) (e1 :* End) g env = do
    (v, weight, env) <- sample (LC_ e1) g env
    return (sampleCoerce c v, weight, env)

sampleScon (UnsafeFrom_ c) (e1 :* End) g env = do
    (v, weight, env) <- sample (LC_ e1) g env
    return (sampleUnsafe c v, weight, env)

sampleScon (MeasureOp_  m) es g env = sampleMeasureOp m es g env

sampleScon MBind (e1 :* e2 :* End) g env = do
    return undefined

sampleCoerce :: Coercion a b -> Sample a -> Sample b
sampleCoerce CNil         a = a
sampleCoerce (CCons c cs) a = sampleCoerce cs (samplePrimCoerce c a)

sampleUnsafe :: Coercion a b -> Sample b -> Sample a
sampleUnsafe CNil         a = a
sampleUnsafe (CCons c cs) a = samplePrimUnsafe c (sampleUnsafe cs a)

samplePrimCoerce :: (PrimCoercion a b) -> Sample a -> Sample b
samplePrimCoerce (Signed HRing_Int ) a = fromNat a
samplePrimCoerce (Signed HRing_Real) a = LF.fromLogFloat a
samplePrimCoerce (Continuous HContinuous_Prob) a = LF.logFloat (fromNat a)
samplePrimCoerce (Continuous HContinuous_Real) a = fromIntegral a

samplePrimUnsafe :: (PrimCoercion a b) -> Sample b -> Sample a
samplePrimUnsafe (Signed HRing_Int ) a = unsafeNat a
samplePrimUnsafe (Signed HRing_Real) a = LF.logFloat a
samplePrimUnsafe (Continuous HContinuous_Prob) a =
    unsafeNat (floor (LF.fromLogFloat a :: Double))
samplePrimUnsafe (Continuous HContinuous_Real) a = floor a

sampleMeasureOp :: (ABT abt, PrimMonad m, Functor m,
                    typs ~ UnLCs args, args ~ LCs typs) =>
                   MeasureOp typs a -> SArgs abt args ->
                   PRNG m -> Env ->
                   m (Sample a, LF.LogFloat, Env)

sampleMeasureOp (Dirac _)   (e1 :* End)  g env =
  sample (LC_ e1) g env
  
sampleMeasureOp Lebesgue    End          g env = do
  (u,b) <- MWC.uniform g
  let l = log u
  let n = -l
  return (if b then n else l, 2 * LF.logToLogFloat n, env)

sampleMeasureOp Counting    End          g env = do
  let success = LF.logToLogFloat (-3 :: Double)
  let pow x y = LF.logToLogFloat (LF.logFromLogFloat x *
                                  (fromIntegral y :: Double))
  u <- MWCD.geometric0 (LF.fromLogFloat success) g
  b <- MWC.uniform g
  return (if b then -1-u else u, 2 / pow (1-success) u / success, env)

sampleMeasureOp Categorical (e1 :* End)  g env = do
  (v, weight, env) <- sample (LC_ e1) g env
  let (_,y,ys) = normalizeVector v
  if not (y > (0::Double)) then
      error "Categorical needs positive weights"
  else do
   u <- MWC.uniformR (0, y) g
   return ( unsafeNat $ fromMaybe 0 (V.findIndex (u <=)
                                     (V.scanl1' (+) ys))
          , weight
          , env
          )

sampleMeasureOp Uniform (e1 :* e2 :* End) g env = do
  (v1, w1, env) <- sample (LC_ e1) g env
  (v2, w2, env) <- sample (LC_ e2) g env
  x <- MWC.uniformR (v1, v2) g
  return (x, w1*w2, env)

sampleMeasureOp Normal  (e1 :* e2 :* End) g env = do
  (v1, w1, env) <- sample (LC_ e1) g env
  (v2, w2, env) <- sample (LC_ e2) g env
  x <- MWCD.normal v1 (LF.fromLogFloat v2) g
  return (x, w1*w2, env)

sampleMeasureOp Poisson (e1 :* End)       g env = do
  (v1, w1, env) <- sample (LC_ e1) g env
  x <- poisson_rng (LF.fromLogFloat v1) g
  return (unsafeNat x, w1, env)

sampleMeasureOp Gamma   (e1 :* e2 :* End) g env = do
  (v1, w1, env) <- sample (LC_ e1) g env
  (v2, w2, env) <- sample (LC_ e2) g env
  x <- MWCD.gamma (LF.fromLogFloat v1) (LF.fromLogFloat v2) g
  return (LF.logFloat x, w1*w2, env)

sampleMeasureOp Beta    (e1 :* e2 :* End) g env = do
  (v1, w1, env) <- sample (LC_ e1) g env
  (v2, w2, env) <- sample (LC_ e2) g env
  x <- MWCD.beta (LF.fromLogFloat v1) (LF.fromLogFloat v2) g
  return (LF.logFloat x, w1*w2, env)

sampleMeasureOp (DirichletProcess _)  _ g env =
    error "sampleMeasureOp: Dirichlet Processes not implemented yet"

sampleMeasureOp (Plate _)   (e1 :* End) g env = sample (LC_ e1) g env

-- Not sure if correct
sampleMeasureOp (Chain _ _) (e1 :* e2 :* End) g env = do
  (v, ps, env) <- sample (LC_ e1) g env
  (s, p,  env) <- sample (LC_ e2) g env
  let samples  = chain s (V.toList v)
  return ((V.fromList samples, s), p * ps, env)
 where chain s     [] = []
       chain s (f:fs) = let (a, s') = f s in
                        a : (chain s' fs)

sampleMeasureOp _ _ _ _ =
    error "sampleMeasureOP: the impossible happened"

sampleValue :: Value a -> Sample a
sampleValue (VNat  n)  = n
sampleValue (VInt  n)  = n
sampleValue (VProb n)  = n
sampleValue (VReal n)  = n
sampleValue (VDatum _) = error "Don't know how to sample Datum"

sampleVar :: (PrimMonad m, Functor m) =>
             PRNG m -> Env -> Variable a -> 
             m (Sample a, LF.LogFloat, Env)
sampleVar g env v = do
  case lookupVar v env of
    Nothing -> error "variable not found!"
    Just a  -> return (a, one, env)

runSample :: (ABT abt, Functor m, PrimMonad m) =>
             abt '[] a -> PRNG m -> m (Sample a, LF.LogFloat)
runSample prog g = do
  (v, weight, _) <- sample (LC_ prog) g emptyEnv
  return (v, weight)

