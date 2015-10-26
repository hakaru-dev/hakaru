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

newtype S (m :: * -> *) (a :: Hakaru) =
    S { unS :: Sample m a }

type family   Sample (m :: * -> *) (a :: Hakaru) :: *
type instance Sample m 'HNat          = Nat
type instance Sample m 'HInt          = Int 
type instance Sample m 'HReal         = Double 
type instance Sample m 'HProb         = LF.LogFloat

type instance Sample m (HPair a b)    = (Sample m a, Sample m b)

type instance Sample m ('HMeasure a)  =
    LF.LogFloat -> PRNG m ->
    m (Maybe (Sample m a, LF.LogFloat))
type instance Sample m (a ':-> b)     = Sample m a -> Sample m b
type instance Sample m ('HArray a)    = V.Vector (Sample m a)

----------------------------------------------------------------

data EAssoc m where
     EAssoc :: {-# UNPACK #-} !(Variable a) -> !(Sample m a) -> EAssoc m

newtype Env m = Env (IM.IntMap (EAssoc m))

emptyEnv :: Env m
emptyEnv = Env IM.empty

newtype SamplerMonad m a =
    SM { unSM :: Env m -> Either T.Text a }

runSM :: SamplerMonad m a -> Either T.Text a 
runSM m = unSM m emptyEnv

instance Functor (SamplerMonad m) where
    fmap f m = SM $ fmap f . unSM m

instance Applicative (SamplerMonad m) where
    pure      = SM . const . Right
    mf <*> mx = mf >>= \f -> fmap f mx

instance Monad (SamplerMonad m) where
    return   = pure
    mx >>= k = SM $ \env -> unSM mx env >>= \x -> unSM (k x) env

extendEnv :: EAssoc m -> SamplerMonad m a -> SamplerMonad m a
extendEnv x (SM m) =
    SM $ \env -> m $ updateEnv x env

getEnv :: SamplerMonad m (Env m)
getEnv = SM Right

failwith :: T.Text -> SamplerMonad m a
failwith = SM . const . Left

updateEnv :: EAssoc m -> Env m -> Env m
updateEnv v@(EAssoc x _) (Env xs) =
    Env $ IM.insert (fromNat $ varID x) v xs

lookupVar :: Variable a -> Env m -> Maybe (Sample m a)
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
          LC_ abt a -> PRNG m -> Env m -> (S m a, Env m)
sample (LC_ e) g env =
  caseVarSyn e (sampleVar g env) $ \t ->
    case t of
      o :$ es  -> sampleScon o es g env
      Value_ v -> (sampleValue v, env)

sampleScon :: (ABT abt, PrimMonad m, Functor m) =>
              SCon args a -> SArgs abt args ->
              PRNG m      -> Env m ->
              (S m a, Env m)

sampleScon (CoerceTo_   c) (e1 :* End) g env =
    let (v, env) = sample (LC_ e1) g env
    in  (sampleCoerce c v, env)

sampleScon (UnsafeFrom_ c) (e1 :* End) g env =
    let (v, env) = sample (LC_ e1) g env
    in  (sampleUnsafe c v, env)

sampleScon (MeasureOp_  m) es g env = sampleMeasureOp m es g env

sampleScon MBind (e1 :* e2 :* End) g env = undefined

sampleCoerce :: Coercion a b -> S m a -> S m b
sampleCoerce CNil         (S a) = S a
sampleCoerce (CCons c cs) (S a) = sampleCoerce cs (samplePrimCoerce c (S a))

sampleUnsafe :: Coercion a b -> S m b -> S m a
sampleUnsafe CNil         (S a) = S a
sampleUnsafe (CCons c cs) (S a) = samplePrimUnsafe c (sampleUnsafe cs (S a))

samplePrimCoerce :: (PrimCoercion a b) -> S m a -> S m b
samplePrimCoerce (Signed HRing_Int ) (S a) = S $ fromNat a
samplePrimCoerce (Signed HRing_Real) (S a) = S $ LF.fromLogFloat a
samplePrimCoerce (Continuous HContinuous_Prob) (S a) = S $ LF.logFloat (fromNat a)
samplePrimCoerce (Continuous HContinuous_Real) (S a) = S $ fromIntegral a

samplePrimUnsafe :: (PrimCoercion a b) -> S m b -> S m a
samplePrimUnsafe (Signed HRing_Int ) (S a) = S $ unsafeNat a
samplePrimUnsafe (Signed HRing_Real) (S a) = S $ LF.logFloat a
samplePrimUnsafe (Continuous HContinuous_Prob) (S a) =
    S $ unsafeNat $ floor (LF.fromLogFloat a :: Double)
samplePrimUnsafe (Continuous HContinuous_Real) (S a) = S $ floor a

sampleMeasureOp :: (ABT abt, PrimMonad m, Functor m,
                    typs ~ UnLCs args, args ~ LCs typs) =>
                   MeasureOp typs a -> SArgs abt args ->
                   PRNG m -> Env m -> (S m a, Env m)

sampleMeasureOp (Dirac _)   (e1 :* End) g env =
  let (S a, env') = sample (LC_ e1) g env
  in  (S (\p _ -> return $ Just (a, p)), env')

sampleMeasureOp Lebesgue    End         g env =
  (S (\p g -> do
        (u,b) <- MWC.uniform g
        let l = log u
        let n = -l
        return $ Just (if b then n
                       else l, 2 * LF.logToLogFloat n)), env)

sampleMeasureOp Counting    End          g env =
  (S (\p g -> do
        let success = LF.logToLogFloat (-3 :: Double)
        let pow x y = LF.logToLogFloat (LF.logFromLogFloat x *
                                        (fromIntegral y :: Double))
        u <- MWCD.geometric0 (LF.fromLogFloat success) g
        b <- MWC.uniform g
        return $ Just (if b then -1-u
                       else u, 2 / pow (1-success) u / success)), env)

sampleMeasureOp Categorical (e1 :* End)  g env =
  (S (\p g -> do
        let (S v, _) = sample (LC_ e1) g env
        let (_,y,ys) = normalizeVector v
        if not (y > (0::Double)) then
            error "Categorical needs positive weights"
        else do
          u <- MWC.uniformR (0, y) g
          return $ Just (unsafeNat $ fromMaybe 0 (V.findIndex (u <=)
                                                  (V.scanl1' (+) ys))
                        , p))
  , env
  )

sampleMeasureOp Uniform (e1 :* e2 :* End) g env =
  let (S v1, _) = sample (LC_ e1) g env
      (S v2, _) = sample (LC_ e2) g env
  in  (S (\ p g -> do
            x <- MWC.uniformR (v1, v2) g
            return $ Just (x, p)), env)

sampleMeasureOp Normal  (e1 :* e2 :* End) g env =
  let (S v1, _) = sample (LC_ e1) g env
      (S v2, _) = sample (LC_ e2) g env
  in  (S (\ p g -> do
            x <- MWCD.normal v1 (LF.fromLogFloat v2) g
            return $ (Just (x, p))), env)

sampleMeasureOp Poisson (e1 :* End)       g env =
  let (S v1, _) = sample (LC_ e1) g env
  in  (S (\ p g -> do
            x <- poisson_rng (LF.fromLogFloat v1) g
            return $ Just (unsafeNat x, p)), env)

sampleMeasureOp Gamma   (e1 :* e2 :* End) g env =
  let (S v1, _) = sample (LC_ e1) g env
      (S v2, _) = sample (LC_ e2) g env
  in  (S (\ p g -> do
            x <- MWCD.gamma (LF.fromLogFloat v1) (LF.fromLogFloat v2) g
            return $ Just (LF.logFloat x, p)), env)

sampleMeasureOp Beta    (e1 :* e2 :* End) g env =
  let (S v1, _) = sample (LC_ e1) g env
      (S v2, _) = sample (LC_ e2) g env
  in  (S (\ p g -> do
            x <- MWCD.beta (LF.fromLogFloat v1) (LF.fromLogFloat v2) g
            return $ Just (LF.logFloat x, p)), env)

sampleMeasureOp (DirichletProcess _)  _ g env =
    error "sampleMeasureOp: Dirichlet Processes not implemented yet"

sampleMeasureOp (Plate _)   (e1 :* End) g env =
    error "sampleMeasureOP: Plate not implemented yet"

-- Not sure if correct
sampleMeasureOp (Chain _ _) (e1 :* e2 :* End) g env =
    error "sampleMeasureOP: Chain not implemented yet"

sampleMeasureOp _ _ _ _ =
    error "sampleMeasureOP: the impossible happened"

sampleValue :: Value a -> S m a
sampleValue (VNat  n)  = S n
sampleValue (VInt  n)  = S n
sampleValue (VProb n)  = S n
sampleValue (VReal n)  = S n
sampleValue (VDatum _) = error "Don't know how to sample Datum"

sampleVar :: (PrimMonad m, Functor m) =>
             PRNG m -> Env m -> Variable a -> 
             (S m a, Env m)
sampleVar g env v = do
  case lookupVar v env of
    Nothing -> error "variable not found!"
    Just a  -> (S a, env)

runSample :: (ABT abt, Functor m, PrimMonad m) =>
             abt '[] a -> PRNG m -> S m a
runSample prog g =
  fst $ sample (LC_ prog) g emptyEnv

