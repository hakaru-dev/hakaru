{-# LANGUAGE CPP
           , GADTs
           , KindSignatures
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
--import qualified System.Random.MWC.Distributions as MWCD
--import qualified Data.Vector                     as V
--import Data.Maybe                                (fromMaybe)
#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..), (<$>))
#endif
--import Control.Monad.State
--import Control.Monad.Trans.Maybe

import qualified Data.Text        as T
import qualified Data.IntMap      as IM

import Language.Hakaru.Syntax.Nat      (fromNat, Nat())
import Language.Hakaru.Syntax.Coercion
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.HClasses
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT hiding (insertAssoc)

type PRNG m = MWC.Gen (PrimState m)

type family   Sample (a :: Hakaru) :: *
type instance Sample 'HNat          = Nat
type instance Sample 'HInt          = Int 
type instance Sample 'HReal         = Double 
type instance Sample 'HProb         = LF.LogFloat 

---------------------------------------------------------------
newtype SamplerMonad abt a =
    SM { unSM :: Assocs abt -> Either T.Text a }

runSM :: SamplerMonad abt a -> Either T.Text a 
runSM m = unSM m emptyAssocs

instance Functor (SamplerMonad abt) where
    fmap f m = SM $ fmap f . unSM m

instance Applicative (SamplerMonad abt) where
    pure      = SM . const . Right
    mf <*> mx = mf >>= \f -> fmap f mx

instance Monad (SamplerMonad abt) where
    return   = pure
    mx >>= k = SM $ \env -> unSM mx env >>= \x -> unSM (k x) env

pushEnv :: Assoc abt-> SamplerMonad abt a -> SamplerMonad abt a
pushEnv x (SM m) =
    SM $ \env -> m $ insertAssoc x env

getEnv :: SamplerMonad abt (Assocs abt)
getEnv = SM Right

failwith :: T.Text -> SamplerMonad abt a
failwith = SM . const . Left


insertAssoc :: Assoc abt -> Assocs abt -> Assocs abt
insertAssoc v@(Assoc x _) (Assocs xs) =
    Assocs $ IM.insert (fromNat $ varID x) v xs

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

sample :: (ABT abt, PrimMonad m) =>
          LC_ abt a -> PRNG m -> Assocs abt ->
          m (Sample a, LF.LogFloat, Assocs abt)
sample (LC_ e) g env =
  caseVarSyn e (sampleVar g env) $ \t ->
    case t of
      o :$ es  -> sampleScon o es g env
      Value_ v -> return (sampleValue v, one, env)

sampleScon :: (ABT abt, PrimMonad m) =>
              SCon args a -> SArgs abt args ->
              PRNG m      -> Assocs abt ->
              m (Sample a, LF.LogFloat, Assocs abt)
sampleScon (CoerceTo_ c) (e1 :* End) g env = do
    (v, weight, env) <- sample (LC_ e1) g env
    return (sampleCoerce c v, weight, env)

sampleScon o es g env = undefined

sampleCoerce :: (Coercion a b) -> Sample a -> Sample b
sampleCoerce CNil         a = a
sampleCoerce (CCons c cs) a = sampleCoerce cs (samplePrimCoerce c a)

samplePrimCoerce :: (PrimCoercion a b) -> Sample a -> Sample b
samplePrimCoerce (Signed HRing_Int ) a = fromNat a
samplePrimCoerce (Signed HRing_Real) a = LF.fromLogFloat a
samplePrimCoerce (Continuous HContinuous_Prob) a = LF.logFloat (fromNat a)
samplePrimCoerce (Continuous HContinuous_Real) a = fromIntegral a

sampleValue :: Value a -> Sample a
sampleValue (VNat  n)  = n
sampleValue (VInt  n)  = n
sampleValue (VProb n)  = n
sampleValue (VReal n)  = n
sampleValue (VDatum _) = error "Don't know how to sample Datum"

sampleVar :: (PrimMonad m, ABT abt) =>
             PRNG m -> Assocs abt -> Variable a -> 
             m (Sample a, LF.LogFloat, Assocs abt)
sampleVar g env v = do
  case lookupAssoc v env of
    Nothing -> error "variable not found!"
    Just a  -> sample (LC_ a) g env

runSample :: (ABT abt, Functor m, PrimMonad m) =>
             abt '[] a -> PRNG m -> m (Sample a, LF.LogFloat)
runSample prog g = do
  (v, weight, _) <- sample (LC_ prog) g emptyAssocs
  return (v, weight)

