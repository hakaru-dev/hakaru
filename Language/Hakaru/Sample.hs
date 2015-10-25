{-# LANGUAGE GADTs
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
--import Control.Monad.State
--import Control.Monad.Trans.Maybe

--import qualified Data.Text        as Text
import Language.Hakaru.Syntax.Nat      (fromNat, Nat(..))
--import Language.Hakaru.Syntax.IClasses (fmap11, foldMap11)
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT

type PRNG m = MWC.Gen (PrimState m)

type family   Sample (a :: Hakaru) :: *
type instance Sample 'HNat          = Nat
type instance Sample 'HInt          = Int 
type instance Sample 'HReal         = Double 
type instance Sample 'HProb         = LF.LogFloat 

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

class Sampleable (f :: Hakaru -> *) where
    sample :: PrimMonad m =>
              f a -> PRNG m -> m (Sample a, LF.LogFloat)

instance (ABT abt) => Sampleable (LC_ abt) where
    sample (LC_ e) g =
      caseVarSyn e sampleVar $ \t ->
          case t of
            Value_ v -> sample v g

instance Sampleable Value where
    sample (VNat  n)  _  = return (n, one)
    sample (VInt  n)  _  = return (n, one)
    sample (VProb n)  _  = return (n, one)
    sample (VReal n)  _  = return (n, one)
    sample (VDatum _) _  = error "Don't know how to sample Datum"

-- HACK: all variables are 42!
sampleVar :: (PrimMonad m) =>
             Variable a -> m (Sample a, LF.LogFloat)
sampleVar _ = return (undefined, one)

runSample :: (ABT abt, Functor m, PrimMonad m) =>
             abt '[] a -> PRNG m -> m (Sample a, LF.LogFloat)
runSample prog g = sample (LC_ prog) g

