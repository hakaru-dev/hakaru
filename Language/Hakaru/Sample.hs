{-# LANGUAGE CPP
           , GADTs
           , KindSignatures
           , TypeOperators
           , TypeFamilies
           , DataKinds
           , FlexibleContexts
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
import           Data.Sequence (Seq)
import qualified Data.Foldable                   as F
import Data.Maybe                                (fromMaybe)

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..), (<$>))
#endif

import Control.Monad.State
import Control.Monad.Trans.Maybe

import qualified Data.Text        as T
import qualified Data.IntMap      as IM

import Language.Hakaru.Syntax.Nat      (fromNat, unsafeNat, Nat())
import Language.Hakaru.Syntax.Coercion
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.HClasses
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Datum
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
type instance Sample m HBool          = Bool

type instance Sample m ('HMeasure a)  =
    LF.LogFloat -> PRNG m ->
    m (Maybe (Sample m a, LF.LogFloat))

type instance Sample m (a ':-> b)     = Sample m a -> Sample m b
type instance Sample m ('HArray a)    = V.Vector (Sample m a)
--type instance Sample m (HData' (HakaruCon a)) = SCode (Sample m a)

type instance Sample m ('HData t ('[ 'K b1, 'K b2] ': xss)) =
    (Sample m b1, Sample m b2)
----------------------------------------------------------------

data SCode a where
     SInr :: !(SCode a) -> SCode a
     SInl :: SStruct a -> SCode a

infixr 7 `SEt`

data SStruct a where
     SEt   :: !(SDFun a) -> !(SStruct a) -> SStruct a
     SDone :: SStruct a

data SDFun a where
     SKonst  :: Show b => !b -> SDFun a
     SIdent  :: Show a => !a -> SDFun a 

----------------------------------------------------------------

data EAssoc m where
     EAssoc :: {-# UNPACK #-} !(Variable a) -> !(Sample m a) -> EAssoc m

newtype Env m = Env (IM.IntMap (EAssoc m))

emptyEnv :: Env m
emptyEnv = Env IM.empty

updateEnv :: EAssoc m -> Env m -> Env m
updateEnv v@(EAssoc x _) (Env xs) =
    Env $ IM.insert (fromNat $ varID x) v xs

lookupVar :: Variable a -> Env m -> Maybe (Sample m a)
lookupVar x (Env env) = do
  EAssoc x' e' <- IM.lookup (fromNat $ varID x) env
  Refl         <- varEq x x'
  return e'

---------------------------------------------------------------

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

sample :: (ABT AST abt, PrimMonad m, Functor m) =>
          LC_ abt a -> Env m -> S m a
sample (LC_ e) env =
  caseVarSyn e (sampleVar env) $ \t -> sampleAST t env

sampleAST :: (ABT AST abt, PrimMonad m, Functor m) =>
             AST abt a -> Env m -> S m a
sampleAST t env =
    case t of
      o :$ es      -> sampleScon   o es env
      NaryOp_ o es -> sampleNaryOp o es env
      Value_  v    -> sampleValue  v
      Datum_  d    -> sampleDatum  d env
      Case_   o es -> error "in Case_"

sampleScon :: (ABT AST abt, PrimMonad m, Functor m) =>
              SCon args a -> SArgs abt args ->
              Env m -> S m a

sampleScon (CoerceTo_   c) (e1 :* End) env =
    let v = sample (LC_ e1) env
    in  sampleCoerce c v

sampleScon (UnsafeFrom_ c) (e1 :* End) env =
    let v = sample (LC_ e1) env
    in  sampleUnsafe c v

sampleScon (Ann_   _)      (e1 :* End) env = sample (LC_ e1) env

sampleScon (MeasureOp_  m) es env = sampleMeasureOp m es env

sampleScon Dirac           (e1 :* End) env =
  let S a = sample (LC_ e1) env
  in  S (\p _ -> return $ Just (a, p))

sampleScon MBind (e1 :* e2 :* End) env =
    let S m1 = sample (LC_ e1) env in
    S (\ p g -> do
         x <- m1 p g
         case x of
           Nothing ->
               return Nothing
           Just (a, p') ->
               caseBind e2 $ \x e2' ->
                   let y = sample (LC_ e2')
                                  (updateEnv (EAssoc x a) env)
                   in  (unS y) p' g)

sampleCoerce :: Coercion a b -> S m a -> S m b
sampleCoerce CNil         (S a) = S a
sampleCoerce (CCons c cs) (S a) = sampleCoerce cs (samplePrimCoerce c (S a))

sampleUnsafe :: Coercion a b -> S m b -> S m a
sampleUnsafe CNil         (S a) = S a
sampleUnsafe (CCons c cs) (S a) = samplePrimUnsafe c (sampleUnsafe cs (S a))

samplePrimCoerce :: (PrimCoercion a b) -> S m a -> S m b
samplePrimCoerce (Signed HRing_Int ) (S a) = S $ fromNat a
samplePrimCoerce (Signed HRing_Real) (S a) = S $ LF.fromLogFloat a
samplePrimCoerce (Continuous HContinuous_Prob) (S a) = S $ LF.logFloat (fromIntegral (fromNat a) :: Double)
samplePrimCoerce (Continuous HContinuous_Real) (S a) = S $ fromIntegral a

samplePrimUnsafe :: (PrimCoercion a b) -> S m b -> S m a
samplePrimUnsafe (Signed HRing_Int ) (S a) = S $ unsafeNat a
samplePrimUnsafe (Signed HRing_Real) (S a) = S $ LF.logFloat a
samplePrimUnsafe (Continuous HContinuous_Prob) (S a) =
    S $ unsafeNat $ floor (LF.fromLogFloat a :: Double)
samplePrimUnsafe (Continuous HContinuous_Real) (S a) = S $ floor a

sampleNaryOp :: (ABT AST abt, PrimMonad m, Functor m) =>
                NaryOp a -> Seq (abt '[] a) ->
                Env m -> S m a

sampleNaryOp And es env = S $ F.foldr (&&) True xs
  where xs = fmap (\a -> unS $ sample (LC_ a) env) es

sampleNaryOp (Sum HSemiring_Nat)  es env = S $ F.foldr (+) 0 xs
  where xs = fmap (\a -> unS $ sample (LC_ a) env) es

sampleNaryOp (Sum HSemiring_Int)  es env = S $ F.foldr (+) 0 xs
  where xs = fmap (\a -> unS $ sample (LC_ a) env) es

sampleNaryOp (Sum HSemiring_Prob) es env = S $ F.foldr (+) 0 xs
  where xs = fmap (\a -> unS $ sample (LC_ a) env) es

sampleNaryOp (Sum HSemiring_Real)  es env = S $ F.foldr (+) 0 xs
  where xs = fmap (\a -> unS $ sample (LC_ a) env) es


sampleMeasureOp :: (ABT AST abt, PrimMonad m, Functor m,
                    typs ~ UnLCs args, args ~ LCs typs) =>
                   MeasureOp typs a -> SArgs abt args ->
                   Env m -> S m ('HMeasure a)

sampleMeasureOp Lebesgue    End         env =
  S (\p g -> do
       (u,b) <- MWC.uniform g
       let l = log u
       let n = -l
       return $ Just (if b then n
                      else l, 2 * LF.logToLogFloat n))

sampleMeasureOp Counting    End         env =
  S (\p g -> do
       let success = LF.logToLogFloat (-3 :: Double)
       let pow x y = LF.logToLogFloat (LF.logFromLogFloat x *
                                       (fromIntegral y :: Double))
       u <- MWCD.geometric0 (LF.fromLogFloat success) g
       b <- MWC.uniform g
       return $ Just (if b then -1-u
                      else u, 2 / pow (1-success) u / success))

sampleMeasureOp Categorical (e1 :* End) env =
  S (\p g -> do
       let S v = sample (LC_ e1) env
       let (_,y,ys) = normalizeVector v
       if not (y > (0::Double)) then
           error "Categorical needs positive weights"
       else do
         u <- MWC.uniformR (0, y) g
         return $ Just (unsafeNat $ fromMaybe 0 (V.findIndex (u <=)
                                                 (V.scanl1' (+) ys))
                       , p))

sampleMeasureOp Uniform (e1 :* e2 :* End) env =
  let S v1 = sample (LC_ e1) env
      S v2 = sample (LC_ e2) env
  in  S (\ p g -> do
           x <- MWC.uniformR (v1, v2) g
           return $ Just (x, p))

sampleMeasureOp Normal  (e1 :* e2 :* End) env =
  let S v1 = sample (LC_ e1) env
      S v2 = sample (LC_ e2) env
  in  S (\ p g -> do
           x <- MWCD.normal v1 (LF.fromLogFloat v2) g
           return $ (Just (x, p)))

sampleMeasureOp Poisson (e1 :* End)       env =
  let S v1 = sample (LC_ e1) env
  in  S (\ p g -> do
           x <- poisson_rng (LF.fromLogFloat v1) g
           return $ Just (unsafeNat x, p))

sampleMeasureOp Gamma   (e1 :* e2 :* End) env =
  let S v1 = sample (LC_ e1) env
      S v2 = sample (LC_ e2) env
  in  S (\ p g -> do
           x <- MWCD.gamma (LF.fromLogFloat v1) (LF.fromLogFloat v2) g
           return $ Just (LF.logFloat x, p))

sampleMeasureOp Beta    (e1 :* e2 :* End) env =
  let S v1 = sample (LC_ e1) env
      S v2 = sample (LC_ e2) env
  in  S (\ p g -> do
           x <- MWCD.beta (LF.fromLogFloat v1) (LF.fromLogFloat v2) g
           return $ Just (LF.logFloat x, p))

sampleMeasureOp (DirichletProcess _)  _ env =
    error "sampleMeasureOp: Dirichlet Processes not implemented yet"

sampleMeasureOp (Plate _)   (e1 :* End) env =
    let S v = sample (LC_ e1) env
    in  S (\ p g -> runMaybeT $ do
             samples <- V.mapM (\m -> MaybeT $ m 1 g) v
             let (v', ps) = V.unzip samples
             return (v', p * V.product ps))

sampleMeasureOp (Chain _ _) (e1 :* e2 :* End) env =
  let S v = sample (LC_ e1) env
      S s = sample (LC_ e2) env
  in  S (\ p g -> runMaybeT $ do
           let convert f = StateT $ \s' -> do
                             ((a,s''),p') <- MaybeT (f s' 1 g)
                             return ((a,p'),s'')
           (samples, sout) <- runStateT (V.mapM convert v) s
           let (v', ps) = V.unzip samples
           return ((v', sout), p * V.product ps))

sampleMeasureOp _ _ _ =
    error "sampleMeasureOP: the impossible happened"

sampleValue :: Value a -> S m a
sampleValue (VNat  n)  = S n
sampleValue (VInt  n)  = S n
sampleValue (VProb n)  = S n
sampleValue (VReal n)  = S n
sampleValue (VDatum _) = error "Don't know how to sample Datum"

-- HACK only will work for HPair
sampleDatum :: (ABT AST abt, PrimMonad m, Functor m) =>
                Datum (abt '[]) (HData' a) ->
                Env m -> S m (HData' a)

sampleDatum (Datum _ (Inl (Et (Konst a)
                           (Et (Konst b) Done)))) env =
             let S a1 = sample (LC_ a) env
                 S a2 = sample (LC_ b) env
             in  S (a1, a2)

sampleDatum (Datum _ _) _ = error "TODO: Handle this case in Datum"

sampleVar :: (PrimMonad m, Functor m) =>
             Env m -> Variable a -> S m a
sampleVar env v = do
  case lookupVar v env of
    Nothing -> error "variable not found!"
    Just a  -> S a

runSample :: (ABT AST abt, Functor m, PrimMonad m) =>
             abt '[] a -> S m a
runSample prog = sample (LC_ prog) emptyEnv

