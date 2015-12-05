{-# LANGUAGE CPP
           , GADTs
           , KindSignatures
           , TypeOperators
           , TypeFamilies
           , DataKinds
           , PolyKinds
           , RankNTypes
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

import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans.Maybe

import qualified Data.Text        as T
import qualified Data.IntMap      as IM

import Language.Hakaru.Syntax.Nat      (fromNat, unsafeNat, Nat())
import Language.Hakaru.Syntax.Natural  (fromNatural, fromNonNegativeRational)
import Language.Hakaru.Syntax.Coercion
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.HClasses
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.DatumCase
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT

import Language.Hakaru.Lazy.Types
import Language.Hakaru.Lazy

import Language.Hakaru.PrettyPrint

type PRNG m = MWC.Gen (PrimState m)

newtype S (m :: * -> *) (a :: Hakaru) =
    S { unS :: Sample m a }

type family   Sample (m :: * -> *) (a :: Hakaru) :: *
type instance Sample m 'HNat          = Nat
type instance Sample m 'HInt          = Int 
type instance Sample m 'HReal         = Double 
type instance Sample m 'HProb         = LF.LogFloat

type instance Sample m ('HMeasure a)  =
    LF.LogFloat -> PRNG m ->
    m (Maybe (Sample m a, LF.LogFloat))

type instance Sample m (a ':-> b)     = Sample m a -> Sample m b
type instance Sample m ('HArray a)    = V.Vector (Sample m a)

type instance Sample m ('HData t xss) = SDatum AST

----------------------------------------------------------------

data SDatum (a :: k1 -> k2 -> *)
    = forall i j. Show (a i j) => SDatum !(a i j)

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

normalize :: [LF.LogFloat] ->
             (LF.LogFloat, Double, [Double])
normalize []  = (0, 0, [])
normalize [x] = (x, 1, [1])
normalize xs  = (m, y, ys)
  where m  = maximum xs
        ys = [ LF.fromLogFloat (x/m) | x <- xs ]
        y  = sum ys


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

sample :: (ABT AST abt, PrimMonad m, Functor m, Show2 abt) =>
          LC_ abt a -> Env m -> S m a
sample (LC_ e) env =
  caseVarSyn e (sampleVar env) $ \t -> sampleAST t env

sampleAST :: (ABT AST abt, PrimMonad m, Functor m, Show2 abt) =>
             AST abt a -> Env m -> S m a
sampleAST t env =
    case t of
      o :$ es       -> sampleScon    o es env
      NaryOp_  o es -> sampleNaryOp  o es env
      Literal_ v    -> sampleLiteral v
      Datum_   d    -> sampleDatum   d env
      Case_    o es -> sampleCase    o es env
      Superpose_ es -> sampleSuperpose es env

sampleScon :: (ABT AST abt, PrimMonad m, Functor m, Show2 abt) =>
              SCon args a -> SArgs abt args ->
              Env m -> S m a

sampleScon Lam_ (e1 :* End)            env =
    caseBind e1 $ \x e1' ->
        S (\v -> unS $ sample (LC_ e1')
                              (updateEnv (EAssoc x v) env))

sampleScon App_ (e1 :* e2 :* End)      env =
    let S f = sample (LC_ e1) env
        S x = sample (LC_ e2) env in
    S (f x)

sampleScon Let_ (e1 :* e2 :* End)      env =
    let S v = sample (LC_ e1) env in
    caseBind e2 $ \x e2' ->
        sample (LC_ e2') (updateEnv (EAssoc x v) env)

sampleScon (Ann_   _)      (e1 :* End) env = sample (LC_ e1) env

sampleScon (CoerceTo_   c) (e1 :* End) env =
    let v = sample (LC_ e1) env
    in  sampleCoerce c v

sampleScon (UnsafeFrom_ c) (e1 :* End) env =
    let v = sample (LC_ e1) env
    in  sampleUnsafe c v

sampleScon (PrimOp_ o)     es env = samplePrimOp    o es env

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

samplePrimOp :: (ABT AST abt, PrimMonad m, Functor m, Show2 abt,
                 typs ~ UnLCs args, args ~ LCs typs) =>
                PrimOp typs a -> SArgs abt args ->
                Env m -> S m a

samplePrimOp Infinity         End env = S $ LF.logFloat (1/0)

samplePrimOp NegativeInfinity End env = S $ -1/0

sampleNaryOp :: (ABT AST abt, PrimMonad m, Functor m, Show2 abt) =>
                NaryOp a -> Seq (abt '[] a) ->
                Env m -> S m a

-- sampleNaryOp And es env = S $ F.foldr (&&) True xs
--   where xs = fmap (\a -> unS $ sample (LC_ a) env) es

sampleNaryOp (Sum HSemiring_Nat)  es env = S $ F.foldr (+) 0 xs
  where xs = fmap (\a -> unS $ sample (LC_ a) env) es

sampleNaryOp (Sum HSemiring_Int)  es env = S $ F.foldr (+) 0 xs
  where xs = fmap (\a -> unS $ sample (LC_ a) env) es

sampleNaryOp (Sum HSemiring_Prob) es env = S $ F.foldr (+) 0 xs
  where xs = fmap (\a -> unS $ sample (LC_ a) env) es

sampleNaryOp (Sum HSemiring_Real)  es env = S $ F.foldr (*) 0 xs
  where xs = fmap (\a -> unS $ sample (LC_ a) env) es

sampleNaryOp (Prod HSemiring_Nat)  es env = S $ F.foldr (*) 1 xs
  where xs = fmap (\a -> unS $ sample (LC_ a) env) es

sampleNaryOp (Prod HSemiring_Int)  es env = S $ F.foldr (*) 1 xs
  where xs = fmap (\a -> unS $ sample (LC_ a) env) es

sampleNaryOp (Prod HSemiring_Prob) es env = S $ F.foldr (*) 1 xs
  where xs = fmap (\a -> unS $ sample (LC_ a) env) es

sampleNaryOp (Prod HSemiring_Real)  es env = S $ F.foldr (*) 1 xs
  where xs = fmap (\a -> unS $ sample (LC_ a) env) es


sampleMeasureOp :: (ABT AST abt, PrimMonad m, Functor m, Show2 abt,
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

-- sampleMeasureOp (Chain _ _) (e1 :* e2 :* End) env =
--   let S v = sample (LC_ e1) env
--       S s = sample (LC_ e2) env
--   in  S (\ p g -> runMaybeT $ do
--            let convert f = StateT $ \s' -> do
--                              ((a,s''),p') <- MaybeT (f s' 1 g)
--                              return ((a,p'),s'')
--            (samples, sout) <- runStateT (V.mapM convert v) s
--            let (v', ps) = V.unzip samples
--            return ((v', sout), p * V.product ps))

sampleMeasureOp _ _ _ =
    error "sampleMeasureOP: the impossible happened"

sampleLiteral :: Literal a -> S m a
sampleLiteral (LNat  n) = S (fromInteger $ fromNatural n) -- TODO: catch overflow errors
sampleLiteral (LInt  n) = S (fromInteger n) -- TODO: catch overflow errors
sampleLiteral (LProb n) = S (fromRational $ fromNonNegativeRational n)
sampleLiteral (LReal n) = S (fromRational n)

sampleDatum
    :: (ABT AST abt, PrimMonad m, Functor m, Show2 abt)
    => Datum (abt '[]) (HData' a)
    -> Env m
    -> S m (HData' a)
sampleDatum d env = S (SDatum (Datum_ d))

-- sampleDatum (Datum _ (Inl a)) env = sampleDCode (Inl a) env

-- sampleDatum (Datum _ _) _ = error "TODO: Handle this case in Datum"

-- sampleDCode   ::  (ABT AST abt, PrimMonad m, Functor m) =>
--                   DatumCode (xs1 ': xs) (abt '[]) ('HData t (xs1 ': xs)) ->
--                   Env m -> S m ('HData t (xs1 ': xs))

-- sampleDCode (Inl a) env = sampleDStruct a env

-- sampleDStruct ::  (ABT AST abt, PrimMonad m, Functor m) =>
--                   DatumStruct xs (abt '[])  ('HData t (xs1 ': xss)) ->
--                   Env m -> S m ('HData t (xs ': xss))
-- sampleDStruct (Et (Konst a) b) env = let S a1 = sampleDKonst (Konst a) env
--                                          S a2 = sampleDStruct b env
--                                      in  S $ Left (a1, a2)

-- sampleDStruct Done             env = S $ Left ()


-- sampleDKonst ::  (ABT AST abt, PrimMonad m, Functor m) => 
--                   DatumFun ('K b) (abt '[]) (HData' a) -> Env m -> S m b
-- sampleDKonst (Konst a) env = sample (LC_ a) env


sampleCase :: (ABT AST abt, PrimMonad m, Functor m, Show2 abt) =>
                (abt '[] a) -> [Branch a abt b] ->
                Env m -> S m b
sampleCase o es env =
    case runIdentity $ matchBranches undefined o es of
      Just (Matched as Nil1, b) -> sample (LC_ $ extendFromMatch (as []) b) env
  where extendFromMatch :: (ABT AST abt) =>
                           [Assoc abt] -> abt '[] b -> abt '[] b 
        extendFromMatch []                e2 = e2
        extendFromMatch ((Assoc x e1):as) e2 =
            syn (Let_ :$ e1 :*
                         bind x (extendFromMatch as e2) :* End)

    {-
    -- BUG: using 'perform' means using the 'M' EvaluationMonad, which returns the lub of results rather than just one!
    let w  = evaluate perform $ syn (Case_ o es)
        w1 = runM w [Some2 $ syn (Case_ o es)] in
    -- HACK: We need to use the below code instead of having
    -- sample (LC_ w1) env, because runM and friends are not
    -- defined for abt '[] a but abt '[] ('HMeasure a)
    caseVarSyn w1 undefined $ \t ->
        case dropLets t of
        Dirac :$ x :* End -> sample (LC_ x) env
        t -> error (show $ pretty w1)
    -- HACK: To remove the lets from residualizeListContext
    where dropLets (Let_ :$ e1 :* e2 :* End) =
            caseBind e2 $ \x e2' -> dropLets' (LC_ e2')
          dropLets e        = e
          dropLets' (LC_ e) =
                  caseVarSyn e undefined $ \t ->
                      dropLets t
    -}

sampleSuperpose :: (ABT AST abt, PrimMonad m, Functor m, Show2 abt) =>
                   [(abt '[] 'HProb, abt '[] ('HMeasure a))] ->
                   Env m -> S m ('HMeasure a)
sampleSuperpose []       env = S (\p g -> return Nothing)
sampleSuperpose [(q, m)] env =
  let S q' = sample (LC_ q) env
      S m' = sample (LC_ m) env
  in  S (\p g -> m' (p * q') g)
        
sampleSuperpose pms@((q, m) : _) env =
  let weights  = map (unS . (\x -> sample (LC_ x) env) . fst) pms
      S m'     = sample (LC_ m) env
      (x,y,ys) = normalize weights in
  S (\p g ->
   if not (y > (0::Double)) then return Nothing else do
     u <- MWC.uniformR (0, y) g
     case [ m1 | (v,(_,m1)) <- zip (scanl1 (+) ys) pms, u <= v ] of
         m2 : _ -> let S m2' = sample (LC_ m2) env in
                   m2' (p * x * LF.logFloat y) g
         []     -> m' (p * x * LF.logFloat y) g)

sampleVar :: (PrimMonad m, Functor m) =>
             Env m -> Variable a -> S m a
sampleVar env v = do
  case lookupVar v env of
    Nothing -> error "variable not found!"
    Just a  -> S a

runSample :: (ABT AST abt, Functor m, PrimMonad m, Show2 abt) =>
             abt '[] a -> S m a
runSample prog = sample (LC_ prog) emptyEnv

