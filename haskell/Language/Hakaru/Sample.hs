{-# LANGUAGE CPP
           , KindSignatures
           , TypeOperators
           , TypeFamilies
           , DataKinds
           , PolyKinds
           , ExistentialQuantification
           , FlexibleContexts
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}

module Language.Hakaru.Sample where

import           Control.Monad.Primitive         (PrimState, PrimMonad)
import           Numeric.SpecFunctions           (logGamma, logBeta, logFactorial)
import qualified Data.Number.LogFloat            as LF
-- import qualified Numeric.Integration.TanhSinh    as TS
import qualified System.Random.MWC               as MWC
import qualified System.Random.MWC.Distributions as MWCD
import qualified Data.Vector                     as V
import           Data.Sequence (Seq)
import qualified Data.Foldable                   as F
import           Data.Maybe                      (fromMaybe)
#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..), (<$>))
#endif
import Control.Monad.Identity
-- import Control.Monad.State
import Control.Monad.Trans.Maybe
-- import qualified Data.Text        as T
import qualified Data.IntMap      as IM

import Data.Number.Nat     (fromNat, unsafeNat, Nat())
import Data.Number.Natural (fromNatural, fromNonNegativeRational)
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.DatumCase
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT
-- import Language.Hakaru.Evaluation.Types
-- import Language.Hakaru.Evaluation.Lazy
-- import Language.Hakaru.PrettyPrint

type PRNG m = MWC.Gen (PrimState m)

newtype S (m :: * -> *) (a :: Hakaru) =
    S { unS :: Sample m a }

type family   Sample (m :: * -> *) (a :: Hakaru) :: *
type instance Sample m 'HNat          = Nat
type instance Sample m 'HInt          = Int 
type instance Sample m 'HReal         = Double 
type instance Sample m 'HProb         = LF.LogFloat
type instance Sample m ('HMeasure a)  =
    LF.LogFloat -> PRNG m -> m (Maybe (Sample m a, LF.LogFloat))
type instance Sample m (a ':-> b)     = Sample m a -> Sample m b
type instance Sample m ('HArray a)    = V.Vector (Sample m a)
type instance Sample m ('HData t xss) = SDatum Term

----------------------------------------------------------------

data SDatum (a :: k1 -> k2 -> *)
    = forall i j. Show (a i j) => SDatum !(a i j)

----------------------------------------------------------------

data EAssoc m
    = forall a. EAssoc {-# UNPACK #-} !(Variable a) !(Sample m a)

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


normalize :: [LF.LogFloat] -> (LF.LogFloat, Double, [Double])
normalize []  = (0, 0, [])
normalize [x] = (x, 1, [1])
normalize xs  = (m, y, ys)
    where
    m  = maximum xs
    ys = [ LF.fromLogFloat (x/m) | x <- xs ]
    y  = sum ys


normalizeVector
    :: V.Vector LF.LogFloat -> (LF.LogFloat, Double, V.Vector Double)
normalizeVector xs =
    case V.length xs of
    0 -> (0, 0, V.empty)
    1 -> (V.unsafeHead xs, 1, V.singleton 1)
    _ ->
        let m  = V.maximum xs
            ys = V.map (\x -> LF.fromLogFloat (x/m)) xs
            y  = V.sum ys
        in (m, y, ys)

---------------------------------------------------------------

sample
    :: (ABT Term abt, PrimMonad m, Functor m, Show2 abt)
    => LC_ abt a -> Env m -> S m a
sample (LC_ e) env =
    caseVarSyn e (sampleVar env) $ \t -> sampleTerm t env


sampleTerm
    :: (ABT Term abt, PrimMonad m, Functor m, Show2 abt)
    => Term abt a -> Env m -> S m a
sampleTerm t env =
    case t of
    o :$ es       -> sampleScon    o es env
    NaryOp_  o es -> sampleNaryOp  o es env
    Literal_ v    -> sampleLiteral v
    Datum_   d    -> sampleDatum   d env
    Case_    o es -> sampleCase    o es env
    Superpose_ es -> sampleSuperpose es env


sampleScon
    :: (ABT Term abt, PrimMonad m, Functor m, Show2 abt)
    => SCon args a -> SArgs abt args -> Env m -> S m a
sampleScon Lam_ (e1 :* End)            env =
    caseBind e1 $ \x e1' ->
        S $ \v -> unS $ sample (LC_ e1') (updateEnv (EAssoc x v) env)
sampleScon App_ (e1 :* e2 :* End)      env =
    let S f = sample (LC_ e1) env
        S x = sample (LC_ e2) env
    in S (f x)
sampleScon Let_ (e1 :* e2 :* End)      env =
    let S v = sample (LC_ e1) env
    in caseBind e2 $ \x e2' ->
        sample (LC_ e2') (updateEnv (EAssoc x v) env)
sampleScon (Ann_   _)      (e1 :* End) env = sample (LC_ e1) env
sampleScon (CoerceTo_   c) (e1 :* End) env =
    coerceTo c $ sample (LC_ e1) env
sampleScon (UnsafeFrom_ c) (e1 :* End) env =
    coerceFrom c $ sample (LC_ e1) env
sampleScon (PrimOp_ o)     es env = samplePrimOp    o es env
sampleScon (MeasureOp_  m) es env = sampleMeasureOp m es env
sampleScon Dirac           (e1 :* End) env =
    let S a = sample (LC_ e1) env
    in  S $ \p _ -> return $ Just (a, p)
sampleScon MBind (e1 :* e2 :* End) env =
    let S m1 = sample (LC_ e1) env
    in S $ \ p g -> do
        x <- m1 p g
        case x of
            Nothing -> return Nothing
            Just (a, p') ->
                caseBind e2 $ \x e2' ->
                    let y = sample (LC_ e2') (updateEnv (EAssoc x a) env)
                    in  unS y p' g

instance Coerce (S m) where
    coerceTo   CNil         v = v
    coerceTo   (CCons c cs) v = coerceTo cs (primCoerceTo c v)

    coerceFrom CNil         v = v
    coerceFrom (CCons c cs) v = primCoerceFrom c (coerceFrom cs v)

instance PrimCoerce (S m) where
    primCoerceTo c l =
        case (c,l) of
        (Signed HRing_Int,            S a) -> S $ fromNat a
        (Signed HRing_Real,           S a) -> S $ LF.fromLogFloat a
        (Continuous HContinuous_Prob, S a) ->
            S $ LF.logFloat (fromIntegral (fromNat a) :: Double)
        (Continuous HContinuous_Real, S a) -> S $ fromIntegral a

    primCoerceFrom c l =
        case (c,l) of
        (Signed HRing_Int,            S a) -> S $ unsafeNat a
        (Signed HRing_Real,           S a) -> S $ LF.logFloat a
        (Continuous HContinuous_Prob, S a) ->
            S $ unsafeNat $ floor (LF.fromLogFloat a :: Double)
        (Continuous HContinuous_Real, S a) -> S $ floor a


samplePrimOp
    ::  ( ABT Term abt, PrimMonad m, Functor m, Show2 abt
        , typs ~ UnLCs args, args ~ LCs typs)
    => PrimOp typs a
    -> SArgs abt args
    -> Env m
    -> S m a
samplePrimOp Infinity         End _ = S $ LF.logFloat (1/0)
samplePrimOp NegativeInfinity End _ = S $ -1/0
samplePrimOp (Negate HRing_Int)  (e1 :* End) env = 
    let S v = sample (LC_ e1) env
    in  S (negate v)
samplePrimOp (Negate HRing_Real) (e1 :* End) env = 
    let S v = sample (LC_ e1) env
    in  S (negate v)

sampleNaryOp
    :: (ABT Term abt, PrimMonad m, Functor m, Show2 abt)
    => NaryOp a -> Seq (abt '[] a) -> Env m -> S m a
-- sampleNaryOp And es = S . F.foldr (&&) True . mapSample es
sampleNaryOp (Sum HSemiring_Nat)   es = S . F.foldr (+) 0 . mapSample es
sampleNaryOp (Sum HSemiring_Int)   es = S . F.foldr (+) 0 . mapSample es
sampleNaryOp (Sum HSemiring_Prob)  es = S . F.foldr (+) 0 . mapSample es
sampleNaryOp (Sum HSemiring_Real)  es = S . F.foldr (+) 0 . mapSample es
sampleNaryOp (Prod HSemiring_Nat)  es = S . F.foldr (*) 1 . mapSample es
sampleNaryOp (Prod HSemiring_Int)  es = S . F.foldr (*) 1 . mapSample es
sampleNaryOp (Prod HSemiring_Prob) es = S . F.foldr (*) 1 . mapSample es
sampleNaryOp (Prod HSemiring_Real) es = S . F.foldr (*) 1 . mapSample es

mapSample
    :: (ABT Term abt, PrimMonad m, Functor m, Show2 abt)
    => Seq (abt '[] a) -> Env m -> Seq (Sample m a)
mapSample es env = fmap (\a -> unS $ sample (LC_ a) env) es


sampleMeasureOp
    ::  ( ABT Term abt, PrimMonad m, Functor m, Show2 abt
        , typs ~ UnLCs args, args ~ LCs typs)
    => MeasureOp typs a -> SArgs abt args -> Env m -> S m ('HMeasure a)

sampleMeasureOp Lebesgue = \End _ ->
    S $ \p g -> do
        (u,b) <- MWC.uniform g
        let l = log u
        let n = -l
        return $ Just (if b then n else l, 2 * LF.logToLogFloat n)

sampleMeasureOp Counting = \End _ ->
    S $ \p g -> do
        let success = LF.logToLogFloat (-3 :: Double)
        let pow x y = LF.logToLogFloat (LF.logFromLogFloat x *
                                       (fromIntegral y :: Double))
        u <- MWCD.geometric0 (LF.fromLogFloat success) g
        b <- MWC.uniform g
        return $ Just
            ( if b then -1-u else u
            , 2 / pow (1-success) u / success)

sampleMeasureOp Categorical = \(e1 :* End) env ->
    S $ \p g -> do
        let S v = sample (LC_ e1) env
        let (_,y,ys) = normalizeVector v
        if not (y > (0::Double)) -- TODO: why not use @y <= 0@ ??
            then error "Categorical needs positive weights"
            else do
                u <- MWC.uniformR (0, y) g
                return $ Just
                    ( unsafeNat
                    . fromMaybe 0
                    . V.findIndex (u <=) 
                    . V.scanl1' (+)
                    $ ys
                    , p)

sampleMeasureOp Uniform = \(e1 :* e2 :* End) env ->
    let S v1 = sample (LC_ e1) env
        S v2 = sample (LC_ e2) env
    in  S $ \ p g -> do
            x <- MWC.uniformR (v1, v2) g
            return $ Just (x, p)

sampleMeasureOp Normal = \(e1 :* e2 :* End) env ->
    let S v1 = sample (LC_ e1) env
        S v2 = sample (LC_ e2) env
    in  S $ \ p g -> do
            x <- MWCD.normal v1 (LF.fromLogFloat v2) g
            return $ Just (x, p)

sampleMeasureOp Poisson = \(e1 :* End) env ->
    let S v1 = sample (LC_ e1) env
    in  S $ \ p g -> do
            x <- poisson_rng (LF.fromLogFloat v1) g
            return $ Just (unsafeNat x, p)

sampleMeasureOp Gamma = \(e1 :* e2 :* End) env ->
    let S v1 = sample (LC_ e1) env
        S v2 = sample (LC_ e2) env
    in  S $ \ p g -> do
            x <- MWCD.gamma (LF.fromLogFloat v1) (LF.fromLogFloat v2) g
            return $ Just (LF.logFloat x, p)

sampleMeasureOp Beta = \(e1 :* e2 :* End) env ->
    let S v1 = sample (LC_ e1) env
        S v2 = sample (LC_ e2) env
    in  S $ \ p g -> do
            x <- MWCD.beta (LF.fromLogFloat v1) (LF.fromLogFloat v2) g
            return $ Just (LF.logFloat x, p)

sampleMeasureOp (DirichletProcess _) = \_ _ ->
    error "sampleMeasureOp: Dirichlet Processes not implemented yet"

sampleMeasureOp (Plate _) = \(e1 :* End) env ->
    let S v = sample (LC_ e1) env
    in  S $ \ p g -> runMaybeT $ do
            samples <- V.mapM (\m -> MaybeT $ m 1 g) v
            let (v', ps) = V.unzip samples
            return (v', p * V.product ps)

sampleMeasureOp (Chain _ _) = \(e1 :* e2 :* End) env ->
    error "sampleMeasureOp: Chain not implemented yet"
--   let S v = sample (LC_ e1) env
--       S s = sample (LC_ e2) env
--   in  S (\ p g -> runMaybeT $ do
--            let convert f = StateT $ \s' -> do
--                              ((a,s''),p') <- MaybeT (f s' 1 g)
--                              return ((a,p'),s'')
--            (samples, sout) <- runStateT (V.mapM convert v) s
--            let (v', ps) = V.unzip samples
--            return ((v', sout), p * V.product ps))



sampleLiteral :: Literal a -> S m a
sampleLiteral (LNat  n) = S . fromInteger $ fromNatural n -- TODO: catch overflow errors
sampleLiteral (LInt  n) = S $ fromInteger n -- TODO: catch overflow errors
sampleLiteral (LProb n) = S . fromRational $ fromNonNegativeRational n
sampleLiteral (LReal n) = S $ fromRational n


-- This function (or, rather, its use od 'SDatum') is the reason
-- why we need the 'Show2' constraint everywhere in this file.
sampleDatum
    :: (ABT Term abt, PrimMonad m, Functor m, Show2 abt)
    => Datum (abt '[]) (HData' a)
    -> Env m
    -> S m (HData' a)
sampleDatum d _ = S (SDatum (Datum_ d))


sampleCase
    :: (ABT Term abt, PrimMonad m, Functor m, Show2 abt)
    => abt '[] a
    -> [Branch a abt b]
    -> Env m
    -> S m b
sampleCase o es env =
    case runIdentity $ matchBranches evaluateDatum o es of
    Just (Matched as Nil1, b) ->
        sample (LC_ $ extendFromMatch (as []) b) env
    Nothing -> error "Missing cases in match expression"
    where
    extendFromMatch
        :: (ABT Term abt) => [Assoc abt] -> abt '[] b -> abt '[] b 
    extendFromMatch []                e2 = e2
    extendFromMatch ((Assoc x e1):as) e2 =
        syn (Let_ :$ e1 :* bind x (extendFromMatch as e2) :* End)

    evaluateDatum :: (ABT Term abt, Monad m) => DatumEvaluator abt m
    evaluateDatum e =
        caseVarSyn e (error "evalueDatumVar: ¯\\_(ツ)_/¯") $ \t ->
            case t of
            Datum_ d            -> return . Just  $ d
            Ann_ _ :$ e1 :* End -> evaluateDatum e1 
            _ -> error "TODO: finish evaluate"
    

sampleSuperpose
    :: (ABT Term abt, PrimMonad m, Functor m, Show2 abt)
    => [(abt '[] 'HProb, abt '[] ('HMeasure a))]
    -> Env m
    -> S m ('HMeasure a)
sampleSuperpose []       _   = S $ \_ _ -> return Nothing
sampleSuperpose [(q, m)] env =
    let S q' = sample (LC_ q) env
        S m' = sample (LC_ m) env
    in  S (\p g -> m' (p * q') g)
        
sampleSuperpose pms@((q, m) : _) env =
    let weights  = map (unS . (\x -> sample (LC_ x) env) . fst) pms
        S m'     = sample (LC_ m) env
        (x,y,ys) = normalize weights
    in S $ \p g ->
        if not (y > (0::Double)) then return Nothing else do
            u <- MWC.uniformR (0, y) g
            case [ m1 | (v,(_,m1)) <- zip (scanl1 (+) ys) pms, u <= v ] of
                m2 : _ ->
                    let S m2' = sample (LC_ m2) env
                    in m2' (p * x * LF.logFloat y) g
                []     -> m' (p * x * LF.logFloat y) g

sampleVar :: (PrimMonad m, Functor m) => Env m -> Variable a -> S m a
sampleVar env v =
    case lookupVar v env of
    Nothing -> error "variable not found!"
    Just a  -> S a

runSample
    :: (ABT Term abt, Functor m, PrimMonad m, Show2 abt)
    => abt '[] a
    -> S m a
runSample prog = sample (LC_ prog) emptyEnv

