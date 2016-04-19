{-# LANGUAGE CPP
           , GADTs
           , KindSignatures
           , TypeOperators
           , TypeFamilies
           , EmptyCase
           , DataKinds
           , PolyKinds
           , ExistentialQuantification
           , FlexibleContexts
           , OverloadedStrings
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}

module Language.Hakaru.Sample where

import           Numeric.SpecFunctions           (logGamma, logBeta, logFactorial)
import qualified Data.Number.LogFloat            as LF
-- import qualified Numeric.Integration.TanhSinh    as TS
import qualified System.Random.MWC               as MWC
import qualified System.Random.MWC.Distributions as MWCD
import qualified Data.Vector                     as V
import           Data.Sequence (Seq)
import qualified Data.Foldable                   as F
import qualified Data.List.NonEmpty              as L
import           Data.List.NonEmpty              (NonEmpty(..))
import           Data.Maybe                      (fromMaybe)
#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..), (<$>))
#endif
import           Control.Monad.Identity
import           Control.Monad.Trans.Maybe
import           Control.Monad.State.Strict
import qualified Data.IntMap                     as IM

import Data.Number.Nat     (fromNat, unsafeNat)
import Data.Number.Natural (fromNatural, fromNonNegativeRational)
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Types.Sing
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.TypeOf
import Language.Hakaru.Syntax.Value
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.DatumCase
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT

data EAssoc =
    forall a. EAssoc {-# UNPACK #-} !(Variable a) !(Value a)

newtype Env = Env (IM.IntMap EAssoc)

emptyEnv :: Env
emptyEnv = Env IM.empty

updateEnv :: EAssoc -> Env -> Env
updateEnv v@(EAssoc x _) (Env xs) =
    Env $ IM.insert (fromNat $ varID x) v xs

lookupVar :: Variable a -> Env -> Maybe (Value a)
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
poisson_rng :: Double -> MWC.GenIO -> IO Int
poisson_rng lambda g' = make_poisson g'
    where
    smu   = sqrt lambda
    b     = 0.931 + 2.53*smu
    a     = -0.059 + 0.02483*b
    vr    = 0.9277 - 3.6224/(b - 2)
    arep  = 1.1239 + 1.1368/(b - 3.4)
    lnlam = log lambda

    make_poisson :: MWC.GenIO -> IO Int
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


normalize :: [Value 'HProb] -> (LF.LogFloat, Double, [Double])
normalize []          = (0, 0, [])
normalize [(VProb x)] = (x, 1, [1])
normalize xs          = (m, y, ys)
    where
    xs' = map (\(VProb x) -> x) xs
    m   = maximum xs'
    ys  = [ LF.fromLogFloat (x/m) | x <- xs' ]
    y   = sum ys


normalizeVector
    :: Value ('HArray 'HProb) -> (LF.LogFloat, Double, V.Vector Double)
normalizeVector (VArray xs) =
    let xs' = V.map (\(VProb x) -> x) xs in
    case V.length xs of
    0 -> (0, 0, V.empty)
    1 -> (V.unsafeHead xs', 1, V.singleton 1)
    _ ->
        let m   = V.maximum xs'
            ys  = V.map (\x -> LF.fromLogFloat (x/m)) xs'
            y   = V.sum ys
        in (m, y, ys)

---------------------------------------------------------------

runEvaluate
    :: (ABT Term abt)
    => abt '[] a
    -> Value a
runEvaluate prog = evaluate prog emptyEnv

evaluate
    :: (ABT Term abt)
    => abt '[] a
    -> Env
    -> Value a
evaluate e env = caseVarSyn e (evaluateVar env) (flip evaluateTerm env)

evaluateVar :: Env -> Variable a -> Value a
evaluateVar env v =
    case lookupVar v env of
    Nothing -> error "variable not found!"
    Just a  -> a

evaluateTerm
    :: (ABT Term abt)
    => Term abt a
    -> Env
    -> Value a
evaluateTerm t env =
    case t of
    o :$ es       -> evaluateScon    o es env
    NaryOp_  o es -> evaluateNaryOp  o es env
    Literal_ v    -> evaluateLiteral v
    Empty_   _    -> evaluateEmpty
    Array_   n es -> evaluateArray   n es env
    Datum_   d    -> evaluateDatum   d    env
    Case_    o es -> evaluateCase    o es env
    Superpose_ es -> evaluateSuperpose es env
    Reject_ _     -> VMeasure $ \_ _ -> return Nothing

evaluateScon
    :: (ABT Term abt)
    => SCon args a
    -> SArgs abt args
    -> Env
    -> Value a
evaluateScon Lam_ (e1 :* End) env =
    caseBind e1 $ \x e1' ->
        VLam $ \v -> evaluate e1' (updateEnv (EAssoc x v) env)
evaluateScon App_ (e1 :* e2 :* End) env =
    case evaluate e1 env of
    VLam f -> f (evaluate e2 env)
    v      -> case v of {}
evaluateScon Let_ (e1 :* e2 :* End) env =
    let v = evaluate e1 env
    in caseBind e2 $ \x e2' ->
        evaluate e2' (updateEnv (EAssoc x v) env)
evaluateScon (CoerceTo_   c) (e1 :* End) env =
    coerceTo c $ evaluate e1 env
evaluateScon (UnsafeFrom_ c) (e1 :* End) env =
    coerceFrom c $ evaluate e1 env
evaluateScon (PrimOp_ o)     es env = evaluatePrimOp    o es env
evaluateScon (ArrayOp_ o)    es env = evaluateArrayOp   o es env
evaluateScon (MeasureOp_  m) es env = evaluateMeasureOp m es env
evaluateScon Dirac           (e1 :* End) env =
    VMeasure $ \p _ -> return $ Just (evaluate e1 env, p)
evaluateScon MBind (e1 :* e2 :* End) env =
    case evaluate e1 env of
    VMeasure m1 -> VMeasure $ \ p g -> do
        x <- m1 p g
        case x of
            Nothing -> return Nothing
            Just (a, p') ->
                caseBind e2 $ \x' e2' ->
                    case evaluate e2' (updateEnv (EAssoc x' a) env) of
                    VMeasure y -> y p' g
                    v          -> case v of {}
    v -> case v of {}

evaluateScon Plate (n :* e2 :* End) env =
    case evaluate n env of
    VNat n' -> caseBind e2 $ \x e' ->
        VMeasure $ \(VProb p) g -> runMaybeT $ do
            (v', ps) <- fmap V.unzip . V.mapM (performMaybe g) $
                V.generate (fromNat n') $ \v ->
                    evaluate e' $
                    updateEnv (EAssoc x . VNat $ unsafeNat v) env
            return
                ( VArray v'
                , VProb $ p * V.product (V.map (\(VProb x) -> x) ps)
                )
    v -> case v of {}
    where
    performMaybe
        :: MWC.GenIO
        -> Value ('HMeasure a)
        -> MaybeT IO (Value a, Value 'HProb)
    performMaybe g (VMeasure m) = MaybeT $ m (VProb 1) g

evaluateScon Chain (n :* s :* e :* End) env =
    case (evaluate n env, evaluate s env) of
    (VNat n', start) ->
        caseBind e $ \x e' ->
            let s' = VLam $ \v -> evaluate e' (updateEnv (EAssoc x v) env) in
            VMeasure (\(VProb p) g -> runMaybeT $ do
                (evaluates, sout) <- runStateT (replicateM (fromNat n') $ convert g s') start
                let (v', ps) = unzip evaluates
                    bodyType :: Sing ('HMeasure (HPair a b)) -> Sing ('HArray a)
                    bodyType = SArray . fst . sUnPair . sUnMeasure
                return
                    ( VDatum $ dPair_ (bodyType $ caseBind e (const typeOf)) (typeOf s)
                        (VArray . V.fromList $ v') sout
                    , VProb $ p * product (map (\(VProb x) -> x) ps)
                    ))
    v -> case v of {}
    where
    convert
        :: MWC.GenIO
        -> Value (s ':-> 'HMeasure (HPair a s))
        -> StateT (Value s) (MaybeT IO) (Value a, Value 'HProb)
    convert g (VLam f) = StateT $ \s' ->
        case f s' of
        VMeasure f' -> do
            (as'', p') <- MaybeT (f' (VProb 1) g)
            let (a, s'') = unPair as''
            return ((a, p'), s'')
        v -> case v of {}

    unPair :: Value (HPair a b) -> (Value a, Value b)
    unPair (VDatum (Datum "pair" _typ
        (Inl (Et (Konst a)
            (Et (Konst b) Done))))) = (a, b)
    unPair x = case x of {}



evaluatePrimOp
    ::  ( ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => PrimOp typs a
    -> SArgs abt args
    -> Env
    -> Value a
evaluatePrimOp Not (e1 :* End) env = 
    case evaluate e1 env of        
      VDatum a -> if a == dTrue
                  then VDatum dFalse
                  else VDatum dTrue
      v        -> case v of {}

evaluatePrimOp Pi  End         _   = VProb . LF.logFloat $ pi
evaluatePrimOp Cos (e1 :* End) env =
    case evaluate e1 env of
      VReal v1 -> VReal . cos $ v1
      v        -> case v of {}
evaluatePrimOp RealPow (e1 :* e2 :* End) env =
    case (evaluate e1 env, evaluate e2 env) of
      (VProb v1, VReal v2) -> VProb $ LF.pow v1 v2
      v                    -> case v of {}
evaluatePrimOp Exp (e1 :* End) env =
    case evaluate e1 env of
      VReal v1 -> VProb . LF.logToLogFloat $ v1
      v        -> case v of {}
evaluatePrimOp Infinity         End _ = VProb $ LF.logFloat LF.infinity
evaluatePrimOp NegativeInfinity End _ = VReal $ LF.negativeInfinity
evaluatePrimOp (Less _) (e1 :* e2 :* End) env =
    case (evaluate e1 env, evaluate e2 env) of
    (VNat  v1, VNat  v2) -> VDatum $ if v1 < v2 then dTrue else dFalse
    (VReal v1, VReal v2) -> VDatum $ if v1 < v2 then dTrue else dFalse
    v                    -> error "TODO: evaluatePrimOp{Less}"
evaluatePrimOp (Negate _) (e1 :* End) env = 
    case evaluate e1 env of
    VInt  v -> VInt  (negate v)
    VReal v -> VReal (negate v)
    v       -> case v of {}
evaluatePrimOp (Recip _) (e1 :* End) env = 
    case evaluate e1 env of
    VProb v -> VProb (recip v)
    VReal v -> VReal (recip v)
    v       -> case v of {}
evaluatePrimOp prim _ _ =
    error ("TODO: evaluatePrimOp{" ++ show prim ++ "}")

evaluateArrayOp
    :: ( ABT Term abt
       , typs ~ UnLCs args
       , args ~ LCs typs)
    => ArrayOp typs a
    -> SArgs abt args
    -> Env
    -> Value a
evaluateArrayOp (Index _)  (e1 :* e2 :* End) env =
    case (evaluate e1 env, evaluate e2 env) of
    (VArray v, VNat n) -> v V.! fromNat n
    v                  -> case v of {}

evaluateArrayOp (Size _)   (e1 :* End) env =
    case evaluate e1 env of
    VArray v -> VNat . unsafeNat $ V.length v
    v        -> case v of {}

evaluateArrayOp (Reduce _) (e1 :* e2 :* e3 :* End) env =
    case ( evaluate e1 env
         , evaluate e2 env
         , evaluate e3 env) of
    (f, a, VArray v) -> V.foldl' (lam2 f) a v
    v        -> case v of {}

evaluateMeasureOp
    :: ( ABT Term abt
       , typs ~ UnLCs args
       , args ~ LCs typs)
    => MeasureOp typs a
    -> SArgs abt args
    -> Env
    -> Value ('HMeasure a)

evaluateMeasureOp Lebesgue End _ =
    VMeasure $ \(VProb p) g -> do
        (u,b) <- MWC.uniform g
        let l = log u
        let n = -l
        return $ Just
            ( VReal $ if b then n else l
            , VProb $ p * 2 * LF.logToLogFloat n
            )

evaluateMeasureOp Counting End _ =
    VMeasure $ \(VProb p) g -> do
        let success = LF.logToLogFloat (-3 :: Double)
        let pow x y = LF.logToLogFloat (LF.logFromLogFloat x *
                                       (fromIntegral y :: Double))
        u <- MWCD.geometric0 (LF.fromLogFloat success) g
        b <- MWC.uniform g
        return $ Just
            ( VInt  $ if b then -1-u else u
            , VProb $ p * 2 / pow (1-success) u / success)

evaluateMeasureOp Categorical (e1 :* End) env =
    VMeasure $ \p g -> do
        let (_,y,ys) = normalizeVector (evaluate e1 env)
        if not (y > (0::Double)) -- TODO: why not use @y <= 0@ ??
        then error "Categorical needs positive weights"
        else do
            u <- MWC.uniformR (0, y) g
            return $ Just
                ( VNat
                . unsafeNat
                . fromMaybe 0
                . V.findIndex (u <=) 
                . V.scanl1' (+)
                $ ys
                , p)

evaluateMeasureOp Uniform (e1 :* e2 :* End) env =
    case (evaluate e1 env, evaluate e2 env) of
    (VReal v1, VReal v2) -> VMeasure $ \p g -> do
        x <- MWC.uniformR (v1, v2) g
        return $ Just (VReal x, p)
    v -> case v of {}

evaluateMeasureOp Normal (e1 :* e2 :* End) env =
    case (evaluate e1 env, evaluate e2 env) of 
    (VReal v1, VProb v2) -> VMeasure $ \ p g -> do
        x <- MWCD.normal v1 (LF.fromLogFloat v2) g
        return $ Just (VReal x, p)
    v -> case v of {}

evaluateMeasureOp Poisson (e1 :* End) env =
    case evaluate e1 env of
    VProb v1 -> VMeasure $ \ p g -> do
        x <- poisson_rng (LF.fromLogFloat v1) g
        return $ Just (VNat $ unsafeNat x, p)
    v -> case v of {}

evaluateMeasureOp Gamma (e1 :* e2 :* End) env =
    case (evaluate e1 env, evaluate e2 env) of 
    (VProb v1, VProb v2) -> VMeasure $ \ p g -> do
        x <- MWCD.gamma (LF.fromLogFloat v1) (LF.fromLogFloat v2) g
        return $ Just (VProb $ LF.logFloat x, p)
    v -> case v of {}

evaluateMeasureOp Beta (e1 :* e2 :* End) env =
    case (evaluate e1 env, evaluate e2 env) of 
    (VProb v1, VProb v2) -> VMeasure $ \ p g -> do
        x <- MWCD.beta (LF.fromLogFloat v1) (LF.fromLogFloat v2) g
        return $ Just (VProb $ LF.logFloat x, p)
    v -> case v of {}

evaluateNaryOp
    :: (ABT Term abt)
    => NaryOp a -> Seq (abt '[] a) -> Env -> Value a
evaluateNaryOp s es =
    F.foldr (evalOp s) (identityElement s) . mapEvaluate es

identityElement :: NaryOp a -> Value a
identityElement And                   = VDatum dTrue
identityElement (Sum HSemiring_Nat)   = VNat  0
identityElement (Sum HSemiring_Int)   = VInt  0
identityElement (Sum HSemiring_Prob)  = VProb 0
identityElement (Sum HSemiring_Real)  = VReal 0
identityElement (Prod HSemiring_Nat)  = VNat  1
identityElement (Prod HSemiring_Int)  = VInt  1
identityElement (Prod HSemiring_Prob) = VProb 1
identityElement (Prod HSemiring_Real) = VReal 1


evalOp
    :: NaryOp a -> Value a -> Value a -> Value a
evalOp And (VDatum a) (VDatum b)        
    | a == dTrue && b == dTrue = VDatum dTrue
    | otherwise = VDatum dFalse
evalOp (Sum  HSemiring_Nat)  (VNat   a) (VNat  b) = VNat  (a + b)
evalOp (Sum  HSemiring_Int)  (VInt   a) (VInt  b) = VInt  (a + b)
evalOp (Sum  HSemiring_Prob) (VProb  a) (VProb b) = VProb (a + b)
evalOp (Sum  HSemiring_Real) (VReal  a) (VReal b) = VReal (a + b)
evalOp (Prod HSemiring_Nat)  (VNat   a) (VNat  b) = VNat  (a * b)
evalOp (Prod HSemiring_Int)  (VInt   a) (VInt  b) = VInt  (a * b)  
evalOp (Prod HSemiring_Prob) (VProb  a) (VProb b) = VProb (a * b)  
evalOp (Prod HSemiring_Real) (VReal  a) (VReal b) = VReal (a * b)

mapEvaluate
    :: (ABT Term abt)
    => Seq (abt '[] a) -> Env -> Seq (Value a)
mapEvaluate es env = fmap (flip evaluate env) es


evaluateLiteral :: Literal a -> Value a
evaluateLiteral (LNat  n) = VNat  . fromInteger $ fromNatural n -- TODO: catch overflow errors
evaluateLiteral (LInt  n) = VInt  $ fromInteger n -- TODO: catch overflow errors
evaluateLiteral (LProb n) = VProb . fromRational $ fromNonNegativeRational n
evaluateLiteral (LReal n) = VReal $ fromRational n

evaluateEmpty :: Value ('HArray a)
evaluateEmpty = VArray V.empty

evaluateArray
    :: (ABT Term abt)
    => (abt '[] 'HNat)
    -> (abt '[ 'HNat ] a)
    -> Env
    -> Value ('HArray a)
evaluateArray n e env =
    case evaluate n env of
    VNat n' -> caseBind e $ \x e' ->
        VArray $ V.generate (fromNat n') $ \v ->
            let v' = VNat $ unsafeNat v in
            evaluate e' (updateEnv (EAssoc x v') env)
    v -> case v of {}

evaluateDatum
    :: (ABT Term abt)
    => Datum (abt '[]) (HData' a)
    -> Env
    -> Value (HData' a)
evaluateDatum d env = VDatum (fmap11 (flip evaluate env) d)

evaluateCase
    :: forall abt a b
    .  (ABT Term abt)
    => abt '[] a
    -> [Branch a abt b]
    -> Env
    -> Value b
evaluateCase o es env =
    case runIdentity $ matchBranches evaluateDatum' (evaluate o env) es of
    Just (Matched as Nil1, b) ->
        evaluate b (extendFromMatch (as []) env)    
    _ -> error "Missing cases in match expression"
    where
    extendFromMatch :: [Assoc Value] -> Env -> Env 
    extendFromMatch []                env' = env'
    extendFromMatch ((Assoc x v1):as) env' =
        extendFromMatch as (updateEnv (EAssoc x v1) env')

    evaluateDatum' :: DatumEvaluator Value Identity
    evaluateDatum' = return . Just . getVDatum

    getVDatum :: Value (HData' a) -> Datum Value (HData' a)
    getVDatum (VDatum a) = a

evaluateSuperpose
    :: (ABT Term abt)
    => NonEmpty (abt '[] 'HProb, abt '[] ('HMeasure a))
    -> Env
    -> Value ('HMeasure a)
evaluateSuperpose ((q, m) :| []) env =
    case evaluate m env of
    VMeasure m' ->
        let VProb q' = evaluate q env
        in  VMeasure (\(VProb p) g -> m' (VProb $ p * q') g)
        
evaluateSuperpose pms@((_, m) :| _) env =
    case evaluate m env of
    VMeasure m' ->
        let pms'     = L.toList pms
            weights  = map ((flip evaluate env) . fst) pms'
            (x,y,ys) = normalize weights
        in VMeasure $ \(VProb p) g ->
            if not (y > (0::Double)) then return Nothing else do
            u <- MWC.uniformR (0, y) g
            case [ m1 | (v,(_,m1)) <- zip (scanl1 (+) ys) pms', u <= v ] of
                m2 : _ ->
                    case evaluate m2 env of
                    VMeasure m2' -> m2' (VProb $ p * x * LF.logFloat y) g
                []     -> m' (VProb $ p * x * LF.logFloat y) g

----------------------------------------------------------------
----------------------------------------------------------- fin.
