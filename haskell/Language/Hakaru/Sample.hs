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

import           Numeric.SpecFunctions            (logGamma, logBeta, logFactorial)
import qualified Data.Number.LogFloat             as LF
import qualified Math.Combinatorics.Exact.Binomial as EB
-- import qualified Numeric.Integration.TanhSinh     as TS
import qualified System.Random.MWC                as MWC
import qualified System.Random.MWC.CondensedTable as MWC
import qualified System.Random.MWC.Distributions  as MWCD

import qualified Data.Vector                      as V
import           Data.STRef
import           Data.Sequence (Seq)
import qualified Data.Foldable                    as F
import qualified Data.List.NonEmpty               as L
import           Data.List.NonEmpty               (NonEmpty(..))
import           Data.Maybe                       (fromMaybe)

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..), (<$>))
#endif
import           Control.Monad
import           Control.Monad.ST
import           Control.Monad.Identity
import           Control.Monad.Trans.Maybe
import           Control.Monad.State.Strict
import qualified Data.IntMap                      as IM

import Data.Number.Nat     (fromNat, unsafeNat)
import Data.Number.Natural (fromNatural, fromNonNegativeRational, Natural, unsafeNatural)
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Types.Sing
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.TypeOf
import Language.Hakaru.Syntax.Value
import Language.Hakaru.Syntax.Reducer
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

updateEnvs
    :: List1 Variable xs
    -> List1 Value xs
    -> Env
    -> Env
updateEnvs Nil1         Nil1         env = env
updateEnvs (Cons1 x xs) (Cons1 y ys) env =
    updateEnvs xs ys (updateEnv (EAssoc x y) env)

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
    o :$          es -> evaluateSCon    o es    env
    NaryOp_  o    es -> evaluateNaryOp  o es    env
    Literal_ v       -> evaluateLiteral v
    Empty_   _       -> evaluateEmpty
    Array_   n    es -> evaluateArray   n es    env
    ArrayLiteral_ es -> VArray . V.fromList $ map (flip evaluate env) es
    Bucket b e    rs -> evaluateBucket  b e  rs env
    Datum_   d       -> evaluateDatum   d       env
    Case_    o    es -> evaluateCase    o es    env
    Superpose_    es -> evaluateSuperpose es    env
    Reject_  _       -> VMeasure $ \_ _ -> return Nothing

evaluateSCon
    :: (ABT Term abt)
    => SCon args a
    -> SArgs abt args
    -> Env
    -> Value a
evaluateSCon Lam_ (e1 :* End) env =
    caseBind e1 $ \x e1' ->
        VLam $ \v -> evaluate e1' (updateEnv (EAssoc x v) env)
evaluateSCon App_ (e1 :* e2 :* End) env =
    case evaluate e1 env of
    VLam f -> f (evaluate e2 env)
    v      -> case v of {}
evaluateSCon Let_ (e1 :* e2 :* End) env =
    let v = evaluate e1 env
    in caseBind e2 $ \x e2' ->
        evaluate e2' (updateEnv (EAssoc x v) env)
evaluateSCon (CoerceTo_   c) (e1 :* End) env =
    coerceTo c $ evaluate e1 env
evaluateSCon (UnsafeFrom_ c) (e1 :* End) env =
    coerceFrom c $ evaluate e1 env
evaluateSCon (PrimOp_ o)     es env = evaluatePrimOp    o es env
evaluateSCon (ArrayOp_ o)    es env = evaluateArrayOp   o es env
evaluateSCon (MeasureOp_  m) es env = evaluateMeasureOp m es env
evaluateSCon Dirac           (e1 :* End) env =
    VMeasure $ \p _ -> return $ Just (evaluate e1 env, p)
evaluateSCon MBind (e1 :* e2 :* End) env =
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

evaluateSCon Plate (n :* e2 :* End) env =
    case evaluate n env of
    VNat n' -> caseBind e2 $ \x e' ->
        VMeasure $ \(VProb p) g -> runMaybeT $ do
            (v', ps) <- fmap V.unzip . V.mapM (performMaybe g) $
                V.generate (fromInteger $ fromNatural n') $ \v ->
                    evaluate e' $
                    updateEnv (EAssoc x . VNat $ intToNatural v) env
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

evaluateSCon Chain (n :* s :* e :* End) env =
    case (evaluate n env, evaluate s env) of
    (VNat n', start) ->
        caseBind e $ \x e' ->
            let s' = VLam $ \v -> evaluate e' (updateEnv (EAssoc x v) env) in
            VMeasure (\(VProb p) g -> runMaybeT $ do
                (evaluates, sout) <- runStateT (replicateM (unsafeInt n') $ convert g s') start
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

evaluateSCon (Summate hd hs) (e1 :* e2 :* e3 :* End) env =
    case (evaluate e1 env, evaluate e2 env) of
    (lo, hi) ->
        caseBind e3 $ \x e3' ->
            foldl (\t i ->
                   evalOp (Sum  hs) t $
                     evaluate e3' (updateEnv (EAssoc x i) env))
                  (identityElement $ Sum hs)
                  (enumFromUntilValue hd lo hi)
    v                        -> case v of {}

evaluateSCon (Product hd hs) (e1 :* e2 :* e3 :* End) env =
    case (evaluate e1 env, evaluate e2 env) of
    (lo, hi) ->
        caseBind e3 $ \x e3' ->
            foldl (\t i ->
                   evalOp (Prod hs) t $
                     evaluate e3' (updateEnv (EAssoc x i) env))
                  (identityElement $ Prod hs)
                  (enumFromUntilValue hd lo hi)
    v                        -> case v of {}

evaluateSCon s _ _ = error $ "TODO: evaluateSCon{" ++ show s ++ "}"

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

evaluatePrimOp Choose (e1 :* e2 :* End) env =
    case (evaluate e1 env, evaluate e2 env) of
      (VNat v1, VNat v2) -> VNat $ EB.choose v1 v2
      v                    -> case v of {}
      
evaluatePrimOp Exp (e1 :* End) env =
    case evaluate e1 env of
      VReal v1 -> VProb . LF.logToLogFloat $ v1
      v        -> case v of {}

evaluatePrimOp Log (e1 :* End) env =
    case evaluate e1 env of
      VProb v1 -> VReal . LF.logFromLogFloat $ v1
      v        -> case v of {}

evaluatePrimOp (Infinity h) End _ =
    case h of
      HIntegrable_Nat  -> error "Can not evaluate infinity for natural numbers"
      HIntegrable_Prob -> VProb $ LF.logFloat LF.infinity

evaluatePrimOp (Equal et) (e1 :* e2 :* End) env = (VDatum . dBool) $ evaluate e1 env == evaluate e2 env

evaluatePrimOp (Less _) (e1 :* e2 :* End) env =
    case (evaluate e1 env, evaluate e2 env) of
    (VNat  v1, VNat  v2) -> VDatum $ if v1 < v2 then dTrue else dFalse
    (VInt  v1, VInt  v2) -> VDatum $ if v1 < v2 then dTrue else dFalse
    (VProb v1, VProb v2) -> VDatum $ if v1 < v2 then dTrue else dFalse
    (VReal v1, VReal v2) -> VDatum $ if v1 < v2 then dTrue else dFalse
    v                    -> error "TODO: evaluatePrimOp{Less}"
evaluatePrimOp (NatPow _) (e1 :* e2 :* End) env = 
    case evaluate e2 env of
    VNat  v2 ->
        let v2' = fromNatural v2 in
        case evaluate e1 env of
          VNat  v1 -> VNat  (v1 ^ v2')
          VInt  v1 -> VInt  (v1 ^ v2')
          VProb v1 -> VProb (v1 ^ v2')
          VReal v1 -> VReal (v1 ^ v2')
    v2       -> case v2 of {}
evaluatePrimOp (Negate _) (e1 :* End) env = 
    case evaluate e1 env of
    VInt  v -> VInt  (negate v)
    VReal v -> VReal (negate v)
    v       -> case v of {}
evaluatePrimOp (Abs   _) (e1 :* End) env =
    case evaluate e1 env of
    VInt  v -> VNat  . unsafeNatural   $ abs v
    VReal v -> VProb . LF.logFloat $ abs v
    v       -> case v of {}
evaluatePrimOp (Recip _) (e1 :* End) env = 
    case evaluate e1 env of
    VProb v -> VProb (recip v)
    VReal v -> VReal (recip v)
    v       -> case v of {}
evaluatePrimOp (NatRoot _) (e1 :* e2 :* End) env =
    case (evaluate e1 env, evaluate e2 env) of
    (VProb v1, VNat v2) -> VProb $ LF.pow v1 (recip . fromIntegral $ v2)
    v                   -> case v of {}    

evaluatePrimOp (Floor) (e1 :* End) env =
    case (evaluate e1 env) of
    VProb v1 -> VNat (floor (LF.fromLogFloat v1))
    v        -> case v of {}

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
evaluateArrayOp (Index _) = \(e1 :* e2 :* End) env ->
    case (evaluate e1 env, evaluate e2 env) of
    (VArray v, VNat n) -> v V.! unsafeInt n
    _                  -> error "evaluateArrayOp: the impossible happened"

evaluateArrayOp (Size _) = \(e1 :* End) env ->
    case evaluate e1 env of
    VArray v -> VNat . intToNatural $ V.length v
    _        -> error "evaluateArrayOp: the impossible happened"

evaluateArrayOp (Reduce _) = \(e1 :* e2 :* e3 :* End) env ->
    case ( evaluate e1 env
         , evaluate e2 env
         , evaluate e3 env) of
    (f, a, VArray v) -> V.foldl' (lam2 f) a v
    _                -> error "evaluateArrayOp: the impossible happened"

evaluateMeasureOp
    :: ( ABT Term abt
       , typs ~ UnLCs args
       , args ~ LCs typs)
    => MeasureOp typs a
    -> SArgs abt args
    -> Env
    -> Value ('HMeasure a)

evaluateMeasureOp Lebesgue = \(e1 :* e2 :* End) env ->
  case (evaluate e1 env, evaluate e2 env) of
    (VReal v1, VReal v2) | v1 < v2 ->
      VMeasure $ \(VProb p) g ->
        case (isInfinite v1, isInfinite v2) of
          (False, False) -> do
            x <- MWC.uniformR (v1, v2) g
            return $ Just (VReal $ x,
                           VProb $ p * LF.logFloat (v2 - v1))
          (False, True) -> do
            u <- MWC.uniform g
            let l = log u
            let n = -l
            return $ Just (VReal $ v1 + n,
                           VProb $ p * LF.logToLogFloat n)
          (True, False) -> do
            u <- MWC.uniform g
            let l = log u
            let n = -l
            return $ Just (VReal $ v2 - n,
                           VProb $ p * LF.logToLogFloat n)
          (True, True) -> do
            (u,b) <- MWC.uniform g
            let l = log u
            let n = -l
            return $ Just (VReal $ if b then n else l,
                           VProb $ p * 2 * LF.logToLogFloat n)

evaluateMeasureOp Counting = \End _ ->
    VMeasure $ \(VProb p) g -> do
        let success = LF.logToLogFloat (-3 :: Double)
        let pow x y = LF.logToLogFloat (LF.logFromLogFloat x *
                                       (fromIntegral y :: Double))
        u' <- MWCD.geometric0 (LF.fromLogFloat success) g
        let u = fromInteger u
        b <- MWC.uniform g
        return $ Just
            ( VInt  $ if b then -1-u else u
            , VProb $ p * 2 / pow (1-success) u / success)

evaluateMeasureOp Categorical = \(e1 :* End) env ->
    VMeasure $ \p g -> do
        let (_,y,ys) = normalizeVector (evaluate e1 env)
        if not (y > (0::Double)) -- TODO: why not use @y <= 0@ ??
        then error "Categorical needs positive weights"
        else do
            u <- MWC.uniformR (0, y) g
            return $ Just
                ( VNat
                . intToNatural
                . fromMaybe 0
                . V.findIndex (u <=) 
                . V.scanl1' (+)
                $ ys
                , p)

evaluateMeasureOp Uniform = \(e1 :* e2 :* End) env ->
    case (evaluate e1 env, evaluate e2 env) of
    (VReal v1, VReal v2) -> VMeasure $ \p g -> do
        x <- MWC.uniformR (v1, v2) g
        return $ Just (VReal x, p)
    _ -> error "evaluateMeasureOp: the impossible happened"

evaluateMeasureOp Normal = \(e1 :* e2 :* End) env ->
    case (evaluate e1 env, evaluate e2 env) of 
    (VReal v1, VProb v2) -> VMeasure $ \ p g -> do
        x <- MWCD.normal v1 (LF.fromLogFloat v2) g
        return $ Just (VReal x, p)
    _ -> error "evaluateMeasureOp: the impossible happened"

evaluateMeasureOp Poisson = \(e1 :* End) env ->
    case evaluate e1 env of
    VProb v1 -> VMeasure $ \ p g -> do
        x <- MWC.genFromTable (MWC.tablePoisson (LF.fromLogFloat v1)) g
        return $ Just (VNat $ intToNatural x, p)
    _ -> error "evaluateMeasureOp: the impossible happened"

evaluateMeasureOp Gamma = \(e1 :* e2 :* End) env ->
    case (evaluate e1 env, evaluate e2 env) of 
    (VProb v1, VProb v2) -> VMeasure $ \ p g -> do
        x <- MWCD.gamma (LF.fromLogFloat v1) (LF.fromLogFloat v2) g
        return $ Just (VProb $ LF.logFloat x, p)
    _ -> error "evaluateMeasureOp: the impossible happened"

evaluateMeasureOp Beta = \(e1 :* e2 :* End) env ->
    case (evaluate e1 env, evaluate e2 env) of 
    (VProb v1, VProb v2) -> VMeasure $ \ p g -> do
        x <- MWCD.beta (LF.fromLogFloat v1) (LF.fromLogFloat v2) g
        return $ Just (VProb $ LF.logFloat x, p)
    _ -> error "evaluateMeasureOp: the impossible happened"

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
identityElement (Max  HOrd_Prob)      = VProb 0
identityElement (Max  HOrd_Real)      = VReal LF.negativeInfinity
identityElement (Min  HOrd_Prob)      = VProb (LF.logFloat LF.infinity)
identityElement (Min  HOrd_Real)      = VReal LF.infinity


evalOp
    :: NaryOp a -> Value a -> Value a -> Value a
evalOp And (VDatum a) (VDatum b)        
    | a == dTrue && b == dTrue = VDatum dTrue
    | otherwise = VDatum dFalse
evalOp (Sum  HSemiring_Nat)  (VNat  a) (VNat  b) = VNat  (a + b)
evalOp (Sum  HSemiring_Int)  (VInt  a) (VInt  b) = VInt  (a + b)
evalOp (Sum  HSemiring_Prob) (VProb a) (VProb b) = VProb (a + b)
evalOp (Sum  HSemiring_Real) (VReal a) (VReal b) = VReal (a + b)
evalOp (Prod HSemiring_Nat)  (VNat  a) (VNat  b) = VNat  (a * b)
evalOp (Prod HSemiring_Int)  (VInt  a) (VInt  b) = VInt  (a * b)  
evalOp (Prod HSemiring_Prob) (VProb a) (VProb b) = VProb (a * b)  
evalOp (Prod HSemiring_Real) (VReal a) (VReal b) = VReal (a * b)
evalOp (Max  HOrd_Prob)      (VProb a) (VProb b) = VProb (max a b)
evalOp (Max  HOrd_Real)      (VReal a) (VReal b) = VReal (max a b)
evalOp (Min  HOrd_Prob)      (VProb a) (VProb b) = VProb (min a b) 
evalOp (Min  HOrd_Real)      (VReal a) (VReal b) = VReal (min a b) 

evalOp op                    _          _        =
    error ("TODO: evalOp{" ++ show op ++ "}")

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
        VArray $ V.generate (unsafeInt n') $ \v ->
            let v' = VNat $ intToNatural v in
            evaluate e' (updateEnv (EAssoc x v') env)

evaluateBucket
    :: (ABT Term abt)
    => abt '[] 'HNat
    -> abt '[] 'HNat
    -> Reducer abt '[] a
    -> Env
    -> Value a
evaluateBucket b e rs env =
    case (evaluate b env, evaluate e env) of
      (VNat b', VNat e') -> runST $ do
          s' <- init Nil1 rs env
          mapM_ (\i -> accum (VNat i) Nil1 rs s' env) [b' .. e' - 1]
          done s'
      v2                 -> case v2 of {}
    where init :: (ABT Term abt)
               => List1 Value xs
               -> Reducer abt xs a
               -> Env
               -> ST s (VReducer s a)
          init ix (Red_Fanout r1 r2)    env  =
              VRed_Pair (type_ r1) (type_ r2) <$> init ix r1 env <*> init ix r2 env
          init ix (Red_Index  n  _  mr) env  =
              let (vars, n') = caseBinds n in
              case evaluate n' (updateEnvs vars ix env) of
                VNat n'' -> VRed_Array <$> V.generateM (fromIntegral n'')
                            (\b -> init (Cons1 (vnat b) ix) mr env)
          init ix (Red_Split _ r1 r2)   env  =
              VRed_Pair (type_ r1) (type_ r2) <$> init ix r1 env <*> init ix r2 env
          init ix Red_Nop               env  = return VRed_Unit
          init ix (Red_Add h _) env = VRed_Num <$> newSTRef (identityElement (Sum h))

          type_ = typeOfReducer

          vnat :: Int -> Value 'HNat
          vnat  = VNat . fromIntegral

          accum :: (ABT Term abt)
                => Value 'HNat
                -> List1 Value xs
                -> Reducer abt xs a
                -> VReducer s a
                -> Env
                -> ST s ()
          accum n ix (Red_Fanout r1 r2)   (VRed_Pair s1 s2 v1 v2) env =
              accum n ix r1 v1 env >> accum n ix r2 v2 env
          accum n ix (Red_Index n' a1 r2) (VRed_Array v)          env =
              caseBind a1 $ \i a1' ->
              let (vars, a1'') = caseBinds a1'
                  VNat ov = evaluate a1''
                            (updateEnv (EAssoc i n) (updateEnvs vars ix env))
                  ov' = fromIntegral ov in
              accum n (Cons1 (VNat ov) ix) r2 (v V.! ov') env
          accum n ix (Red_Split b  r1 r2) (VRed_Pair s1 s2 v1 v2) env =
              caseBind b $ \i b' ->
                  let (vars, b'') = caseBinds b' in
                  case evaluate b''
                       (updateEnv (EAssoc i n) (updateEnvs vars ix env)) of
                  VDatum b' -> if b' == dTrue then
                                   accum n ix r1 v1 env
                               else
                                   accum n ix r2 v2 env
          accum n ix (Red_Add h e) (VRed_Num s) env =
              caseBind e $ \i e' ->
                  let (vars, e'') = caseBinds e'
                      v = evaluate e''
                          (updateEnv (EAssoc i n) (updateEnvs vars ix env)) in
                  modifySTRef' s (evalOp (Sum h) v)
          accum _ _ Red_Nop _ _ = return ()

          done :: VReducer s a -> ST s (Value a)
          done (VRed_Num s)            = readSTRef s
          done VRed_Unit               = return (VDatum dUnit)
          done (VRed_Pair s1 s2 v1 v2) = do
            v1' <- done v1
            v2' <- done v2
            return (VDatum $ dPair_ s1 s2 v1' v2')
          done (VRed_Array v)          = VArray <$> V.sequence (V.map done v)

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
    Just (Matched rho b) ->
        evaluate b (extendFromMatch (fromAssocs rho) env)
    _ -> error "Missing cases in match expression"
    where
    extendFromMatch :: [Assoc Value] -> Env -> Env
    extendFromMatch []                env' = env'
    extendFromMatch (Assoc x v : xvs) env' =
        extendFromMatch xvs (updateEnv (EAssoc x v) env')

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

-- Useful 'short-hand'
intToNatural :: Int -> Natural
intToNatural = unsafeNatural . toInteger

unsafeInt :: Natural -> Int
unsafeInt = fromInteger . fromNatural
----------------------------------------------------------- fin.
