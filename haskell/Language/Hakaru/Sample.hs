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
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.Value
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.DatumCase
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT

data EAssoc
    = forall a. EAssoc {-# UNPACK #-} !(Variable a) !(Value a)

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

evaluate :: forall abt a
         .  (ABT Term abt)
         => abt '[] a
         -> Env
         -> Value a
evaluate e env = caseVarSyn e (evaluateVar env) (flip evaluateTerm env)

evaluateVar :: Env -> Variable a -> Value a
evaluateVar env v =
    case lookupVar v env of
    Nothing -> error "variable not found!"
    Just a  -> a

evaluateTerm :: forall abt a
             .  (ABT Term abt)
             => Term abt a
             -> Env
             -> Value a
evaluateTerm t env =
    case t of
    o :$ es       -> evaluateScon    o es env
    NaryOp_  o es -> evaluateNaryOp  o es env
    Literal_ v    -> evaluateLiteral v
    Datum_   d    -> evaluateDatum   d env
    Case_    o es -> evaluateCase    o es env
    Superpose_ es -> evaluateSuperpose es env

evaluateScon
    :: (ABT Term abt)
    => SCon args a
    -> SArgs abt args
    -> Env
    -> Value a
evaluateScon Lam_ (e1 :* End)            env =
    caseBind e1 $ \x e1' ->
        VLam $ \v -> evaluate e1' (updateEnv (EAssoc x v) env)
evaluateScon App_ (e1 :* e2 :* End)      env =
    case evaluate e1 env of
      VLam f -> f (evaluate e2 env)
      v      -> case v of {}
evaluateScon Let_ (e1 :* e2 :* End)      env =
    let v = evaluate e1 env
    in caseBind e2 $ \x e2' ->
        evaluate e2' (updateEnv (EAssoc x v) env)
evaluateScon (Ann_   _)      (e1 :* End) env = evaluate e1 env
evaluateScon (CoerceTo_   c) (e1 :* End) env =
    coerceTo c $ evaluate e1 env
evaluateScon (UnsafeFrom_ c) (e1 :* End) env =
    coerceFrom c $ evaluate e1 env
evaluateScon (PrimOp_ o)     es env = evaluatePrimOp    o es env
evaluateScon (MeasureOp_  m) es env = evaluateMeasureOp m es env
evaluateScon Dirac           (e1 :* End) env =
    VMeasure $ \p _ -> return $ Just (evaluate e1 env, p)
evaluateScon MBind (e1 :* e2 :* End) env =
    case evaluate e1 env of
      VMeasure m1 ->
        VMeasure $ \ p g -> do
          x <- m1 p g
          case x of
            Nothing -> return Nothing
            Just (a, p') ->
               caseBind e2 $ \x' e2' ->
                   case evaluate e2' (updateEnv (EAssoc x' a) env) of
                     VMeasure y -> y p' g
                     v -> case v of {}
      v -> case v of {}

evaluatePrimOp
    ::  ( ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => PrimOp typs a
    -> SArgs abt args
    -> Env
    -> Value a
evaluatePrimOp Infinity         End _ = VProb $ LF.logFloat (1/0)
evaluatePrimOp NegativeInfinity End _ = VReal $ -1/0
evaluatePrimOp (Negate _) (e1 :* End) env = 
    case evaluate e1 env of
      VInt  v -> VInt  (negate v)
      VReal v -> VReal (negate v)
      v       -> case v of {}


evaluateNaryOp
    :: (ABT Term abt)
    => NaryOp a -> Seq (abt '[] a) -> Env -> Value a
evaluateNaryOp s es = F.foldr (evalOp s) (identityElement s) . mapEvaluate es

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
        return $ Just ( if b
                        then VReal n
                        else VReal l
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

evaluateMeasureOp (DirichletProcess _) _ _ =
    error "evaluateMeasureOp: Dirichlet Processes not implemented yet"

evaluateMeasureOp (Plate _) (e1 :* End) env =
    case evaluate e1 env of
        VArray a -> VMeasure $ \(VProb p) g -> runMaybeT $ do
          evaluates <- V.mapM (performMaybe g) a
          let (v', ps) = V.unzip evaluates
          return ( VArray v'
                 , VProb $ p * V.product (V.map (\(VProb x) -> x) ps)
                 )
        v -> case v of {}

  where performMaybe
            :: MWC.GenIO
            -> Value ('HMeasure a)
            -> MaybeT IO (Value a, Value 'HProb)
        performMaybe g (VMeasure m) = MaybeT $ m (VProb 1) g

evaluateMeasureOp (Chain _ _) (e1 :* e2 :* End) env =
    case (evaluate e1 env, evaluate e2 env) of
        (VArray v, s) -> VMeasure (\(VProb p) g -> runMaybeT $ do
             (evaluates, sout) <- runStateT (V.mapM (convert g) v) s
             let (v', ps) = V.unzip evaluates
             return ( VDatum $ dPair (VArray v') sout
                    , VProb $ p * V.product (V.map (\(VProb x) -> x) ps)
                    ))
        v -> case v of {}

   where convert :: MWC.GenIO
                 -> Value (s ':-> 'HMeasure (HPair a s))
                 -> StateT (Value s) (MaybeT IO) (Value a, Value 'HProb)
         convert g (VLam f) =
             StateT $ \s' ->
              case f s' of
                   VMeasure f' -> do
                       (as'',p') <- MaybeT (f' (VProb 1) g)
                       let (a, s'') = unPair as''
                       return ((a,p'),s'')
                   v -> case v of {}

         unPair :: Value (HPair a b) -> (Value a, Value b)
         unPair (VDatum (Datum "pair"
                         (Inl (Et (Konst a)
                               (Et (Konst b) Done))))) =
             (a, b)
         unPair x = case x of {}

evaluateLiteral :: Literal a -> Value a
evaluateLiteral (LNat  n) = VNat  . fromInteger $ fromNatural n -- TODO: catch overflow errors
evaluateLiteral (LInt  n) = VInt  $ fromInteger n -- TODO: catch overflow errors
evaluateLiteral (LProb n) = VProb . fromRational $ fromNonNegativeRational n
evaluateLiteral (LReal n) = VReal $ fromRational n

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
    => [(abt '[] 'HProb, abt '[] ('HMeasure a))]
    -> Env
    -> Value ('HMeasure a)
evaluateSuperpose []       _   = VMeasure $ \_ _ -> return Nothing
evaluateSuperpose [(q, m)] env =
    case evaluate m env of
         VMeasure m' ->
             let VProb q' = evaluate q env
             in  VMeasure (\(VProb p) g -> m' (VProb $ p * q') g)
        
evaluateSuperpose pms@((_, m) : _) env =
    case evaluate m env of
      VMeasure m' ->
          let weights  = map ((flip evaluate env) . fst) pms
              (x,y,ys) = normalize weights
          in VMeasure $ \(VProb p) g ->
              if not (y > (0::Double)) then return Nothing else do
                  u <- MWC.uniformR (0, y) g
                  case [ m1 | (v,(_,m1)) <- zip (scanl1 (+) ys) pms, u <= v ] of
                    m2 : _ ->
                        case evaluate m2 env of
                          VMeasure m2' -> m2' (VProb $ p * x * LF.logFloat y) g
                    []     -> m' (VProb $ p * x * LF.logFloat y) g

---------------------------------------------------------------------------------
---------------------------------------------------------------------------- fin.
