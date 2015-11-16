{-# LANGUAGE CPP
           , GADTs
           , EmptyCase
           , DataKinds
           , KindSignatures
           , MultiParamTypeClasses
           , FunctionalDependencies
           , ScopedTypeVariables
           , FlexibleContexts
           , RankNTypes
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.11.15
-- |
-- Module      :  Language.Hakaru.Lazy
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Lazy partial evaluation.
--
-- BUG: completely gave up on structure sharing. Need to add that back in.
----------------------------------------------------------------
module Language.Hakaru.Lazy
    (
    -- * Lazy partial evaluation
      MeasureEvaluator
    , TermEvaluator
    , evaluate
    , perform
    -- ** Helper functions
    , update
    ) where

import           Prelude hiding (id, (.))
import           Control.Category     (Category(..))
import           Data.Sequence        (Seq)
import qualified Data.Sequence        as Seq
import qualified Data.Text            as Text
import           Data.Number.LogFloat (LogFloat)
#if __GLASGOW_HASKELL__ < 710
import           Data.Functor         ((<$>))
#endif

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.HClasses
import Language.Hakaru.Syntax.Nat
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.TypeOf
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.DatumCase
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.Coercion
import Language.Hakaru.Lazy.Types
import qualified Language.Hakaru.Syntax.Prelude as P
import qualified Language.Hakaru.Expect         as E

----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: (eventually) accept an argument dictating the evaluation
-- strategy (HNF, WHNF, full-beta NF,...). The strategy value should
-- probably be a family of singletons, where the type-level strategy
-- @s@ is also an index on the 'Context' and (the renamed) 'Whnf'.
-- That way we don't need to define a bunch of variant 'Context',
-- 'Statement', and 'Whnf' data types; but rather can use indexing
-- to select out subtypes of the generic versions.


-- | A function for \"performing\" an 'HMeasure' monadic action.
-- This could mean actual random sampling, or simulated sampling
-- by generating a new term and returning the newly bound variable,
-- or anything else.
type MeasureEvaluator abt m =
    forall a. abt '[] ('HMeasure a) -> m (Whnf abt a)


-- | A function for evaluating any term to weak-head normal form.
type TermEvaluator abt m =
    forall a. abt '[] a -> m (Whnf abt a)


-- | Lazy partial evaluation with a given \"perform\" function.
evaluate
    :: forall abt m
    .  (ABT AST abt, EvaluationMonad abt m)
    => MeasureEvaluator abt m
    -> TermEvaluator    abt m
evaluate perform = evaluate_
    where
    -- TODO: At present, whenever we residualize a case expression we'll
    -- generate a 'Neutral' term which will, when run, repeat the work
    -- we're doing in the evaluation here. We could eliminate this
    -- redundancy by introducing a new variable for @e@ each time this
    -- function is called--- if only we had some way of getting those
    -- variables put into the right place for when we residualize the
    -- original scrutinee...
    --
    -- N.B., 'DatumEvaluator' is a rank-2 type so it requires a signature
    evaluateDatum :: DatumEvaluator abt m
    evaluateDatum e = viewWhnfDatum <$> evaluate_ e

    evaluate_ :: TermEvaluator abt m
    evaluate_ e0 =
      caseVarSyn e0 (update perform evaluate_) $ \t ->
        case t of
        -- Things which are already WHNFs
        Value_ v                 -> return . Head_ $ WValue v
        Datum_ d                 -> return . Head_ $ WDatum d
        Empty_                   -> return . Head_ $ WEmpty
        Array_ e1 e2             -> return . Head_ $ WArray e1 e2
        Lam_  :$ e1 :* End       -> return . Head_ $ WLam   e1
        Dirac :$ e1 :* End       -> return . Head_ $ WDirac e1
        MBind :$ e1 :* e2 :* End -> return . Head_ $ WMBind e1 e2
        MeasureOp_ o :$ es       -> return . Head_ $ WMeasureOp o es
        Superpose_ pes           -> return . Head_ $ WSuperpose pes


        -- Everything else needs some evaluation

        App_ :$ e1 :* e2 :* End -> do
            w1 <- evaluate_ e1
            case w1 of
                Neutral e1'    -> return . Neutral $ P.app e1' e2
                Head_ (WLam f) ->
                    caseBind f $ \x f' ->
                        push (SLet x $ Thunk e2) f' evaluate_
                _ -> error "evaluate: the impossible happened"

        Let_ :$ e1 :* e2 :* End ->
            caseBind e2 $ \x e2' ->
                push (SLet x $ Thunk e1) e2' evaluate_

        -- TODO: should prolly count as already a WHNF?
        Fix_ :$ e1 :* End -> error "TODO: evaluate{Fix_}"

        Ann_      typ :$ e1 :* End -> ann      typ <$> evaluate_ e1
        CoerceTo_   c :$ e1 :* End -> coerceTo   c <$> evaluate_ e1
        UnsafeFrom_ c :$ e1 :* End -> unsafeFrom c <$> evaluate_ e1

        -- TODO: will maybe clean up the code to map 'evaluate' over @es@ before calling the evaluateFooOp helpers?
        NaryOp_ o    es -> evaluateNaryOp evaluate_ o es
        PrimOp_ o :$ es -> evaluatePrimOp o es

        -- BUG: avoid the chance of looping in case 'E.expect' residualizes!
        -- TODO: use 'evaluate' in 'E.expect' for the evaluation of @e1@
        Expect :$ e1 :* e2 :* End ->
            evaluate_ . E.expect e1 $ \e3 ->
                syn (Let_ :$ e3 :* e2 :* End)

        Lub_ es -> error "TODO: evaluate{Lub_}" -- (Head_ . HLub) <$> T.for es evaluate_

        -- TODO: rather than throwing a Haskell error, instead
        -- capture the possibility of failure in the 'EvaluationMonad'
        -- monad.
        Case_ e bs -> do
            match <- matchBranches evaluateDatum e bs
            case match of
                Nothing ->
                    -- TODO: print more info about where this happened
                    error "evaluate: non-exhaustive patterns in case!"
                Just (GotStuck, _) ->
                    return . Neutral . syn $ Case_ e bs
                Just (Matched ss Nil1, body) ->
                    pushes (toStatements ss) body evaluate_

        -- HACK: these cases are impossible, and ghc can confirm
        -- that (via no warnings about the empty case analysis being
        -- incomplete), but ghc can't infer it for some reason
        _ :$ es -> case es of {}


type DList a = [a] -> [a]

toStatements :: DList (Assoc abt) -> [Statement abt]
toStatements ss = map (\(Assoc x e) -> SLet x $ Thunk e) (ss [])


----------------------------------------------------------------
-- TODO: figure out how to abstract this so it can be reused by
-- 'constrainValue'. Especially the 'SBranch case of 'step'
--
-- TODO: we could speed up the case for free variables by having
-- the 'Context' also keep track of the largest free var. That way,
-- we can just check up front whether @varID x < nextFreeVarID@.
-- Of course, we'd have to make sure we've sufficiently renamed all
-- bound variables to be above @nextFreeVarID@; but then we have to
-- do that anyways.
update
    :: (ABT AST abt, EvaluationMonad abt m)
    => MeasureEvaluator abt m
    -> TermEvaluator    abt m
    -> Variable a
    -> m (Whnf abt a)
update perform evaluate_ = \x ->
    -- If we get 'Nothing', then it turns out @x@ is a free variable
    fmap (maybe (Neutral $ var x) id) . select x $ \s ->
        case s of
        SBind y e -> do
            Refl <- varEq x y
            Just $ do
                w <- perform $ caseLazy e fromWhnf id
                unsafePush (SLet x $ Whnf_ w)
                return w
        SLet y e -> do
            Refl <- varEq x y
            Just $ do
                w <- caseLazy e return evaluate_
                unsafePush (SLet x $ Whnf_ w)
                return w
        SWeight _ -> Nothing


----------------------------------------------------------------
-- if not @mustCheck (fromWhnf w1)@, then could in principle eliminate the annotation; though it might be here so that it'll actually get pushed down to somewhere it's needed later on, so it's best to play it safe and leave it in.
ann :: (ABT AST abt) => Sing a -> Whnf abt a -> Whnf abt a
ann typ (Neutral e) = Neutral $ syn (Ann_ typ :$ e :* End)
ann typ (Head_   v) = Head_   $ WAnn typ v

-- TODO: cancellation; constant coercion
-- TODO: better unify the two cases of Whnf
coerceTo :: (ABT AST abt) => Coercion a b -> Whnf abt a -> Whnf abt b
coerceTo c w =
    case w of
    Neutral e ->
        Neutral . maybe (P.coerceTo_ c e) id
            $ caseVarSyn e (const Nothing) $ \t ->
                case t of
                -- UnsafeFrom_ c' :$ es' -> TODO: cancellation
                CoerceTo_ c' :$ es' ->
                    case es' of
                    e' :* End -> Just $ P.coerceTo_ (c . c') e'
                    _         -> error "coerceTo: the impossible happened"
                _ -> Nothing
    Head_ v ->
        case v of
        -- WUnsafeFrom c' v' -> TODO: cancellation
        WCoerceTo c' v' -> Head_ $ WCoerceTo (c . c') v'
        _               -> Head_ $ WCoerceTo c v


unsafeFrom :: (ABT AST abt) => Coercion a b -> Whnf abt b -> Whnf abt a
unsafeFrom c w =
    case w of
    Neutral e ->
        Neutral . maybe (P.unsafeFrom_ c e) id
            $ caseVarSyn e (const Nothing) $ \t ->
                case t of
                -- CoerceTo_ c' :$ es' -> TODO: cancellation
                UnsafeFrom_ c' :$ es' ->
                    case es' of
                    e' :* End -> Just $ P.unsafeFrom_ (c' . c) e'
                    _         -> error "unsafeFrom: the impossible happened"
                _ -> Nothing
    Head_ v ->
        case v of
        -- WCoerceTo c' v' -> TODO: cancellation
        WUnsafeFrom c' v' -> Head_ $ WUnsafeFrom (c' . c) v'
        _                 -> Head_ $ WUnsafeFrom c v


----------------------------------------------------------------
-- BUG: need to improve the types so they can capture polymorphic data types
-- BUG: this is a gross hack. If we can avoid it, we should!!!
class Interp a a' | a -> a' where
    reify   :: (ABT AST abt) => Head abt a -> a'
    reflect :: (ABT AST abt) => a' -> Head abt a

instance Interp 'HNat Nat where
    reify (WValue (VNat n)) = n
    reify (WAnn        _ v) = reify v
    reify (WCoerceTo   _ _) = error "TODO: reify{WCoerceTo}"
    reify (WUnsafeFrom _ _) = error "TODO: reify{WUnsafeFrom}"
    reflect = WValue . VNat

instance Interp 'HInt Int where
    reify (WValue (VInt i)) = i
    reify (WAnn        _ v) = reify v
    reify (WCoerceTo   _ _) = error "TODO: reify{WCoerceTo}"
    reify (WUnsafeFrom _ _) = error "TODO: reify{WUnsafeFrom}"
    reflect = WValue . VInt

instance Interp 'HProb LogFloat where -- TODO: use rational instead
    reify (WValue (VProb p)) = p
    reify (WAnn        _ v) = reify v
    reify (WCoerceTo   _ _) = error "TODO: reify{WCoerceTo}"
    reify (WUnsafeFrom _ _) = error "TODO: reify{WUnsafeFrom}"
    reflect = WValue . VProb

instance Interp 'HReal Double where -- TODO: use rational instead
    reify (WValue (VReal r)) = r
    reify (WAnn        _ v) = reify v
    reify (WCoerceTo   _ _) = error "TODO: reify{WCoerceTo}"
    reify (WUnsafeFrom _ _) = error "TODO: reify{WUnsafeFrom}"
    reflect = WValue . VReal

{-
identifyDatum :: (ABT AST abt) => DatumEvaluator abt Identity
identifyDatum = return . viewWhnfDatum

foo = ...like viewWhnfDatum but with the type of fromWhnf...

instance Interp HUnit () where
    reflect () = WValue $ VDatum dUnit
    reify w = runIdentity $ do
        match <- matchTopPattern identifyDatum (foo w) pUnit Nil1
        case match of
            Just (Matched _ss Nil1) -> return ()
            _ -> error "reify{HUnit}: the impossible happened"

instance Interp HBool Bool where
    reflect = WValue . VDatum . (\b -> if b then dTrue else dFalse)
    reify w = runIdentity $ do
        match <- matchTopPattern identifyDatum (foo w) pTrue Nil1
        case match of
            Just (Matched _ss Nil1) -> return True
            match <- matchTopPattern identifyDatum (foo w) pFalse Nil1
            case match of
                Just (Matched _ss Nil1) -> return False
                _ -> error "reify{HBool}: the impossible happened"

instance (Interp a a', Interp b b')
    => Interp (HPair a b) (a',b')
    where
    reflect (a,b) = P.pair a b
    reify w = runIdentity $ do
        match <- matchTopPattern identifyDatum (foo w) (pPair PVar PVar) (Cons1 x (Cons1 y Nil1))
        case match of
            Just (Matched ss Nil1) ->
                case xs [] of
                [Assoc _x e1, Assoc _y e2] -> return (reify e1, reify e2)
                _ -> error "reify{HPair}: the impossible happened"
            _ -> error "reify{HPair}: the impossible happened"

instance (Interp a a', Interp b b')
    => Interp (HEither a b) (Either a' b')
    where
    reflect (Left  a) = P.left  a
    reflect (Right b) = P.right b
    reify =

instance (Interp a a') => Interp (HMaybe a) (Maybe a') where
    reflect Nothing  = P.nothing
    reflect (Just a) = P.just a
    reify =

instance (Interp a a') => Interp (HList a) [a'] where
    reflect []     = P.nil
    reflect (x:xs) = P.cons x xs
    reify =
-}


rr1 :: (ABT AST abt, EvaluationMonad abt m, Interp a a', Interp b b')
    => (a' -> b')
    -> (abt '[] a -> abt '[] b)
    -> abt '[] a
    -> m (Whnf abt b)
rr1 f' f e = do
    w <- evaluate (error "TODO: thread 'perform' through to 'rr1'") e
    return $
        case w of
        Neutral e' -> Neutral $ f e'
        Head_   v  -> Head_ . reflect $ f' (reify v)


rr2 :: ( ABT AST abt, EvaluationMonad abt m
       , Interp a a', Interp b b', Interp c c')
    => (a' -> b' -> c')
    -> (abt '[] a -> abt '[] b -> abt '[] c)
    -> abt '[] a
    -> abt '[] b
    -> m (Whnf abt c)
rr2 f' f e1 e2 = do
    w1 <- evaluate (error "TODO: thread 'perform' through to 'rr2'") e1
    w2 <- evaluate (error "TODO: thread 'perform' through to 'rr2'") e2
    return $
        case w1 of
        Neutral e1' -> Neutral $ f e1' (fromWhnf w2)
        Head_   v1  ->
            case w2 of
            Neutral e2' -> Neutral $ f (fromWhnf w1) e2'
            Head_   v2  -> Head_ . reflect $ f' (reify v1) (reify v2)


impl, diff, nand, nor :: Bool -> Bool -> Bool
impl x y = not x || y
diff x y = x && not y
nand x y = not (x && y)
nor  x y = not (x || y)

natRoot :: (Floating a) => a -> Nat -> a
natRoot x y = x ** recip (fromIntegral (fromNat y))


----------------------------------------------------------------
evaluateNaryOp
    :: (ABT AST abt, EvaluationMonad abt m)
    => TermEvaluator abt m
    -> NaryOp a
    -> Seq (abt '[] a)
    -> m (Whnf abt a)
evaluateNaryOp evaluate_ = \o es -> mainLoop o (evalOp o) Seq.empty es
    where
    -- TODO: there's got to be a more efficient way to do this...
    mainLoop o op ws es =
        case Seq.viewl es of
        Seq.EmptyL   -> return $
            case Seq.viewl ws of
            Seq.EmptyL         -> identityElement o
            w Seq.:< ws'
                | Seq.null ws' -> w -- Avoid singleton naryOps
                | otherwise    ->
                    Neutral . syn . NaryOp_ o $ fmap fromWhnf ws
        e Seq.:< es' -> do
            w <- evaluate_ e
            case matchNaryOp o w of
                Nothing  -> mainLoop o op (snocLoop op ws w) es'
                Just es2 -> mainLoop o op ws (es2 Seq.>< es')

    snocLoop
        :: (ABT syn abt)
        => (Head abt a -> Head abt a -> Head abt a)
        -> Seq (Whnf abt a)
        -> Whnf abt a
        -> Seq (Whnf abt a)
    snocLoop op ws w1 =
        case Seq.viewr ws of
        Seq.EmptyR    -> Seq.singleton w1
        ws' Seq.:> w2 ->
            case (w1,w2) of
            (Head_ v1, Head_ v2) -> snocLoop op ws' (Head_ (op v1 v2))
            _                    -> ws Seq.|> w1

    matchNaryOp
        :: (ABT AST abt)
        => NaryOp a
        -> Whnf abt a
        -> Maybe (Seq (abt '[] a))
    matchNaryOp o w =
        case w of
        Head_   _ -> Nothing
        Neutral e ->
            caseVarSyn e (const Nothing) $ \t ->
                case t of
                NaryOp_ o' es | o' == o -> Just es
                _                       -> Nothing

    -- TODO: move this off to Prelude.hs or somewhere...
    identityElement :: (ABT AST abt) => NaryOp a -> Whnf abt a
    identityElement o =
        case o of
        And    -> Head_ (WDatum dTrue)
        Or     -> Head_ (WDatum dFalse)
        Xor    -> Head_ (WDatum dFalse)
        Iff    -> Head_ (WDatum dTrue)
        Min  _ -> Neutral (syn (NaryOp_ o Seq.empty)) -- no identity in general (but we could do it by cases...)
        Max  _ -> Neutral (syn (NaryOp_ o Seq.empty)) -- no identity in general (but we could do it by cases...)
        -- TODO: figure out how to reuse 'P.zero' and 'P.one' here
        Sum  HSemiring_Nat  -> Head_ (WValue (VNat  0))
        Sum  HSemiring_Int  -> Head_ (WValue (VInt  0))
        Sum  HSemiring_Prob -> Head_ (WValue (VProb 0))
        Sum  HSemiring_Real -> Head_ (WValue (VReal 0))
        Prod HSemiring_Nat  -> Head_ (WValue (VNat  1))
        Prod HSemiring_Int  -> Head_ (WValue (VInt  1))
        Prod HSemiring_Prob -> Head_ (WValue (VProb 1))
        Prod HSemiring_Real -> Head_ (WValue (VReal 1))

    -- | The evaluation interpretation of each NaryOp
    evalOp :: NaryOp a -> Head abt a -> Head abt a -> Head abt a
    {-
    evalOp And      v1 v2 = reflect (reify v1 && reify v2)
    evalOp Or       v1 v2 = reflect (reify v1 || reify v2)
    evalOp Xor      v1 v2 = reflect (reify v1 /= reify v2)
    evalOp Iff      v1 v2 = reflect (reify v1 == reify v2)
    evalOp (Min  _) v1 v2 = reflect (reify v1 `min` reify v2)
    evalOp (Max  _) v1 v2 = reflect (reify v1 `max` reify v2)
    evalOp (Sum  _) v1 v2 = reflect (reify v1 + reify v2)
    evalOp (Prod _) v1 v2 = reflect (reify v1 * reify v2)
    -}
    -- HACK: this is just to have something to test. We really should reduce\/remove all this boilerplate...
    evalOp (Sum  s) (WValue v1) (WValue v2) = WValue $ evalSum  s v1 v2
    evalOp (Prod s) (WValue v1) (WValue v2) = WValue $ evalProd s v1 v2
    evalOp (Sum  _) _ _ = error "evalOp{Sum}: the impossible happened"
    evalOp (Prod _) _ _ = error "evalOp{Prod}: the impossible happened"
    evalOp _ _ _ = error "TODO: evalOp{HBool ops, HOrd ops}"

    evalSum, evalProd :: HSemiring a -> Value a -> Value a -> Value a
    evalSum  HSemiring_Nat  (VNat  n1) (VNat  n2) = VNat  (n1 + n2)
    evalSum  HSemiring_Int  (VInt  i1) (VInt  i2) = VInt  (i1 + i2)
    evalSum  HSemiring_Prob (VProb p1) (VProb p2) = VProb (p1 + p2)
    evalSum  HSemiring_Real (VReal r1) (VReal r2) = VReal (r1 + r2)
    evalSum  s _ _ = case s of {}
    evalProd HSemiring_Nat  (VNat  n1) (VNat  n2) = VNat  (n1 * n2)
    evalProd HSemiring_Int  (VInt  i1) (VInt  i2) = VInt  (i1 * i2)
    evalProd HSemiring_Prob (VProb p1) (VProb p2) = VProb (p1 * p2)
    evalProd HSemiring_Real (VReal r1) (VReal r2) = VReal (r1 * r2)
    evalProd s _ _ = case s of {}


----------------------------------------------------------------
evaluatePrimOp
    :: ( ABT AST abt, EvaluationMonad abt m
       , typs ~ UnLCs args, args ~ LCs typs)
    => PrimOp typs a
    -> SArgs abt args
    -> m (Whnf abt a)
{-
evaluatePrimOp Not  (e1 :* End)       = rr1 not  P.not  e1
evaluatePrimOp Impl (e1 :* e2 :* End) = rr2 impl P.impl e1 e2
evaluatePrimOp Diff (e1 :* e2 :* End) = rr2 diff P.diff e1 e2
evaluatePrimOp Nand (e1 :* e2 :* End) = rr2 nand P.nand e1 e2
evaluatePrimOp Nor  (e1 :* e2 :* End) = rr2 nor  P.nor  e1 e2
-- TODO: all our magic constants (Pi, Infty,...) should be bundled together under one AST constructor called something like @Constant@; that way we can group them in the 'Head' like we do for values.
evaluatePrimOp Pi        End               = return (Head_ HPi)
-}
evaluatePrimOp Sin       (e1 :* End)       = rr1 sin   P.sin   e1
evaluatePrimOp Cos       (e1 :* End)       = rr1 cos   P.cos   e1
evaluatePrimOp Tan       (e1 :* End)       = rr1 tan   P.tan   e1
evaluatePrimOp Asin      (e1 :* End)       = rr1 asin  P.asin  e1
evaluatePrimOp Acos      (e1 :* End)       = rr1 acos  P.acos  e1
evaluatePrimOp Atan      (e1 :* End)       = rr1 atan  P.atan  e1
evaluatePrimOp Sinh      (e1 :* End)       = rr1 sinh  P.sinh  e1
evaluatePrimOp Cosh      (e1 :* End)       = rr1 cosh  P.cosh  e1
evaluatePrimOp Tanh      (e1 :* End)       = rr1 tanh  P.tanh  e1
evaluatePrimOp Asinh     (e1 :* End)       = rr1 asinh P.asinh e1
evaluatePrimOp Acosh     (e1 :* End)       = rr1 acosh P.acosh e1
evaluatePrimOp Atanh     (e1 :* End)       = rr1 atanh P.atanh e1
{-
evaluatePrimOp RealPow   (e1 :* e2 :* End) = rr2 (**) (P.**) e1 e2
evaluatePrimOp Exp       (e1 :* End)       = rr1 exp   P.exp e1 -- TODO: types
evaluatePrimOp Log       (e1 :* End)       = rr1 log   P.log e1 -- TODO: types
evaluatePrimOp Infinity         End        = return (Head_ HInfinity)
evaluatePrimOp NegativeInfinity End        = return (Head_ HNegativeInfinity)
evaluatePrimOp GammaFunc   (e1 :* End)             =
evaluatePrimOp BetaFunc    (e1 :* e2 :* End)       =
evaluatePrimOp Integrate   (e1 :* e2 :* e3 :* End) =
evaluatePrimOp Summate     (e1 :* e2 :* e3 :* End) =
{-
evaluateArrayOp (Index   _) (e1 :* e2 :* End)       =
evaluateArrayOp (Size    _) (e1 :* End)             =
evaluateArrayOp (Reduce  _) (e1 :* e2 :* e3 :* End) =
-}
evaluatePrimOp (Equal   _) (e1 :* e2 :* End) = rr2 (==)    (P.==) e1 e2
evaluatePrimOp (Less    _) (e1 :* e2 :* End) = rr2 (<)     (P.<)  e1 e2
evaluatePrimOp (NatPow  _) (e1 :* e2 :* End) = rr2 (^^)    (P.^^) e1 e2
evaluatePrimOp (Negate  _) (e1 :* End)       = rr1 negate  P.negate e1
evaluatePrimOp (Abs     _) (e1 :* End)       = rr1 abs     P.abs_   e1 -- TODO: types
evaluatePrimOp (Signum  _) (e1 :* End)       = rr1 signum  P.signum e1
evaluatePrimOp (Recip   _) (e1 :* End)       = rr1 recip   P.recip  e1
evaluatePrimOp (NatRoot _) (e1 :* e2 :* End) = rr2 natRoot _ e1 e2
evaluatePrimOp (Erf     _) (e1 :* End)       = rr1 erf     P.erf    e1
-}
evaluatePrimOp _ _ = error "TODO: finish evaluatePrimOp"


----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: 'perform' should move to Disintegrate.hs

-- N.B., that return type is correct, albeit strange. The idea is that the continuation takes in the variable of type @a@ bound by the expression of type @'HMeasure a@. However, this requires that the continuation of the 'Ans' type actually does @forall a. ...('HMeasure a)@ which is at odds with what 'evaluate' wants (or at least, what *I* think it should want.)
perform :: (ABT AST abt) => MeasureEvaluator abt (M abt)
perform e0 =
    caseVarSyn e0 (error "TODO: perform{Var}") $ \t ->
        case t of
        Dirac :$ e1 :* End       -> evaluate perform e1
        MeasureOp_ _ :$ _        -> mbindTheContinuation e0
        MBind :$ e1 :* e2 :* End ->
            caseBind e2 $ \x e2' ->
                push (SBind x $ Thunk e1) e2' perform
        Superpose_ es ->
            error "TODO: perform{Superpose_}"
            {-
            P.superpose <$> T.traverse perform es -- TODO: not quite right; need to push the SWeight in each branch. Also, 'Whnf' un\/wrapping
            -}

        -- I think this captures the logic of the following two cases from the paper:
        -- > perform u | atomic u    = mbindTheContinuation u
        -- > perform e | not (hnf e) = evaluate e >>= perform
        -- TODO: But we should be careful to make sure we haven't left any cases out. Maybe we should have some sort of @mustPerform@ predicate like we have 'mustCheck' in TypeCheck.hs...?
        _ -> do
            w <- evaluate perform e0
            case w of
                Head_   v -> perform $ fromHead v
                Neutral e -> mbindTheContinuation e


-- This is the only place (in this file) where we really need
-- the 'M' instance of 'EvaluationMonad'. I think it's also the
-- only place (anywhere) that we really need to know the internal
-- CPS structure of 'M'. (Though I suppose a few other places
-- let us short-circuit generating unused code after a 'P.bot'
-- or 'P.reject'.)
mbindTheContinuation :: (ABT AST abt) => MeasureEvaluator abt (M abt)
mbindTheContinuation e = do
    z <- freshVar Text.empty (case typeOf e of SMeasure typ -> typ)
    M $ \c h -> syn (MBind :$ e :* bind z (c (Neutral $ var z) h) :* End)


----------------------------------------------------------------
----------------------------------------------------------- fin.
