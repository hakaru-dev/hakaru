{-# LANGUAGE CPP
           , GADTs
           , DataKinds
           , KindSignatures
           , MultiParamTypeClasses
           , FunctionalDependencies
           , ScopedTypeVariables
           , FlexibleContexts
           , Rank2Types
           , TypeSynonymInstances
           , FlexibleInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.04.28
-- |
-- Module      :  Language.Hakaru.Evaluation.Lazy
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Lazy partial evaluation.
--
-- BUG: completely gave up on structure sharing. Need to add that
-- back in. cf., @gvidal-lopstr07lncs.pdf@ for an approach much
-- like my old one.
----------------------------------------------------------------
module Language.Hakaru.Evaluation.Lazy
    ( evaluate
    -- ** Helper functions
    , evaluateNaryOp
    , evaluatePrimOp
    , evaluateArrayOp
    -- ** Helpers that should really go away
    , Interp(..), reifyPair
    ) where

import           Prelude                hiding (id, (.))
import           Control.Category       (Category(..))
#if __GLASGOW_HASKELL__ < 710
import           Data.Functor           ((<$>))
#endif
import           Control.Monad          ((<=<))
import           Control.Monad.Identity (Identity, runIdentity)
import           Data.Sequence          (Seq)
import qualified Data.Sequence          as Seq
import qualified Data.Text              as Text

import Language.Hakaru.Syntax.IClasses
import Data.Number.Nat
import Data.Number.Natural
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Syntax.TypeOf
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.DatumCase (DatumEvaluator, MatchResult(..), matchBranches, MatchState(..), matchTopPattern)
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Evaluation.Types
import qualified Language.Hakaru.Syntax.Prelude as P
{-
-- BUG: can't import this because of cyclic dependency
import qualified Language.Hakaru.Expect         as E
-}

#ifdef __TRACE_DISINTEGRATE__
import Language.Hakaru.Pretty.Haskell (pretty)
import Debug.Trace (trace)
#endif

----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: (eventually) accept an argument dictating the evaluation
-- strategy (HNF, WHNF, full-beta NF,...). The strategy value should
-- probably be a family of singletons, where the type-level strategy
-- @s@ is also an index on the 'Context' and (the renamed) 'Whnf'.
-- That way we don't need to define a bunch of variant 'Context',
-- 'Statement', and 'Whnf' data types; but rather can use indexing
-- to select out subtypes of the generic versions.


-- | Lazy partial evaluation with some given \"perform\" and
-- \"evaluateCase\" functions. N.B., if @p ~ 'Pure@ then the
-- \"perform\" function will never be called.
evaluate
    :: forall abt m p
    .  (ABT Term abt, EvaluationMonad abt m p)
    => MeasureEvaluator abt m
    -> TermEvaluator    abt m
{-# INLINE evaluate #-}
evaluate perform = evaluate_
    where
    evaluateCase_ :: CaseEvaluator abt m
    evaluateCase_ = evaluateCase evaluate_

    evaluate_ :: TermEvaluator abt m
    evaluate_ e0 =
#ifdef __TRACE_DISINTEGRATE__
      trace ("-- evaluate_: " ++ show (pretty e0)) $
#endif
      caseVarSyn e0 (evaluateVar perform evaluate_) $ \t ->
        case t of
        -- Things which are already WHNFs
        Literal_ v               -> return . Head_ $ WLiteral v
        Datum_   d               -> return . Head_ $ WDatum   d
        Empty_   typ             -> return . Head_ $ WEmpty   typ
        Array_   e1 e2           -> return . Head_ $ WArray e1 e2
        ArrayLiteral_ es         -> return . Head_ $ WArrayLiteral es
        Lam_  :$ e1 :* End       -> return . Head_ $ WLam   e1
        Dirac :$ e1 :* End       -> return . Head_ $ WDirac e1
        MBind :$ e1 :* e2 :* End -> return . Head_ $ WMBind e1 e2
        Plate :$ e1 :* e2 :* End -> return . Head_ $ WPlate e1 e2
        MeasureOp_ o :$ es       -> return . Head_ $ WMeasureOp o es
        Superpose_ pes           -> return . Head_ $ WSuperpose pes
        Reject_ typ              -> return . Head_ $ WReject typ
        -- We don't bother evaluating these, even though we could...
        Integrate :$ e1 :* e2 :* e3 :* End ->
            return . Head_ $ WIntegrate e1 e2 e3
        Summate h1 h2 :$ e1 :* e2 :* e3 :* End ->
            return . Neutral $ syn t
            --return . Head_ $ WSummate   e1 e2 e3


        -- Everything else needs some evaluation

        App_ :$ e1 :* e2 :* End -> do
            w1 <- evaluate_ e1
            case w1 of
                Neutral e1' -> return . Neutral $ P.app e1' e2
                Head_   v1  -> evaluateApp v1
            where
            evaluateApp (WLam f)   =
                -- call-by-name:
                caseBind f $ \x f' -> do
                    i <- getIndices
                    push (SLet x (Thunk e2) i) f' >>= evaluate_
            evaluateApp _ = error "evaluate{App_}: the impossible happened"

        Let_ :$ e1 :* e2 :* End -> do
            i <- getIndices
            caseBind e2 $ \x e2' ->
                push (SLet x (Thunk e1) i) e2' >>= evaluate_

        CoerceTo_   c :$ e1 :* End -> coerceTo   c <$> evaluate_ e1
        UnsafeFrom_ c :$ e1 :* End -> coerceFrom c <$> evaluate_ e1

        -- TODO: will maybe clean up the code to map 'evaluate' over @es@ before calling the evaluateFooOp helpers?
        NaryOp_  o    es -> evaluateNaryOp  evaluate_ o es
        ArrayOp_ o :$ es -> evaluateArrayOp evaluate_ o es
        PrimOp_  o :$ es -> evaluatePrimOp  evaluate_ o es

        Transform_ t :$ _ -> error $
            concat ["TODO: evaluate{", show t, "}"
                   ,": cannot evaluate transforms; expand them first"]

        Case_ e bs -> evaluateCase_ e bs

        _ :$ _ -> error "evaluate: the impossible happened"


----------------------------------------------------------------
-- BUG: need to improve the types so they can capture polymorphic data types
-- BUG: this is a **really gross** hack. If we can avoid it, we should!!!
class Interp a a' | a -> a' where
    reify   :: (ABT Term abt) => Head abt a -> a'
    reflect :: (ABT Term abt) => a' -> Head abt a

instance Interp 'HNat Natural where
    reflect = WLiteral . LNat
    reify (WLiteral (LNat n)) = n
    reify (WCoerceTo   _ _) = error "TODO: reify{WCoerceTo}"
    reify (WUnsafeFrom _ _) = error "TODO: reify{WUnsafeFrom}"

instance Interp 'HInt Integer where
    reflect = WLiteral . LInt
    reify (WLiteral (LInt i)) = i
    reify (WCoerceTo   _ _) = error "TODO: reify{WCoerceTo}"
    reify (WUnsafeFrom _ _) = error "TODO: reify{WUnsafeFrom}"

instance Interp 'HProb NonNegativeRational where
    reflect = WLiteral . LProb
    reify (WLiteral (LProb p)) = p
    reify (WCoerceTo   _ _)   = error "TODO: reify{WCoerceTo}"
    reify (WUnsafeFrom _ _)   = error "TODO: reify{WUnsafeFrom}"
    reify (WIntegrate  _ _ _) = error "TODO: reify{WIntegrate}"
    --reify (WSummate    _ _ _) = error "TODO: reify{WSummate}"

instance Interp 'HReal Rational where
    reflect = WLiteral . LReal
    reify (WLiteral (LReal r)) = r
    reify (WCoerceTo   _ _) = error "TODO: reify{WCoerceTo}"
    reify (WUnsafeFrom _ _) = error "TODO: reify{WUnsafeFrom}"


identifyDatum :: (ABT Term abt) => DatumEvaluator (abt '[]) Identity
identifyDatum = return . (viewWhnfDatum <=< toWhnf)

-- HACK: this requires -XTypeSynonymInstances and -XFlexibleInstances
-- This instance does seem to work; albeit it's trivial...
instance Interp HUnit () where
    reflect () = WDatum dUnit
    reify v = runIdentity $ do
        match <- matchTopPattern identifyDatum (fromHead v) pUnit Nil1
        case match of
            Just (Matched_ _ss Nil1) -> return ()
            _ -> error "reify{HUnit}: the impossible happened"

-- HACK: this requires -XTypeSynonymInstances and -XFlexibleInstances
-- This instance also seems to work...
instance Interp HBool Bool where
    reflect = WDatum . (\b -> if b then dTrue else dFalse)
    reify v = runIdentity $ do
        matchT <- matchTopPattern identifyDatum (fromHead v) pTrue Nil1
        case matchT of
            Just (Matched_ _ss Nil1) -> return True
            Just GotStuck_ -> error "reify{HBool}: the impossible happened"
            Nothing -> do
                matchF <- matchTopPattern identifyDatum (fromHead v) pFalse Nil1
                case matchF of
                    Just (Matched_ _ss Nil1) -> return False
                    _ -> error "reify{HBool}: the impossible happened"


-- TODO: can't we just use 'viewHeadDatum' and match on that?
reifyPair
    :: (ABT Term abt) => Head abt (HPair a b) -> (abt '[] a, abt '[] b)
reifyPair v =
    let impossible = error "reifyPair: the impossible happened"
        e0    = fromHead v
        n     = nextFree e0
        (a,b) = sUnPair $ typeOf e0
        x = Variable Text.empty n       a
        y = Variable Text.empty (1 + n) b

    in runIdentity $ do
        match <- matchTopPattern identifyDatum e0 (pPair PVar PVar) (Cons1 x (Cons1 y Nil1))
        case match of
            Just (Matched_ ss Nil1) ->
                case ss [] of
                [Assoc x' e1, Assoc y' e2] ->
                    maybe impossible id $ do
                        Refl <- varEq x x'
                        Refl <- varEq y y'
                        Just $ return (e1, e2)
                _ -> impossible
            _ -> impossible
{-
instance Interp (HPair a b) (abt '[] a, abt '[] b) where
    reflect (a,b) = P.pair a b
    reify = reifyPair

instance Interp (HEither a b) (Either (abt '[] a) (abt '[] b)) where
    reflect (Left  a) = P.left  a
    reflect (Right b) = P.right b
    reify =

instance Interp (HMaybe a) (Maybe (abt '[] a)) where
    reflect Nothing  = P.nothing
    reflect (Just a) = P.just a
    reify =

data ListHead (a :: Hakaru)
    = NilHead
    | ConsHead (abt '[] a) (abt '[] (HList a)) -- modulo scoping of @abt@

instance Interp (HList a) (ListHead a) where
    reflect []     = P.nil
    reflect (x:xs) = P.cons x xs
    reify =
-}


impl, diff, nand, nor :: Bool -> Bool -> Bool
impl x y = not x || y
diff x y = x && not y
nand x y = not (x && y)
nor  x y = not (x || y)

-- BUG: no Floating instance for LogFloat (nor NonNegativeRational), so can't actually use this...
natRoot :: (Floating a) => a -> Nat -> a
natRoot x y = x ** recip (fromIntegral (fromNat y))


----------------------------------------------------------------
evaluateNaryOp
    :: (ABT Term abt, EvaluationMonad abt m p)
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
            Seq.EmptyL         -> identityElement o -- Avoid empty naryOps
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
        -- TODO: immediately return @ws@ if @w1 == identityElement o@ (whenever identityElement is defined)
        case Seq.viewr ws of
        Seq.EmptyR    -> Seq.singleton w1
        ws' Seq.:> w2 ->
            case (w1,w2) of
            (Head_ v1, Head_ v2) -> snocLoop op ws' (Head_ (op v1 v2))
            _                    -> ws Seq.|> w1

    matchNaryOp
        :: (ABT Term abt)
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
    identityElement :: (ABT Term abt) => NaryOp a -> Whnf abt a
    identityElement o =
        case o of
        And    -> Head_ (WDatum dTrue)
        Or     -> Head_ (WDatum dFalse)
        Xor    -> Head_ (WDatum dFalse)
        Iff    -> Head_ (WDatum dTrue)
        Min  _ -> Neutral (syn (NaryOp_ o Seq.empty)) -- no identity in general (but we could do it by cases...)
        Max  _ -> Neutral (syn (NaryOp_ o Seq.empty)) -- no identity in general (but we could do it by cases...)
        -- TODO: figure out how to reuse 'P.zero_' and 'P.one_' here; requires converting thr @(syn . Literal_)@ into @(Head_ . WLiteral)@. Maybe we should change 'P.zero_' and 'P.one_' so they just return the 'Literal' itself rather than the @abt@?
        Sum  HSemiring_Nat  -> Head_ (WLiteral (LNat  0))
        Sum  HSemiring_Int  -> Head_ (WLiteral (LInt  0))
        Sum  HSemiring_Prob -> Head_ (WLiteral (LProb 0))
        Sum  HSemiring_Real -> Head_ (WLiteral (LReal 0))
        Prod HSemiring_Nat  -> Head_ (WLiteral (LNat  1))
        Prod HSemiring_Int  -> Head_ (WLiteral (LInt  1))
        Prod HSemiring_Prob -> Head_ (WLiteral (LProb 1))
        Prod HSemiring_Real -> Head_ (WLiteral (LReal 1))

    -- | The evaluation interpretation of each NaryOp
    evalOp
        :: (ABT Term abt)
        => NaryOp a
        -> Head abt a
        -> Head abt a
        -> Head abt a
    -- TODO: something more efficient\/direct if we can...
    evalOp And      = \v1 v2 -> reflect (reify v1 && reify v2)
    evalOp Or       = \v1 v2 -> reflect (reify v1 || reify v2)
    evalOp Xor      = \v1 v2 -> reflect (reify v1 /= reify v2)
    evalOp Iff      = \v1 v2 -> reflect (reify v1 == reify v2)
    evalOp (Min  _) = error "TODO: evalOp{Min}"
    evalOp (Max  _) = error "TODO: evalOp{Max}"
    {-
    evalOp (Min  _) = \v1 v2 -> reflect (reify v1 `min` reify v2)
    evalOp (Max  _) = \v1 v2 -> reflect (reify v1 `max` reify v2)
    evalOp (Sum  _) = \v1 v2 -> reflect (reify v1 + reify v2)
    evalOp (Prod _) = \v1 v2 -> reflect (reify v1 * reify v2)
    -}
    -- HACK: this is just to have something to test. We really should reduce\/remove all this boilerplate...
    evalOp (Sum  theSemi) =
        \(WLiteral v1) (WLiteral v2) -> WLiteral $ evalSum  theSemi v1 v2
    evalOp (Prod theSemi) =
        \(WLiteral v1) (WLiteral v2) -> WLiteral $ evalProd theSemi v1 v2

    -- TODO: even if only one of the arguments is a literal, if that literal is zero\/one, then we can still partially evaluate it. (As is done in the old finally-tagless code)
    evalSum, evalProd :: HSemiring a -> Literal a -> Literal a -> Literal a
    evalSum  HSemiring_Nat  = \(LNat  n1) (LNat  n2) -> LNat  (n1 + n2)
    evalSum  HSemiring_Int  = \(LInt  i1) (LInt  i2) -> LInt  (i1 + i2)
    evalSum  HSemiring_Prob = \(LProb p1) (LProb p2) -> LProb (p1 + p2)
    evalSum  HSemiring_Real = \(LReal r1) (LReal r2) -> LReal (r1 + r2)
    evalProd HSemiring_Nat  = \(LNat  n1) (LNat  n2) -> LNat  (n1 * n2)
    evalProd HSemiring_Int  = \(LInt  i1) (LInt  i2) -> LInt  (i1 * i2)
    evalProd HSemiring_Prob = \(LProb p1) (LProb p2) -> LProb (p1 * p2)
    evalProd HSemiring_Real = \(LReal r1) (LReal r2) -> LReal (r1 * r2)


----------------------------------------------------------------
evaluateArrayOp
    :: ( ABT Term abt, EvaluationMonad abt m p
       , typs ~ UnLCs args, args ~ LCs typs)
    => TermEvaluator abt m
    -> ArrayOp typs a
    -> SArgs abt args
    -> m (Whnf abt a)
evaluateArrayOp evaluate_ = go
    where
    go o@(Index _) = \(e1 :* e2 :* End) -> do
        let -- idxCode :: abt '[] ('HArray a) -> abt '[] 'HNat -> abt '[] a
            -- idxCode a i = Neutral $ syn (ArrayOp_ o :$ a :* i :* End)
        w1 <- evaluate_ e1
        case w1 of
            Neutral e1' -> 
                return . Neutral $ syn (ArrayOp_ o :$ e1' :* e2 :* End)
            Head_ (WArray _ b) ->
                caseBind b $ \x body -> extSubst x e2 body >>= evaluate_
            Head_ (WEmpty _)   ->
                error "TODO: evaluateArrayOp{Index}{Head_ (WEmpty _)}"
            Head_ (WArrayLiteral arr) ->
                do w2 <- evaluate_ e2
                   case w2 of
                     Head_ (WLiteral (LNat n)) -> return . Neutral $ 
                                                  arr !! fromInteger (fromNatural n)
                     _  -> return . Neutral $
                           syn (ArrayOp_ o :$ fromWhnf w1 :* fromWhnf w2 :* End)
            _ -> error "evaluateArrayOp{Index}: uknown whnf of array type"

    go o@(Size _) = \(e1 :* End) -> do
        w1 <- evaluate_ e1
        case w1 of
            Neutral e1' -> return . Neutral $ syn (ArrayOp_ o :$ e1' :* End)
            Head_ (WEmpty _)    -> return . Head_ $ WLiteral (LNat 0)
            Head_ (WArray e2 _) -> evaluate_ e2
            Head_ (WArrayLiteral es) -> return . Head_ . WLiteral .
                                        primCoerceFrom (Signed HRing_Int) .
                                        LInt . toInteger $ length es

    go (Reduce _) = \(e1 :* e2 :* e3 :* End) ->
        error "TODO: evaluateArrayOp{Reduce}"

----------------------------------------------------------------
-- TODO: maybe we should adjust 'Whnf' to have a third option for
-- closed terms of the atomic\/literal types, so that we can avoid
-- reducing them just yet. Of course, we'll have to reduce them
-- eventually, but we can leave that for the runtime evaluation or
-- Maple or whatever. These are called \"annotated\" terms in Fischer
-- et al 2008 (though they allow anything to be annotated, not just
-- closed terms of atomic type).
evaluatePrimOp
    :: forall abt m p typs args a
    .  ( ABT Term abt, EvaluationMonad abt m p
       , typs ~ UnLCs args, args ~ LCs typs)
    => TermEvaluator abt m
    -> PrimOp typs a
    -> SArgs abt args
    -> m (Whnf abt a)
evaluatePrimOp evaluate_ = go
    where
    -- HACK: we don't have any way of saying these functions haven't reduced even though it's not actually a neutral term.
    neu1 :: forall b c
        .  (abt '[] b -> abt '[] c)
        -> abt '[] b
        -> m (Whnf abt c)
    neu1 f e = (Neutral . f . fromWhnf) <$> evaluate_ e

    neu2 :: forall b c d
        .  (abt '[] b -> abt '[] c -> abt '[] d)
        -> abt '[] b
        -> abt '[] c   
        -> m (Whnf abt d)
    neu2 f e1 e2 = do e1' <- fromWhnf <$> evaluate_ e1
                      e2' <- fromWhnf <$> evaluate_ e2
                      return . Neutral $ f e1' e2'

    rr1 :: forall b b' c c'
        .  (Interp b b', Interp c c')
        => (b' -> c')
        -> (abt '[] b -> abt '[] c)
        -> abt '[] b
        -> m (Whnf abt c)
    rr1 f' f e = do
        w <- evaluate_ e
        return $
            case w of
            Neutral e' -> Neutral $ f e'
            Head_   v  -> Head_ . reflect $ f' (reify v)

    rr2 :: forall b b' c c' d d'
        .  (Interp b b', Interp c c', Interp d d')
        => (b' -> c' -> d')
        -> (abt '[] b -> abt '[] c -> abt '[] d)
        -> abt '[] b
        -> abt '[] c
        -> m (Whnf abt d)
    rr2 f' f e1 e2 = do
        w1 <- evaluate_ e1
        w2 <- evaluate_ e2
        return $
            case w1 of
            Neutral e1' -> Neutral $ f e1' (fromWhnf w2)
            Head_   v1  ->
                case w2 of
                Neutral e2' -> Neutral $ f (fromWhnf w1) e2'
                Head_   v2  -> Head_ . reflect $ f' (reify v1) (reify v2)

    primOp2_
        :: forall b c d
        .  PrimOp '[ b, c ] d -> abt '[] b -> abt '[] c -> abt '[] d
    primOp2_ o e1 e2 = syn (PrimOp_ o :$ e1 :* e2 :* End)

    -- TODO: something more efficient\/direct if we can...
    go Not  (e1 :* End)       = rr1 not  P.not  e1
    go Impl (e1 :* e2 :* End) = rr2 impl (primOp2_ Impl) e1 e2
    go Diff (e1 :* e2 :* End) = rr2 diff (primOp2_ Diff) e1 e2
    go Nand (e1 :* e2 :* End) = rr2 nand P.nand e1 e2
    go Nor  (e1 :* e2 :* End) = rr2 nor  P.nor  e1 e2

    -- HACK: we don't have a way of saying that 'Pi' (or 'Infinity',...) is in fact a head; so we're forced to call it neutral which is a lie. We should add constructor(s) to 'Head' to cover these magic constants; probably grouped together under a single constructor called something like @Constant@. Maybe should group them like that in the AST as well?
    go Pi        End               = return $ Neutral P.pi

    -- We treat trig functions as strict, thus forcing their
    -- arguments; however, to avoid fuzz issues we don't actually
    -- evaluate the trig functions.
    --
    -- HACK: we might should have some other way to make these
    -- 'Whnf' rather than calling them neutral terms; since they
    -- aren't, in fact, neutral!
    go Sin       (e1 :* End)       = neu1 P.sin   e1
    go Cos       (e1 :* End)       = neu1 P.cos   e1
    go Tan       (e1 :* End)       = neu1 P.tan   e1
    go Asin      (e1 :* End)       = neu1 P.asin  e1
    go Acos      (e1 :* End)       = neu1 P.acos  e1
    go Atan      (e1 :* End)       = neu1 P.atan  e1
    go Sinh      (e1 :* End)       = neu1 P.sinh  e1
    go Cosh      (e1 :* End)       = neu1 P.cosh  e1
    go Tanh      (e1 :* End)       = neu1 P.tanh  e1
    go Asinh     (e1 :* End)       = neu1 P.asinh e1
    go Acosh     (e1 :* End)       = neu1 P.acosh e1
    go Atanh     (e1 :* End)       = neu1 P.atanh e1
    go Floor      (e1 :* End)      = neu1 P.floor e1

    -- TODO: deal with how we have better types for these three ops than Haskell does...
    -- go RealPow   (e1 :* e2 :* End) = rr2 (**) (P.**) e1 e2
    go RealPow   (e1 :* e2 :* End) = neu2 (P.**) e1 e2
    go Choose    (e1 :* e2 :* End) = neu2 (P.choose) e1 e2

    -- HACK: these aren't actually neutral!
    -- BUG: we should try to cancel out @(exp . log)@ and @(log . exp)@
    go Exp       (e1 :* End)       = neu1 P.exp e1
    go Log       (e1 :* End)       = neu1 P.log e1

    -- HACK: these aren't actually neutral!
    go (Infinity h)     End        =
        case h of
          HIntegrable_Nat  -> return . Neutral $ P.primOp0_ (Infinity h)
          HIntegrable_Prob -> return $ Neutral P.infinity

    go GammaFunc   (e1 :* End)            = neu1 P.gammaFunc e1
    go BetaFunc    (e1 :* e2 :* End)      = neu2 P.betaFunc  e1 e2

    go (Equal  theEq)   (e1 :* e2 :* End) = rrEqual theEq  e1 e2
    go (Less   theOrd)  (e1 :* e2 :* End) = rrLess  theOrd e1 e2
    go (NatPow theSemi) (e1 :* e2 :* End) =
        case theSemi of
        HSemiring_Nat    -> rr2 (\v1 v2 -> v1 ^ fromNatural v2) (P.^) e1 e2
        HSemiring_Int    -> rr2 (\v1 v2 -> v1 ^ fromNatural v2) (P.^) e1 e2
        HSemiring_Prob   -> rr2 (\v1 v2 -> v1 ^ fromNatural v2) (P.^) e1 e2
        HSemiring_Real   -> rr2 (\v1 v2 -> v1 ^ fromNatural v2) (P.^) e1 e2
    go (Negate theRing) (e1 :* End) =
        case theRing of
        HRing_Int        -> rr1 negate P.negate e1
        HRing_Real       -> rr1 negate P.negate e1
    go (Abs    theRing) (e1 :* End) =
        case theRing of
        HRing_Int        -> rr1 (unsafeNatural . abs) P.abs_ e1
        HRing_Real       -> rr1 (unsafeNonNegativeRational  . abs) P.abs_ e1
    go (Signum theRing) (e1 :* End) =
        case theRing of
        HRing_Int        -> rr1 signum P.signum e1
        HRing_Real       -> rr1 signum P.signum e1
    go (Recip  theFractional) (e1 :* End) =
        case theFractional of
        HFractional_Prob -> rr1 recip  P.recip  e1
        HFractional_Real -> rr1 recip  P.recip  e1
    go (NatRoot theRadical) (e1 :* e2 :* End) =
        case theRadical of
        HRadical_Prob -> neu2 (flip P.thRootOf) e1 e2
    {-
    go (NatRoot theRadical) (e1 :* e2 :* End) =
        case theRadical of
        HRadical_Prob -> rr2 natRoot (flip P.thRootOf) e1 e2
    go (Erf theContinuous) (e1 :* End) =
        case theContinuous of
        HContinuous_Prob -> rr1 erf P.erf e1
        HContinuous_Real -> rr1 erf P.erf e1
    -}
    go op _ = error $ "TODO: evaluatePrimOp{" ++ show op ++ "}"


    rrEqual
        :: forall b. HEq b -> abt '[] b -> abt '[] b -> m (Whnf abt HBool)
    rrEqual theEq =
        case theEq of
        HEq_Nat    -> rr2 (==) (P.==)
        HEq_Int    -> rr2 (==) (P.==)
        HEq_Prob   -> rr2 (==) (P.==)
        HEq_Real   -> rr2 (==) (P.==)
        HEq_Array aEq -> error "TODO: rrEqual{HEq_Array}"
        HEq_Bool   -> rr2 (==) (P.==)
        HEq_Unit   -> rr2 (==) (P.==)
        HEq_Pair   aEq bEq ->
            \e1 e2 -> do
                w1 <- evaluate_ e1
                w2 <- evaluate_ e2
                case w1 of
                    Neutral e1' ->
                        return . Neutral
                            $ P.primOp2_ (Equal theEq) e1' (fromWhnf w2)
                    Head_   v1  ->
                        case w2 of
                        Neutral e2' ->
                            return . Neutral
                                $ P.primOp2_ (Equal theEq) (fromHead v1) e2'
                        Head_ v2 -> do
                            let (v1a, v1b) = reifyPair v1
                            let (v2a, v2b) = reifyPair v2
                            wa <- rrEqual aEq v1a v2a
                            wb <- rrEqual bEq v1b v2b
                            return $
                                case wa of
                                Neutral ea ->
                                    case wb of
                                    Neutral eb -> Neutral (ea P.&& eb)
                                    Head_   vb
                                        | reify vb  -> wa
                                        | otherwise -> Head_ $ WDatum dFalse
                                Head_ va
                                    | reify va  -> wb
                                    | otherwise -> Head_ $ WDatum dFalse

        HEq_Either aEq bEq -> error "TODO: rrEqual{HEq_Either}"

    rrLess
        :: forall b. HOrd b -> abt '[] b -> abt '[] b -> m (Whnf abt HBool)
    rrLess theOrd =
        case theOrd of
        HOrd_Nat    -> rr2 (<) (P.<)
        HOrd_Int    -> rr2 (<) (P.<)
        HOrd_Prob   -> rr2 (<) (P.<)
        HOrd_Real   -> rr2 (<) (P.<)
        HOrd_Array aOrd -> error "TODO: rrLess{HOrd_Array}"
        HOrd_Bool   -> rr2 (<) (P.<)
        HOrd_Unit   -> rr2 (<) (P.<)
        HOrd_Pair aOrd bOrd ->
            \e1 e2 -> do
                w1 <- evaluate_ e1
                w2 <- evaluate_ e2
                case w1 of
                    Neutral e1' ->
                        return . Neutral
                            $ P.primOp2_ (Less theOrd) e1' (fromWhnf w2)
                    Head_   v1  ->
                        case w2 of
                        Neutral e2' ->
                            return . Neutral
                                $ P.primOp2_ (Less theOrd) (fromHead v1) e2'
                        Head_ v2 -> do
                            let (v1a, v1b) = reifyPair v1
                            let (v2a, v2b) = reifyPair v2
                            error "TODO: rrLess{HOrd_Pair}"
                            -- BUG: The obvious recursion won't work because we need to know when the first components are equal before recursing (to implement lexicographic ordering). We really need a ternary comparison operator like 'compare'.
        HOrd_Either aOrd bOrd -> error "TODO: rrLess{HOrd_Either}"


----------------------------------------------------------------
----------------------------------------------------------- fin.
