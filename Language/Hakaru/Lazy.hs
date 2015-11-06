{-# LANGUAGE CPP
           , GADTs
           , EmptyCase
           , DataKinds
           , KindSignatures
           , MultiParamTypeClasses
           , FunctionalDependencies
           , ScopedTypeVariables
           , FlexibleContexts
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.11.05
-- |
-- Module      :  Language.Hakaru.Lazy
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Lazy partial evaluation.
----------------------------------------------------------------
module Language.Hakaru.Lazy
    (
    -- * Lazy partial evaluation
      evaluate
    , perform
    -- ** Helper functions
    , update
    ) where

import qualified Data.Foldable        as F
import qualified Data.Traversable     as T
import           Data.Sequence        (Seq)
import qualified Data.Sequence        as Seq
import           Data.Number.LogFloat (LogFloat)
#if __GLASGOW_HASKELL__ < 710
import           Data.Functor         ((<$>))
import           Control.Applicative  (Applicative(..))
#endif

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.Nat
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.DatumCase
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.Coercion
import Language.Hakaru.Lazy.Types
import qualified Language.Hakaru.Syntax.Prelude as P
import qualified Language.Hakaru.Expect         as E
import Language.Hakaru.PrettyPrint -- HACK: for ghci use only

----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: make this function monad-polymorphic, and have it take
-- some sort of continuation for the one case of 'update' where we
-- need to 'perform'. This way we can generalize over the notion
-- of \"performing\" in order to reuse this function with Sample.hs
-- and Expect.hs
--
-- TODO: (eventually) accept an argument dictating the evaluation
-- strategy (HNF, WHNF, full-beta NF,...). The strategy value should
-- probably be a family of singletons, where the type-level strategy
-- @s@ is also an index on the 'Context' and (the renamed) 'Whnf'.
-- That way we don't need to define a bunch of variant 'Context',
-- 'Statement', and 'Whnf' data types; but rather can use indexing
-- to select out subtypes of the generic versions.
evaluate
    :: (ABT AST abt, EvaluationMonad abt m)
    => abt '[] a
    -> m (Whnf abt a)
evaluate e0 =
    caseVarSyn e0 update $ \t ->
        case t of
        -- Things which are already weak head-normal forms
        Value_  v         -> return . Head_ $ WValue v
        Datum_  d         -> return . Head_ $ WDatum d
        Empty_            -> return . Head_ $ WEmpty
        Array_  e1 e2     -> return . Head_ $ WArray   e1 e2
        Lam_ :$ e1 :* End -> return . Head_ $ WLam     e1
        Dirac        :$ _ -> return . Head_ $ WMeasure e0
        MBind        :$ _ -> return . Head_ $ WMeasure e0 -- N.B., not HNF
        MeasureOp_ _ :$ _ -> return . Head_ $ WMeasure e0
        Superpose_ _      -> return . Head_ $ WMeasure e0


        -- Everything else needs some evaluation

        App_ :$ e1 :* e2 :* End -> do
            -- This implementation gives call-by-need beta-reduction.
            w1 <- evaluate e1
            caseNeutralHead w1
                (\e1' -> return . Neutral $ P.app e1' e2)
                $ \(WLam f) ->
                    caseBind f $ \x f' ->
                        push (SLet x $ Thunk e2) f' evaluate

        Let_ :$ e1 :* e2 :* End ->
            caseBind e2 $ \x e2' ->
                push (SLet x $ Thunk e1) e2' evaluate

        Fix_ :$ e1 :* End -> error "TODO: evaluate{Fix_}"

        Ann_ typ :$ e1 :* End -> error "TODO: evaluate{Ann_}"
        {-
            do
            w1 <- evaluate e1
            return $
                -- if not @mustCheck (fromWhnf w1)@, then could in principle eliminate the annotation; though it might be here so that it'll actually get pushed down to somewhere it's needed later on, so it's best to play it safe and leave it in.
                caseNeutralHead w1
                    (Neutral . P.ann_ typ)
                    (\v1 -> Head_ $ HAnn typ v1) -- or something...
        -}

        CoerceTo_   c :$ e1 :* End -> coerceTo   c <$> evaluate e1
        UnsafeFrom_ c :$ e1 :* End -> unsafeFrom c <$> evaluate e1
        -- TODO: will maybe clean up the code to map 'evaluate' over @es@ before calling the evaluateFooOp helpers?
        NaryOp_     o    es        -> evaluateNaryOp o es
        PrimOp_     o :$ es        -> evaluatePrimOp o es

        -- BUG: avoid the chance of looping in case 'E.expect' residualizes!
        -- TODO: use 'evaluate' in 'E.expect' for the evaluation of @e1@
        Expect :$ e1 :* e2 :* End ->
            caseBind e2 $ \x e2' ->
                evaluate $ E.expect e1 (\e3 -> subst x e3 e2')

        Lub_ es -> error "TODO: evaluate{Lub_}" -- (Head_ . HLub) <$> T.for es evaluate

        -- TODO: rather than throwing a Haskell error, instead
        -- capture the possibility of failure in the 'M' monad.
        Case_ e bs -> do
            match <- matchBranches evaluateDatum e bs
            case match of
                Nothing -> error "evaluate{Case_}: nothing matched!"
                Just (GotStuck, _) ->
                    return . Neutral . syn $ Case_ e bs
                Just (Matched ss Nil1, body) ->
                    pushes (toStatements ss) body evaluate

        -- HACK: these cases are impossible, and ghc can confirm
        -- that (via no warnings about the empty case analysis being
        -- incomplete), but ghc can't infer it for some reason
        Lam_ :$ es -> case es of {}
        App_ :$ es -> case es of {}
        Let_ :$ es -> case es of {}
        Fix_ :$ es -> case es of {}
        Ann_ _ :$ es -> case es of {}
        CoerceTo_ _ :$ es -> case es of {}
        UnsafeFrom_ _ :$ es -> case es of {}
        Expect :$ es -> case es of {}


-- TODO: At present, whenever we residualize a case expression we'll
-- generate a 'Neutral' term which will, when run, repeat the work
-- we're doing in the evaluation here. We could eliminate this
-- redundancy by introducing a new variable for @e@ each time this
-- function is called--- if only we had some way of getting those
-- variables put into the right place for when we residualize the
-- original scrutinee...
--
-- Factored out to the top level, since 'DatumEvaluator' is a rank-2 type
evaluateDatum
    :: (ABT AST abt, EvaluationMonad abt m) => DatumEvaluator abt m
evaluateDatum e = viewWhnfDatum <$> evaluate e

type DList a = [a] -> [a]

toStatements
    :: DList (Assoc abt)
    -> [Statement abt]
toStatements ss = map (\(Assoc x e) -> SLet x $ Thunk e) (ss [])


----------------------------------------------------------------
-- TODO: figure out how to abstract this so it can be reused by
-- 'constrainValue'. Especially the 'SBranch case of 'step'
--
-- TODO: make this function monad-polymorphic, and have it take
-- some sort of continuation for the one case where we need to
-- 'perform'. This way we can generalize over the notion of
-- \"performing\" in order to reuse this function with Sample.hs
-- and Expect.hs
--
-- TODO: we could speed up the case for free variables by having
-- the 'Context' also keep track of the largest free var. That way,
-- we can just check up front whether @varID x < nextFreeVarID@.
-- Of course, we'd have to make sure we've sufficiently renamed all
-- bound variables to be above @nextFreeVarID@; but then we have to
-- do that anyways.
update
    :: forall abt m a
    .  (ABT AST abt, EvaluationMonad abt m)
    => Variable a
    -> m (Whnf abt a)
update = \x -> do
    mb <- select (binderFor x)
    return $
        case mb of
        Nothing -> Neutral (var x) -- turns out @x@ is a free variable
        Just w  -> w
    where
    -- | Is @s@ a binder for @x@ (i.e., does @s@ bind @x@)?
    binderFor :: Variable a -> Statement abt -> Maybe (m (Whnf abt a))
    binderFor x (SBind y e) = do
        Refl <- varEq x y
        Just $ do
            w <- error "TODO: update{SBind}" -- BUG: @caseLazy e return perform@ requires @m ~ M abt@
            unsafePush (SLet x $ Whnf_ w)
            return (NamedWhnf x w)
    binderFor x (SLet y e) = do
        Refl <- varEq x y
        Just $ do
            w <- caseLazy e return evaluate
            unsafePush (SLet x $ Whnf_ w)
            return (NamedWhnf x w)
    binderFor x (SBranch ys pat e)
        | varElem x ys = Just $ do
            w <- caseLazy e return evaluate
            error "TODO: update{SBranch}" -- BUG: @updateBranch x ys pat w@ requires @m ~ M abt@...
    binderFor _ _ = Nothing

    -- TODO: double check to make sure we don't accidentally drop the bindings for @ys@.
    -- BUG: this idea seemed to work fine for the @unleft@\/@unright@ examples in the paper, but it doesn't generalize. In particular, this can cause us to recursively residualize 'SBranch' things all up the heap; but since things can have multiple branches in general, that means we can end up generating some severely bloated code! I think in general we really shouldn't have 'SBranch' as a 'Statement' (unless we're doing HNF in lieu of WHNF); it's really just a special case for source code using @unleft@\/@unright@ and 'MBind'-ing the result, and we should probably treat it like that; i.e., just like any other 'SBind'.
    updateBranch
        :: forall (xs :: [Hakaru]) (b :: Hakaru)
        .  Variable a
        -> List1 Variable xs
        -> Pattern xs b
        -> Whnf abt b
        -> M abt (Whnf abt a)
    updateBranch x ys pat w =
        let residualizeCase e = M $ \c h ->
                Neutral . syn $ Case_ e
                    [ Branch pat $
                        case eqAppendIdentity ys of
                        Refl -> binds ys (fromWhnf $ c (Neutral $ var x) h)
                    , Branch PWild $
                        error "TODO: update{SBranch}: other branches" -- for the case where we're in the 'M'' monad rather than the 'M' monad, we can use 'P.reject' here...
                    ]
        in do
            -- BUG: should we really use @fromWhnf w@ here? Or should we prefer @caseNeutralHead w residualizeCase $ \v -> ...(fromHead v)...@?
            match <- matchTopPattern evaluateDatum (fromWhnf w) pat ys
            case match of
                Just (Matched ss Nil1) -> do
                    unsafePushes (toStatements ss) -- TODO: use a DList to avoid reversing inside 'unsafePushes'
                    update x -- Now we need to force the new binding for @x@
                Just GotStuck -> residualizeCase (fromWhnf w)
                Nothing -> error "TODO: update{SBranch}: match is guaranteed to fail" -- P.reject


-- TODO: move this to ABT.hs\/Variable.hs
varElem :: Variable (a :: Hakaru) -> List1 Variable (xs :: [Hakaru]) -> Bool
varElem _ Nil1         = False
varElem x (Cons1 y ys) =
    case varEq x y of
    Just _  -> True
    Nothing -> varElem x ys


----------------------------------------------------------------
-- BUG: need to improve the types so they can capture polymorphic data types
-- BUG: this is a gross hack. If we can avoid it, we should!
class Interp a a' | a -> a' where
    reify   :: (ABT AST abt) => Head abt a -> a'
    reflect :: (ABT AST abt) => a' -> Head abt a

instance Interp 'HNat Nat where
    reify (WValue (VNat n)) = n
    reflect = WValue . VNat

instance Interp 'HInt Int where
    reify (WValue (VInt i)) = i
    reflect = WValue . VInt

instance Interp 'HProb LogFloat where -- TODO: use rational instead
    reify (WValue (VProb p)) = p
    reflect = WValue . VProb

instance Interp 'HReal Double where -- TODO: use rational instead
    reify (WValue (VReal r)) = r
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
    w <- evaluate e
    caseNeutralHead w
        (return . Neutral . f)
        (return . Head_ . reflect . f' . reify)


rr2 :: ( ABT AST abt, EvaluationMonad abt m
       , Interp a a', Interp b b', Interp c c')
    => (a' -> b' -> c')
    -> (abt '[] a -> abt '[] b -> abt '[] c)
    -> abt '[] a
    -> abt '[] b
    -> m (Whnf abt c)
rr2 f' f e1 e2 = do
    w1 <- evaluate e1
    w2 <- evaluate e2
    caseNeutralHead w1
        (\e1' -> return . Neutral $ f e1' (fromWhnf w2))
        $ \v1 ->
            caseNeutralHead w2
                (\e2' -> return . Neutral $ f (fromWhnf w1) e2')
                $ \v2 -> return . Head_ . reflect $ f' (reify v1) (reify v2)


impl, diff, nand, nor :: Bool -> Bool -> Bool
impl x y = not x || y
diff x y = x && not y
nand x y = not (x && y)
nor  x y = not (x || y)

natRoot :: (Floating a) => a -> Nat -> a
natRoot x y = x ** recip (fromIntegral (fromNat y))


----------------------------------------------------------------
-- TODO: there's got to be a more efficient way to do this...
narySnoc
    :: (Head abt a -> Head abt a -> Head abt a)
    -> Seq (Whnf abt a)
    -> Whnf abt a
    -> Seq (Whnf abt a)
narySnoc op = go
    where
    go ws w =
        case Seq.viewr ws of
        Seq.EmptyR   -> Seq.singleton w
        ws' Seq.:> w' ->
            case (w',w) of
            -- BUG: deal with NamedWhnf
            (Head_ v1, Head_ v2) -> go ws' (Head_ (op v1 v2))
            _                    -> ws Seq.|> w

naryAppend
    :: (Head abt a -> Head abt a -> Head abt a)
    -> Seq (Whnf abt a)
    -> Seq (Whnf abt a)
    -> Seq (Whnf abt a)
naryAppend op = go
    where
    go ws1 ws2 =
        case Seq.viewl ws2 of
        Seq.EmptyL     -> ws1
        w' Seq.:< ws2' -> go (narySnoc op ws1 w') ws2'


evaluateNaryOp
    :: (ABT AST abt, EvaluationMonad abt m)
    => NaryOp a
    -> Seq (abt '[] a)
    -> m (Whnf abt a)
evaluateNaryOp = \o es -> do
    ws <- T.traverse evaluate es
    let ws' = naryAppend (evalOp o) Seq.empty ws
    return $
        case Seq.viewl ws' of
        Seq.EmptyL     -> Neutral $ identityElement o
        w1 Seq.:< ws'' ->
            case Seq.viewl ws'' of
            Seq.EmptyL -> w1 -- Avoid singleton naryOps
            _          -> Neutral . syn . NaryOp_ o $ fmap fromWhnf ws'
    where
    -- TODO: move this off to Prelude.hs or somewhere...
    identityElement :: (ABT AST abt) => NaryOp a -> abt '[] a
    identityElement o =
        case o of
        And    -> P.true
        Or     -> P.false
        Xor    -> emptyNaryOp o -- no identity
        Iff    -> emptyNaryOp o -- no identity
        Min  _ -> emptyNaryOp o -- no identity in general (but we could do it by cases...)
        Max  _ -> emptyNaryOp o -- no identity in general (but we could do it by cases...)
        Sum  _ -> emptyNaryOp o -- HACK: 'P.zero' is too stupid here
        Prod _ -> emptyNaryOp o -- HACK: 'P.one' is too stupid here
    
    emptyNaryOp o = syn (NaryOp_ o Seq.empty)
    
    -- | The evaluation interpretation of each NaryOp
    evalOp :: NaryOp a -> Head abt a -> Head abt a -> Head abt a
    evalOp = error "TODO: evalOp"
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
evaluatePrimOp RealPow   (e1 :* e2 :* End) = rr2 (**)  _ e1 e2 -- TODO: types
evaluatePrimOp Exp       (e1 :* End)       = rr1 exp   _ e1 -- TODO: types
evaluatePrimOp Log       (e1 :* End)       = rr1 log   _ e1 -- TODO: types
evaluatePrimOp Infinity         End        = return (Head_ HInfinity)
evaluatePrimOp NegativeInfinity End        = return (Head_ HNegativeInfinity)
evaluatePrimOp GammaFunc   (e1 :* End)             =
evaluatePrimOp BetaFunc    (e1 :* e2 :* End)       =
evaluatePrimOp Integrate   (e1 :* e2 :* e3 :* End) =
evaluatePrimOp Summate     (e1 :* e2 :* e3 :* End) =
evaluatePrimOp (Index   _) (e1 :* e2 :* End)       =
evaluatePrimOp (Size    _) (e1 :* End)             =
evaluatePrimOp (Reduce  _) (e1 :* e2 :* e3 :* End) =
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
coerceTo :: Coercion a b -> Whnf abt a -> Whnf abt b
coerceTo = error "TODO: coerceTo"
{-
coerceTo c e0 =
    case e0 of
    Head_   e' -> go c e'
    Neutral e' -> return (P.coerceTo_ c e') -- TODO: inline the smartness of P.coerceTo_ here; and make the prelude version dumb.
    where
    go c e =
        case e of
        WValue   v     ->
        WDatum   d     ->
        WEmpty         ->
        WArray   e1 e2 ->
        WLam     e1    ->
        WMeasure e1    ->
-}


unsafeFrom :: Coercion a b -> Whnf abt b -> Whnf abt a
unsafeFrom = error "TODO: unsafeFrom"
{-
unsafeFrom c e0 =
    case e0 of
    head_   e' -> go c e'
    Neutral e' -> return (P.unsafeFrom_ c e') -- TODO: inline the smartness of P.unsafeFrom_ here; and make the prelude version dumb.
    where
    go c e =
        case e of
        WValue   v     ->
        WDatum   d     ->
        WEmpty         ->
        WArray   e1 e2 ->
        WLam     e1    ->
        WMeasure e1    ->
-}


----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: 'perform' should move to Disintegrate.hs

-- N.B., that return type is correct, albeit strange. The idea is that the continuation takes in the variable of type @a@ bound by the expression of type @'HMeasure a@. However, this requires that the continuation of the 'Ans' type actually does @forall a. ...('HMeasure a)@ which is at odds with what 'evaluate' wants (or at least, what *I* think it should want.)
-- BUG: eliminate the 'SingI' requirement (comes from using @(P.>>=)@)
-- BUG: use 'freshNat' when generating names for @(P.>>=)@ rather than using the HOAS API.
perform
    :: (ABT AST abt, SingI a)
    => abt '[] ('HMeasure a) -> M abt (Whnf abt a)
perform e0 =
    caseVarSyn e0 (error "TODO: perform{Var}") $ \t ->
        case t of
        Dirac :$ e1 :* End ->
            evaluate e1
        MeasureOp_ _ :$ _ ->
            M $ \c h -> Head_ $ WMeasure (e0 P.>>= \z -> fromWhnf (c (Neutral z) h))
        MBind :$ e1 :* e2 :* End ->
            caseBind e2 $ \x e2' ->
                push (SBind x $ Thunk e1) e2' perform
        Superpose_ es ->
            error "TODO: perform{Superpose_}"
            {-
            P.superpose <$> T.traverse perform es -- TODO: not quite right; need to push the SWeight in each branch. Also, 'Whnf' un\/wrapping
            -}

        -- I think this captures the logic of the following two cases from the paper:
        -- > perform u | atomic u    = M' $ \c h -> u P.>>= \z -> c z h
        -- > perform e | not (hnf e) = evaluate e >>= perform
        -- TODO: But we should be careful to make sure we haven't left any cases out. Maybe we should have some sort of @mustPerform@ predicate like we have 'mustCheck' in TypeCheck.hs...?
        _ -> do
            w <- evaluate e0
            flip (caseNeutralHead w) (perform . fromHead) $ \e0' ->
                M $ \c h -> Head_ $ WMeasure (e0' P.>>= \z -> fromWhnf (c (Neutral z) h))


----------------------------------------------------------------
----------------------------------------------------------- fin.
