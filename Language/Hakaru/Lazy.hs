{-# LANGUAGE CPP
           , GADTs
           , EmptyCase
           , DataKinds
           , MultiParamTypeClasses
           , FunctionalDependencies
           , ScopedTypeVariables
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.28
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

import Data.Sequence        (Seq)
import Data.Number.LogFloat (LogFloat)
#if __GLASGOW_HASKELL__ < 710
import Data.Functor         ((<$>))
import Control.Applicative  (Applicative(..))
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
-- BUG: we need (a) a variant of 'update' which doesn't 'perform' if it finds an 'SBind' or else, (b) better ways of converting between 'M' and 'M''.
evaluate :: (ABT abt) => abt '[] a -> M abt (Whnf abt a)
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
            w1 <- evaluate e1
            case w1 of
                Neutral e1'    -> return . Neutral $ P.app e1' e2
                Head_ (WLam f) ->
                    caseBind f $ \x f' ->
                        push (SLet x $ Thunk e2) f' evaluate
                Head_ v1 -> case v1 of {} -- HACK: impossible

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
                case w1 of
                Head_   v1  -> Head_   $ HAnn   typ v1
                Neutral e1' -> Neutral $ P.ann_ typ e1'
        -}

        CoerceTo_   c :$ e1 :* End -> coerceTo   c <$> evaluate e1
        UnsafeFrom_ c :$ e1 :* End -> unsafeFrom c <$> evaluate e1
        -- TODO: will maybe clean up the code to map 'evaluate' over @es@ before calling the evaluateFooOp helpers?
        NaryOp_     o    es        -> evaluateNaryOp o es
        PrimOp_     o :$ es        -> evaluatePrimOp o es

        -- TODO: avoid the chance of looping in case 'E.expect' residualizes.
        -- TODO: use 'evaluate' in 'E.expect' in order to partially-NBE @e1@
        Expect :$ e1 :* e2 :* End ->
            caseBind e2 $ \x e2' ->
                evaluate $ E.expect e1 (\e3 -> subst x e3 e2')

        Lub_ es -> error "TODO: evaluate{Lub_}" -- (Head_ . HLub) <$> T.for es evaluate

        -- TODO: in the paper there's a guard so that this only fires when @not (atomic e)@. I think that was to prevent infinite loops in case 'evaluate' returns a 'Neutral' term. We get around this in the following way... The 'matchBranches' primitive will tell us it 'GotStuck' if it turns out that the value @v@ is not already a 'Datum' (whether as 'Datum_' or as 'Value_')[1]. And whenever 'matchBranches' gets stuck, 'tryMatch' will wrap the whole case expression up as a Neutral term.
        --
        -- [1] 'matchBranches' will also tell us it 'GotStuck' if the scrutinee isn't a 'Datum' at some subterm a nested 'Pattern' is trying to match against. At present this means we won't do as much partial evaluation as we really ought to; but in the future the 'GotStuck' constructor should return some information about where it got stuck so that we can 'evaluate' that subexpression. If we were evaluating to full normal forms, this wouldn't be an issue; it's only a problem because we're only doing (W)HNFs.
        Case_ e bs -> do
            w <- evaluate e
            tryMatch (fromWhnf w) bs evaluate

        -- HACK: these cases are impossible, and ghc can confirm that (via no warnings about the empty case analysis being incomplete), but ghc can't infer it for some reason
        Lam_ :$ es -> case es of {}
        App_ :$ es -> case es of {}
        Let_ :$ es -> case es of {}
        Fix_ :$ es -> case es of {}
        Ann_ _ :$ es -> case es of {}
        CoerceTo_ _ :$ es -> case es of {}
        UnsafeFrom_ _ :$ es -> case es of {}
        Expect :$ es -> case es of {}


----------------------------------------------------------------
-- TODO: figure out how to abstract this so it can be reused by
-- 'constrainValue'. Especially the 'SBranch case of 'step'
--
-- BUG: we need (a) a variant of 'update' which doesn't 'perform'
-- if it finds an 'SBind' or else, (b) better ways of converting
-- between 'M' and 'M''.
--
-- TODO: it's unclear what this function should really return. The
-- simplest thing would be to return @()@ since we're always returning
-- @Neutral(var x)@ so we can just have the caller do that themselves;
-- but returning @()@ breaks down in the case where we have to
-- residualize a case expression.
update :: forall abt a. (ABT abt) => Variable a -> M abt (Whnf abt a)
update x = loop []
    where
    loop :: [Statement abt] -> M abt (Whnf abt a)
    loop ss = do
        ms <- pop
        case ms of
            Nothing -> do
                naivePushes ss
                return (Neutral $ var x)
            Just s  ->
                case step s of
                Nothing -> loop (s:ss)
                Just mw -> do
                    -- Evaluate the body of @s@, updating it along the way.
                    w <- mw
                    -- Put the rest of the context back.
                    naivePushes ss
                    return w
                    -- TODO: rather than having @mw@ return @w =
                    -- Neutral(var x)@ and then returning that to
                    -- our caller; we may rather have @mw@ return
                    -- whatever @x@ becomes bound to after evaluation.
                    -- That would allow callers to do stuff with
                    -- the value rather than looking it up again
                    -- (e.g., performing immediate substitution
                    -- because the variable is only used once, or
                    -- something similar). This would also allow
                    -- us to distinguish this case from the case
                    -- where the variable isn't bound in the context
                    -- at all.


    step :: Statement abt -> Maybe (M abt (Whnf abt a))
    step (SBind y e) = do
        Refl <- varEq x y
        Just $ do
            w <- error "TODO: update{SBind}" -- caseLazy e return perform
            naivePush (SLet x $ Whnf_ w)
            return (Neutral $ var x)
    step (SLet y e) = do
        Refl <- varEq x y
        Just $ do
            w <- caseLazy e return evaluate
            naivePush (SLet x $ Whnf_ w)
            return (Neutral $ var x)
    step (SBranch ys pat e)
        | varElem x ys = Just $ do
            w <- caseLazy e return evaluate
            updateBranch ys pat w
    step _ = Nothing

    -- TODO: we must be sure to push @SBranch ys pat (Whnf_ w)@ or whatever 'Assocs' it reduces to back onto the context. Otherwise, we'll lose variable bindings!
    updateBranch
        :: forall xs b
        .  List1 Variable xs
        -> Pattern xs b
        -> Whnf abt b
        -> M abt (Whnf abt a)
    updateBranch ys pat w =
        let residualizeCase e = M $ \c h ->
                Neutral . syn $ Case_ e
                    [ Branch pat $
                        case eqAppendIdentity ys of
                        Refl -> binds ys (fromWhnf $ c (Neutral $ var x) h)
                    , Branch PWild $
                        error "TODO: update{SBranch}: other branches" -- for the case where we're in the 'M'' monad rather than the 'M' monad, we can use 'P.reject' here...
                    ]
        in
        case w of
        Neutral e -> residualizeCase e
        Head_   v ->
            case matchTopPattern (fromHead v) pat ys of
            Just (Matched ss _) -> naivePushes (toStatements ss) >> update x
            Just GotStuck       -> residualizeCase (fromHead v)
            Nothing             -> error "TODO: updateBranch" -- P.reject


-- TODO: move this to ABT.hs\/Variable.hs
varElem :: Variable a -> List1 Variable xs -> Bool
varElem x Nil1         = False
varElem x (Cons1 y ys) = varEq_ x y || varElem x ys

varEq_ :: Variable a -> Variable b -> Bool
varEq_ x y = maybe False (const True) (varEq x y)


----------------------------------------------------------------
-- TODO: generalize this to return any @M abt r@
-- | Try to match against a set of branches. If matching succeeds,
-- then push the bindings onto the 'Context' and call the continuation.
-- If matching gets stuck, then residualize the case expression.
-- If matching fails, then throw an error.
--
-- TODO: rather than throwing a Haskell error, instead capture the possibility of failure in the 'M' monad.
--
-- TODO: rather than giving up and residualizing the 'Case_' so quickly when we get stuck, have 'GotStuck' return some info about what needs to be forced next (or if it really is stuck because of a neutral term).
tryMatch
    :: (ABT abt)
    => abt '[] a
    -> [Branch a abt b]
    -> (abt '[] b -> M abt (Whnf abt b))
    -> M abt (Whnf abt b)
tryMatch e bs k =
    case matchBranches e bs of
    Nothing                    -> error "tryMatch: nothing matched!"
    Just (GotStuck    , _)     -> return . Neutral . syn $ Case_ e bs
    Just (Matched ss _, body') -> pushes (toStatements ss) body' k


type DList a = [a] -> [a]

toStatements
    :: DList (Assoc abt)
    -> [Statement abt]
toStatements = map (\(Assoc x e) -> SLet x $ Thunk e) . ($ [])


----------------------------------------------------------------
-- BUG: need to improve the types so they can capture polymorphic data types
class Interp a a' | a -> a' where
    reify   :: (ABT abt) => Head abt a -> a'
    reflect :: (ABT abt) => a' -> Head abt a

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
-- TODO: generalize matchBranches\/MatchResult to allow any sort of continuation...
-- BUG: """Could not deduce (Eq1 (abt '[])) arising from a use of ‘==’"""
instance Interp HUnit () where
    reflect () = WValue $ VDatum dUnit
    reify w =
        -- HACK!!!
        let d = case w of
                WValue (VDatum d) -> fmap11 P.value_ d
                WDatum         d  -> d
        in
        if d == dUnit
        then ()
        else error "reify{HUnit}: the impossible happened"

instance Interp HBool Bool where
    reflect = WValue . VDatum . (\b -> if b then dTrue else dFalse)
    reify w =
        -- HACK!!!
        let d = case w of
                WValue (VDatum d) -> fmap11 P.value_ d
                WDatum         d  -> d
        in
        if d == dTrue  then True  else
        if d == dFalse then False else
        error "reify{HBool}: the impossible happened"

instance (Interp a a', Interp b b')
    => Interp (HPair a b) (a',b')
    where
    reify =
    reflect (a,b) = P.pair a b

instance (Interp a a', Interp b b')
    => Interp (HEither a b) (Either a' b')
    where
    reify =
    reflect (Left  a) = P.left  a
    reflect (Right b) = P.right b

instance (Interp a a') => Interp (HMaybe a) (Maybe a') where
    reify =
    reflect Nothing  = P.nothing
    reflect (Just a) = P.just a

instance (Interp a a') => Interp (HList a) [a'] where
    reify =
    reflect []     = P.nil
    reflect (x:xs) = P.cons x xs
-}


rr1 :: (ABT abt, Interp a a', Interp b b')
    => (a' -> b')
    -> (abt '[] a -> abt '[] b)
    -> abt '[] a
    -> M abt (Whnf abt b)
rr1 f' f e = do
    w <- evaluate e
    return $
        case w of
        Head_   v  -> Head_ . reflect $ f' (reify v)
        Neutral e' -> Neutral $ f e'


rr2 :: (ABT abt, Interp a a', Interp b b', Interp c c')
    => (a' -> b' -> c')
    -> (abt '[] a -> abt '[] b -> abt '[] c)
    -> abt '[] a
    -> abt '[] b
    -> M abt (Whnf abt c)
rr2 f' f e1 e2 = do
    w1 <- evaluate e1
    w2 <- evaluate e2
    return $
        case (w1,w2) of
        (Head_ v1, Head_ v2) -> Head_ . reflect $ f' (reify v1) (reify v2)
        _                    -> Neutral $ f (fromWhnf w1) (fromWhnf w2)


impl, diff, nand, nor :: Bool -> Bool -> Bool
impl x y = not x || y
diff x y = x && not y
nand x y = not (x && y)
nor  x y = not (x || y)

natRoot :: (Floating a) => a -> Nat -> a
natRoot x y = x ** recip (fromIntegral (fromNat y))


----------------------------------------------------------------
evaluateNaryOp :: NaryOp a -> Seq (abt '[] a) -> M abt (Whnf abt a)
evaluateNaryOp = error "TODO: evaluateNaryOp"
{-
evaluateNaryOp o es = foldBy (interp o) <$> T.traverse evaluate es
    where
    -- The evaluation interpretation of each NaryOp
    op And      =
    op Or       =
    op Xor      =
    op Iff      =
    op (Min  _) =
    op (Max  _) =
    op (Sum  _) =
    op (Prod _) =
    
    -- Either actually interpret @op o x y@ or else residualize it
    interp o x y =
    
    -- TODO: group things like values to do them all at once, keeping the neutrals til the very end
    foldBy f vs = 
-}


----------------------------------------------------------------
evaluatePrimOp
    :: (ABT abt, typs ~ UnLCs args, args ~ LCs typs)
    => PrimOp typs a
    -> SArgs abt args
    -> M abt (Whnf abt a)
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
-- N.B., that return type is correct, albeit strange. The idea is that the continuation takes in the variable of type @a@ bound by the expression of type @'HMeasure a@. However, this requires that the continuation of the 'Ans' type actually does @forall a. ...('HMeasure a)@ which is at odds with what 'evaluate' wants (or at least, what *I* think it should want.)
-- BUG: eliminate the 'SingI' requirement (comes from using @(P.>>=)@)
perform
    :: (ABT abt, SingI a) => abt '[] ('HMeasure a) -> M' abt (Whnf abt a)
perform e0 =
    caseVarSyn e0 (error "TODO: perform{Var}") $ \t ->
        case t of
        Dirac :$ e1 :* End ->
            m2mprime $ evaluate e1
        MeasureOp_ _ :$ _ ->
            M' $ \c h -> Head_ $ WMeasure (e0 P.>>= \z -> fromWhnf (c (Neutral z) h))
        MBind :$ e1 :* e2 :* End ->
            caseBind e2 $ \x e2' ->
                push' (SBind x $ Thunk e1) e2' perform
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
            w <- m2mprime (evaluate e0)
            case w of
                Head_   v -> perform (fromHead v)
                Neutral e -> M' $ \c h -> Head_ $ WMeasure (e P.>>= \z -> fromWhnf (c (Neutral z) h))


----------------------------------------------------------------
----------------------------------------------------------- fin.
