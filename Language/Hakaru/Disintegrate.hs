{-# LANGUAGE CPP
           , GADTs
           , EmptyCase
           , KindSignatures
           , DataKinds
           , PolyKinds
           , TypeOperators
           , ScopedTypeVariables
           , RankNTypes
           , MultiParamTypeClasses
           , TypeSynonymInstances
           , FlexibleInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.24
-- |
-- Module      :  Language.Hakaru.Disintegrate
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- This is a fork of the old "Language.Hakaru.Lazy" to work with our new
-- AST.
--
-- TODO: capture in the type signatures when things allow the use
-- of 'Lub' vs when they do not.
----------------------------------------------------------------
module Language.Hakaru.Disintegrate
    ( disintegrate
    , density
    , observe
    , determine
    , Backward(..)
    ) where

import           Data.Number.LogFloat  (LogFloat)
#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..))
#endif

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.Nat      (Nat)
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.DatumCase
import Language.Hakaru.Syntax.ABT
import qualified Language.Hakaru.Syntax.Prelude as P
import Language.Hakaru.Expect (total)

----------------------------------------------------------------

-- BUG: get rid of the SingI requirements
-- N.B., the old version used to use the @env@ hack in order to handle the fact that free variables can change their type (eewww!!); we may need to do that again, but we should avoid it if we can possibly do so.
-- N.B., the Backward requirement is probably(?) phrased to be overly strict
-- | This function fils the role that the old @runDisintegrate@ did. It's unclear what exactly the old @disintegrate@ was supposed to be doing...
disintegrate
    :: (ABT abt, SingI a, SingI b, Backward a a)
    => abt '[] ('HMeasure (HPair a b))
    -> abt '[] (a ':-> 'HMeasure b) -- this Hakaru function is measurable
disintegrate m =
    error "TODO: disintegrate"
{-
    runCompose $
    P.lam $ \x ->
    runLazy $
    P.snd <$> conditionalize (P.pair (lazy . return $ Value x) P.unit) m
    -- N.B., I think that use of @unit@ is for giving a "don't care" pattern; rather than actually having anything to do with the @HUnit@ type. We should avoid this by having 'conditionalize' actually accept some form of pattern (for possible observations) rather than accepting terms.
    -- TODO: can we lift the @lam(\x ->@ over the @runCompose@? if so, then we can make sure those functions only need to be called inside 'conditionalize'
-}


-- BUG: get rid of the SingI requirements
-- N.B., the old version used to use the @env@ hack in order to handle the fact that free variables can change their type (eewww!!); we may need to do that again, but we should avoid it if we can possibly do so.
-- N.B., we intentionally phrase the Backward requirement to be overly strict
density
    :: (ABT abt, SingI a, Backward a a)
    => abt '[] ('HMeasure a)
    -> abt '[] (a ':-> 'HProb) -- TODO: make this a Haskell function?
density m =
    P.lam $ \x -> total (conditionalize x m)
    -- BUG: we need to wrap @x@ in the @scalar0@ wrapper before handing it to 'conditionalize'
    -- @scalar0@ means forward is no-op and backward is bot.
{-
    [ \x -> total (d `app` x)
    | d <- runCompose $
        P.lam $ \x ->
        runLazy $
        conditionalize (lazy . return $ Value x) m
    ]
=== {assuming: (`app` x) <$> runCompose f == runCompose (f `app` x) }
    P.lam $ \x ->
    total $
    runCompose $
    runLazy $
    conditionalize (lazy . return $ Value x) m
-}


-- BUG: get rid of the SingI requirements
-- N.B., the old version used to use the @env@ hack (but not on the first argument) in order to handle the fact that free variables can change their type (eewww!!); we may need to do that again, but we should avoid it if we can possibly do so.
-- TODO: what's the point of having this function instead of just using @disintegrate m `app` x@ ? I.E., what does the @scalar0@ wrapper actually achieve; i.e., how does it direct things instead of just failing when we try to go the wrong direction?
-- BUG: come up with new names avoid name conflict vs the Prelude function.
observe
    :: (ABT abt, SingI a, SingI b, Backward a a)
    => abt '[] a
    -> abt '[] ('HMeasure (HPair a b))
    -> abt '[] ('HMeasure b)
observe x m =
    {- runCompose $ -}
    {- runLazy $ -}
    P.snd P.<$> conditionalize (P.pair x P.unit) m
    -- TODO: can we lift the @(snd <$>)@ over the @runCompose@ and @runLazy@ functions? if so, then we can make sure those functions only need to be called inside 'conditionalize'
    -- N.B., see the note at 'disintegrate' about the use of @unit@ here...


-- N.B., all arguments used to have type @Lazy s repr@ instead of @abt '[]@
-- | This is what used to be called @disintegrate@. I think this new name captures whatever it is that funtion was actually supposed to be doing?
--
-- The first argument is a representation of a projection function followed by equality; for example @(pair x unit)@ rather than @(x ==) . fst@. This trick isn't used in the paper, and probably doesn't generalize...
--
-- TODO: whatever this function is supposed to do, it should probably be the one that's the primop rather than 'disintegrate'.
conditionalize
    :: (ABT abt, Backward ab a)
    => abt '[] a
    -> abt '[] ('HMeasure ab)
    -> abt '[] ('HMeasure ab)
conditionalize a m =
    error "TODO: conditionalize"
    {-
    let n = do
            x  <- forward m
            ab <- memo (unMeasure x)
            backward_ ab a
            return ab
    in Lazy (return . Measure $ Lazy (n >>= forward) (\t -> n >>= (`backward` t))) (\_ -> M $ \_ _ -> bot)
    -}


-- | Eliminate uses of 'Lub_' by chosing one of the alternatives
-- arbitrarily. In the future, this function should be replaced by
-- a better one that takes some sort of strategy for deciding which
-- alternative to choose.
--
-- HACK: it's unclear (to me) whether this is actually the same as
-- the function of the same name in "Language.Hakaru.Lazy".
--
-- TODO: should we return @Maybe (abt '[] a)@ or should we allow @bot@ at the very top level of the result?
determine :: (ABT abt) => abt '[] a -> abt '[] a
determine m = error "TODO: determine"

----------------------------------------------------------------
-- BUG: replace all the -XTypeSynonymInstances with a single general instance for all @'HData@

class Backward (b :: Hakaru) (a :: Hakaru) where
    {-
    backward_ :: (ABT abt) => Lazy s abt b -> Lazy s abt a -> M s abt ()
    -}

instance Backward a HUnit where
    {-
    backward_ _ _ = return ()
    -}

instance Backward HBool HBool where
    {-
    backward_ a x =
        ifM (equal_ a x) >>= \b -> if b then return () else P.reject
    -}

instance Backward 'HInt 'HInt where
    {-
    backward_ a x = forward x >>= backward a
    -}

instance Backward 'HReal 'HReal where
    {-
    backward_ a x = forward x >>= backward a
    -}

instance Backward 'HProb 'HProb where
    {-
    backward_ a x = forward x >>= backward a
    -}

instance (Backward a x, Backward b y)
    => Backward (HPair a b) (HPair x y)
    where
    {-
    backward_ ab xy = do
        (a,b) <- unpairM ab
        (x,y) <- unpairM xy
        backward_ a x
        backward_ b y
    -}

instance (Backward a x, Backward b y)
    => Backward (HEither a b) (HEither x y)
    where
    {-
    backward_ ab xy = do
        a_b <- uneitherM ab
        x_y <- uneitherM xy
        case (a_b, x_y) of
            (Left  a, Left  x) -> backward_ a x
            (Right b, Right y) -> backward_ b y
            _                  -> P.reject
    -}

----------------------------------------------------------------
----------------------------------------------------------------
-- N.B., when putting things into the context, be sure to freshen the variables as if we were allocating a new location on the heap.

-- For simplicity we don't actually distinguish between "variables" and "locations". In the old finally-tagless code we had an @s@ parameter like the 'ST' monad does in order to keep track of which heap things belong to. But since we might have nested disintegration, and thus nested heaps, doing that means we'd have to do some sort of De Bruijn numbering in the @s@ parameter in order to keep track of the nested regions; and that's just too much work to bother with.



-- | Weak head-normal forms.
-- TODO: or did we really mean (strong) head-normal forms?
-- TODO: we should distinguish between true (W)HNFs and neutral terms!
data Whnf :: (Hakaru -> *) -> Hakaru -> * where
    -- TODO: use Natural, Integer, Rational, NonNegativeRational!
    -- 'Value'-like things:
    WhnfNat  :: {-# UNPACK #-} !Nat      -> Whnf rec 'HNat
    WhnfInt  :: {-# UNPACK #-} !Int      -> Whnf rec 'HInt
    WhnfProb :: {-# UNPACK #-} !LogFloat -> Whnf rec 'HProb
    WhnfReal :: {-# UNPACK #-} !Double   -> Whnf rec 'HReal
    WhnfDatum
        :: {-# UNPACK #-} !(Datum rec (HData' t))
        -> Whnf rec (HData' t)

    -- Other stuff:
    -- TODO: Is this truly a WHNF or is it a HNF?
    -- TODO: add strictness?
    WhnfArray :: rec 'HInt -> (rec 'HInt -> rec a) -> Whnf rec ('HArray a)
    -- TODO: shouldn't there be an @WhnfLam@?
    -- TODO: should probably be separated out, since this doesn't really fit with our usual notion of head-normal forms...
    WhnfMeasure :: rec a -> Whnf rec ('HMeasure a) -- TODO: not sure what's going on here...
    
{-
-- BUG: how to capture that @abt@ in the type without making things too ugly for the case where @rec ~ Lazy s (abt '[])@ ? Or should this really be @rec@ rather than @abt '[]@ ?
    -- Neutral terms: (TODO: should we rename the type? These aren't typically considered part of head-normal form since they're not heads; albeit they are normal forms...)
    WhnfNeutral :: abt '[] a -> Whnf rec a
-}

-- | A neutral term; i.e., a term whose reduction is blocked by a free variable.
neutral :: abt '[] a -> Whnf rec a
neutral = error "TODO: Neutral"

-- | A thunk; i.e., any term we decide to maybe evaluate later.
-- TODO: this isn't a 'Whnf' in any sense; but is only here because 'Statement' says we need 'Whnf' rather than some other more general thing...
thunk :: abt '[] a -> Whnf rec a
thunk = error "TODO: Thunk"


-- | formerly called @forget@, but this seems like a better name
fromWhnf :: (ABT abt) => Whnf (abt '[]) a -> abt '[] a
fromWhnf (WhnfNat   n) = P.nat_   n
fromWhnf (WhnfInt   i) = P.int_   i
fromWhnf (WhnfProb  p) = P.prob_  p
fromWhnf (WhnfReal  r) = P.real_  r
fromWhnf (WhnfDatum d) = P.datum_ d
-- TODO: fromWhnf (WhnfNeutral e) = e
fromWhnf _ = error "fromWhnf: these cases should never be reached" -- TODO: why not be able to residualize WhnfMeasure and WhnfArray? even if they aren't reached in the stated use of this function, they should still make some amout of sense, ne?


----------------------------------------------------------------
-- | A single statement in the @HMeasure@ monad, where bound variables
-- are considered part of the \"statement\" that binds them rather
-- than part of the continuation. Thus, non-binding statements like
-- @Weight@ are also included here.
--
-- This type was formerly called @Binding@, but that is inaccurate
-- since it also includes non-binding statements.
--
-- TODO: should these really all be 'Whnf' (or even the sum of WHNF and neutral terms)? Shouldn't we be allowed to have arbitrary not at all normal forms if we are, in fact, doing *lazy* partial evaluation?
data Statement abt where
    SBind
        :: {-# UNPACK #-} !(Variable a) -- was @Loc s a@
        -> !(Whnf (abt '[]) ('HMeasure a)) -- was @Lazy s abt a@
        -> Statement abt
    SLet
        :: {-# UNPACK #-} !(Variable a) -- was @Loc s a@
        -> !(Whnf (abt '[]) a) -- was @Whnf (L s abt) a@
        -> Statement abt
    SCase
        :: !(List1 Variable xs) -- was @Locs s xs@
        -> !(Pattern xs a)
        -> !(Whnf (abt '[]) a) -- was @Lazy s abt a@
        -> Statement abt
    SWeight 
        :: !(Whnf (abt '[]) 'HProb) -- was @Lazy s abt 'HProb@
        -> Statement abt
    -- TODO: if we do proper HNFs then we should add all the other binding forms (Lam_, Array_, Expect,...) as \"statements\" too


-- | An ordered collection of statements representing the context
-- surrounding the current focus of our program transformation.
-- That is, since some transformations work from the bottom up, we
-- need to keep track of the statements we passed along the way
-- when reaching for the bottom.
--
-- This type was formerly called @Heap@ (presumably due to the
-- 'Statement' type being called @Binding@) but that seems like a
-- misnomer to me since this really has nothing to do with allocation.
-- However, it is still like a heap inasmuch as it's a dependency
-- graph and we may wish to change the topological sorting or remove
-- \"garbage\" (subject to correctness criteria).
data Context abt = Context
    { freshNat   :: {-# UNPACK #-} !Nat
    , statements :: [Statement abt] -- stored in reverse order.
    }
-- TODO: to the extent that we can ignore order of statements, we could use an @IntMap (Statement abt)@ in order to speed up the lookup times in 'update'. We just need to figure out (a) what to do with 'SWeight' statements, (b) how to handle 'SCase' so that we can just make one map modification despite possibly binding multiple variables, and (c) figure out how to recover the order (to the extent that we must).

emptyContext :: Context abt
emptyContext = Context 0 []

{-
-- | Given a context and a final statement, print them out as a complete expression.
residualizeContext
    :: (ABT abt)
    => Context abt
    -> abt '[] ('HMeasure a)
    -> abt '[] ('HMeasure a)
residualizeContext = (runResidualizer .) . go . statements
    where
    go [] e =
        return e
    go (SBind x body : ss) e = do
        rest <- go ss e
        return $ syn (MBind :$ fromLazy body :* bind x rest :* End)
    go (SLet x body : ss) e = do
        rest <- go ss e
        return $ syn (Let_ :$ fromWhnf_L body :* bind x rest :* End)
    go (SCase xs pat body : ss) e = do
        rest <- go ss e
        return $ syn (Case_ (fromLazy body)
            [ Branch pat   rest
            , Branch PWild P.reject
            ])
    go (SWeight body : ss) e = do
        rest <- go ss e
        return (P.weight (fromLazy body) P.*> rest)
-}

----------------------------------------------------------------
-- TODO: is that actually Whnf like the paper says? or is it just any term?
type Ans abt a = Context abt -> Whnf (abt '[]) a -- was @Whnf (L s abt) ('HMeasure a)@

-- TODO: defunctionalize the continuation. In particular, the only heap modifications we need are 'push' and a variant of 'update' for finding\/replacing a binding once we have the value in hand.
newtype M abt x = M { unM :: forall a. (x -> Ans abt a) -> Ans abt a }

instance Functor (M abt) where
    fmap f (M m)  = M $ \c -> m (c . f)

instance Applicative (M abt) where
    pure x        = M $ \c -> c x
    M mf <*> M mx = M $ \c -> mf $ \f -> mx $ \x -> c (f x)

instance Monad (M abt) where
    return    = pure
    M m >>= k = M $ \c -> m $ \x -> unM (k x) c

{-
-- TODO: use @freshen :: Variable a -> M (Variable a)@ instead; to avoid losing the hint and singleton
freshVar :: M abt (Variable a)
freshVar = M $ \c h@Context{freshNat=n} ->
    c (Variable Text.empty n sing) h{freshNat = 1+n}
-}

push :: Statement abt -> M abt ()
push s = M $ \c h -> c () h{statements = s : statements h}

pushes :: [Statement abt] -> M abt ()
pushes ss = M $ \c h -> c () h{statements = ss ++ statements h}

-- | N.B., this can be unsafe. If a binding statement is returned, then the caller must be sure to push back on statements binding all the same variables!
pop :: M abt (Maybe (Statement abt))
pop = M $ \c h ->
    case statements h of
    []   -> c Nothing  h
    s:ss -> c (Just s) h{statements = ss}

----------------------------------------------------------------
{-
data L s abt a = L
    { forward  :: M s abt (Whnf (L s abt) a)
    , backward :: Whnf (L s abt) a -> M s abt ()
    }

-- TODO: make the length indexing explicit:
-- > data C abt a = C { unC :: forall n. Sing n -> [Vec (Some abt) n -> a] }
--
-- TODO: does the old version actually mean to erase type info? or should we rather use:
-- > data C abt a = C { unC :: forall xs. Sing xs -> [List1 abt xs -> a] }
--
-- TODO: should we add back in something like @C@ for interpreting\/erasing the uses of 'Lub_'?
data C abt a = C { unC :: Nat -> [[Some abt] -> a] }

type Lazy s abt a = L s (C abt) a
-}

----------------------------------------------------------------
----------------------------------------------------------------
{-
disintegrate
    :: (ABT abt, SingI a, SingI b) -- Backward a a
    => abt '[] ('HMeasure (HPair a b))
    -> abt '[] (a ':-> 'HMeasure b) -- ^ this Hakaru function is measurable
disintegrate m =
    P.lam $ \a ->
    fromWhnf $ unM (perform m) (\ab ->
      unM (constrainValue (fst ab) a) (\h' ->
        residualizeContext h' (P.dirac $ P.snd ab)))
      emptyContext
-}

----------------------------------------------------------------
-- | Every value is already in WHNF.
valueToWhnf :: (ABT abt) => Value a -> Whnf (abt '[]) a
valueToWhnf (VNat   n) = WhnfNat   n
valueToWhnf (VInt   i) = WhnfInt   i
valueToWhnf (VProb  p) = WhnfProb  p
valueToWhnf (VReal  r) = WhnfReal  r
valueToWhnf (VDatum d) = WhnfDatum (fmap11 P.value_ d)

type DList a = [a] -> [a]

tryMatch
    :: (ABT abt)
    => abt '[] a
    -> [Branch a abt b]
    -> (abt '[] b -> M abt (Whnf (abt '[]) b))
    -> M abt (Whnf (abt '[]) b)
tryMatch e bs k =
    case matchBranches e bs of
    Nothing                 -> error "tryMatch: nothing matched!" -- TODO: return the Hakaru code for throwing an error instead. Or have some sort of 'fail' option in our monad.
    Just GotStuck           -> return . neutral . syn $ Case_ e bs
    Just (Matched ss body') -> pushes (toStatements ss) >> k body'
    where
    toStatements
        :: DList (Assoc abt)
        -> [Statement abt]
    toStatements = map toStatement . ($ [])
    
    toStatement :: Assoc abt -> Statement abt
    toStatement (Assoc x e) = SLet x (thunk e)

{-
-- TODO: move to ABT.hs and come up with a good name for it.
-- | The inverse of 'binder'; aka \"instantiation\".
($$)
    :: (ABT abt)
    => abt (a ': xs) b
    -> abt '[] a
    -> abt xs  b
f $$ e =
    caseBind f $ \x f' ->
        subst x e f'
    
evaluate :: abt '[] a -> M abt (Whnf (abt '[]) a)
evaluate e =
    caseVarSyn e update $ \t ->
        case t of
        -- Things which are already weak head-normal forms
        _ | isNeutral t    -> return (neutral t) -- 'isNeutral' is called \"atomic\" in the paper.
        Value_ v           -> return (valueToWhnf v)
        Datum_ d           -> return (WhnfDatum d)
        Empty_             -> return WhnfEmpty
        Array_ e1 e2       -> return (WhnfArray e1 e2)
        Lam_ :$ e1 :* End  -> return (WhnfLam e1)
        MeasureOp_ _ :$ _  -> return (WhnfMeasure t)
        MBind        :$ _  -> return (WhnfMeasure t) -- N.B., not HNF
        Superpose_ _       -> return (WhnfMeasure t)
        
        -- Everything else needs some evaluation
        
        App_ :$ e1 :* e2 :* End -> do
            v1 <- evaluate e1
            case v1 of
                WhnfLam f -> evaluate (f $$ e2)
                _         -> return . neutral $ P.app (fromWhnf v1) e2
        
        Let_ :$ e1 :* e2 :* End ->
            caseBind e2 $ \x e2' -> do
                push (SLet x (thunk e1))
                evaluate e2'
        
        Fix_ :$ e1 :* End ->
        
        Ann_        t :$ e1 :* End ->
        CoerceTo_   c :$ e1 :* End ->
        UnsafeFrom_ c :$ e1 :* End ->
        NaryOp_     o    es        -> evaluateNaryOp o es
        PrimOp_     o :$ es        -> evaluatePrimOp o es

        -- TODO: avoid the chance of looping in case 'E.expect' residualizes.
        -- TODO: use 'evaluate' in 'E.expect' in order to partially-NBE @e1@
        Expect :$ e1 :* e2 :* End ->
            evaluate $ E.expect e1 (e2 $$)
        
        Lub_ es -> WhnfLub <$> T.for es evaluate
        
        -- TODO: in the paper there's a guard so that this only fires when @not (atomic e)@. I think that was to prevent infinite loops in case 'evaluate' returns a 'neutral' term. We get around this in the following way... The 'matchBranches' primitive will tell us it 'GotStuck' if it turns out that the value @v@ is not already a 'Datum' (whether as 'Datum_' or as 'Value_')[1]. And whenever 'matchBranches' gets stuck, 'tryMatch' will wrap the whole case expression up as a neutral term.
        --
        -- [1] 'matchBranches' will also tell us it 'GotStuck' if the scrutinee isn't a 'Datum' at some subterm a nested 'Pattern' is trying to match against. At present this means we won't do as much partial evaluation as we really ought to; but in the future the 'GotStuck' constructor should return some information about where it got stuck so that we can 'evaluate' that subexpression. If we were evaluating to full normal forms, this wouldn't be an issue; it's only a problem because we're only doing (W)HNFs.
        Case_ e bs -> do
            v <- evaluate e
            tryMatch (fromWhnf v) bs evaluate



evaluateNaryOp :: NaryOp a -> Seq (abt '[] a) -> M abt (Whnf (abt '[]) a)
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


-- Essentially, these should all do @f <$> evaluate e1 <*> evaluate e2...@ where @f@ is the interpretation of the 'PrimOp', which residualizes as necessary if it gets stuck.
evaluatePrimOp
    :: (typs ~ UnLCs args, args ~ LCs typs)
    => PrimOp typs a
    -> SCon   args a
    -> M abt (Whnf (abt '[]) a)
evaluatePrimOp Not  (e1 :* End)       =
evaluatePrimOp Impl (e1 :* e2 :* End) =
evaluatePrimOp Diff (e1 :* e2 :* End) =
evaluatePrimOp Nand (e1 :* e2 :* End) =
evaluatePrimOp Nor  (e1 :* e2 :* End) =
evaluatePrimOp Pi        End               =
evaluatePrimOp Sin       (e1 :* End)       =
evaluatePrimOp Cos       (e1 :* End)       =
evaluatePrimOp Tan       (e1 :* End)       =
evaluatePrimOp Asin      (e1 :* End)       =
evaluatePrimOp Acos      (e1 :* End)       =
evaluatePrimOp Atan      (e1 :* End)       =
evaluatePrimOp Sinh      (e1 :* End)       =
evaluatePrimOp Cosh      (e1 :* End)       =
evaluatePrimOp Tanh      (e1 :* End)       =
evaluatePrimOp Asinh     (e1 :* End)       =
evaluatePrimOp Acosh     (e1 :* End)       =
evaluatePrimOp Atanh     (e1 :* End)       =
evaluatePrimOp RealPow   (e1 :* e2 :* End) =
evaluatePrimOp Exp       (e1 :* End)       =
evaluatePrimOp Log       (e1 :* End)       =
evaluatePrimOp Infinity         End        =
evaluatePrimOp NegativeInfinity End        =
evaluatePrimOp GammaFunc   (e1 :* End)       =
evaluatePrimOp BetaFunc    (e1 :* e2 :* End) =
evaluatePrimOp Integrate   (e1 :* e2 :* e3 :* End) =
evaluatePrimOp Summate     (e1 :* e2 :* e3 :* End) =
evaluatePrimOp (Index   _) (e1 :* e2 :* End) =
evaluatePrimOp (Size    _) (e1 :* End)       =
evaluatePrimOp (Reduce  _) (e1 :* e2 :* e3 :* End) =
evaluatePrimOp (Equal   _) (e1 :* e2 :* End) =
evaluatePrimOp (Less    _) (e1 :* e2 :* End) =
evaluatePrimOp (NatPow  _) (e1 :* e2 :* End) =
evaluatePrimOp (Negate  _) (e1 :* End)       =
evaluatePrimOp (Abs     _) (e1 :* End)       =
evaluatePrimOp (Signum  _) (e1 :* End)       =
evaluatePrimOp (Recip   _) (e1 :* End)       =
evaluatePrimOp (NatRoot _) (e1 :* e2 :* End) =
evaluatePrimOp (Erf _)     (e1 :* End)       =
-- HACK: GHC can't figure out that there are no other type-safe cases
evaluatePrimOp _ _ = error "evaluatePrimOp: the impossible happened"


----------------------------------------------------------------        
-- TODO: should this really return @Whnf (L s abt) a@ or @Whnf (abt '[]) a@ ? cf., type mismatch between what 'evaluate' gives and what 'SLet' wants.
update :: Variable a -> M abt (Whnf (abt '[]) a)
update x = loop []
    where
    loop ss = do
        ms <- pop
        case ms of
            Nothing -> do
                pushes (reverse ss)
                return (WhnfNeutral (var x))
            Just s  ->
                case step s of
                Nothing -> loop (s:ss)
                Just mv -> do
                    v <- mv             -- evaluate the body of @s@
                    push   (SLet x v)   -- replace @s@ itself
                    pushes (reverse ss) -- put the rest of the context back
                    return v            -- TODO: return (NamedWhnf x v)

    step (SBind  y e) | x == y = Just $ perform  e
    step (SLet   y e) | x == y = Just $ evaluate e
    step (SLeft  y e) | x == y = Just $ evaluate e >>= (`unleft`  evaluate)
    step (SRight y e) | x == y = Just $ evaluate e >>= (`unright` evaluate)
    step _                     = Nothing
          

-- TODO: should that actually be Whnf or are neutral terms also allowed?
perform  :: abt '[] ('HMeasure a) -> M abt (Whnf (abt '[]) a)
perform u | atomic u         = M $ \c h -> u P.>>= \z -> c z h
perform Lebesgue             = M $ \c h -> P.lebesgue P.>>= \z -> c z h
perform (Uniform lo hi)      = M $ \c h -> P.uniform lo hi P.>>= \z -> c z h
perform (Dirac e)            = evaluate e
perform (MBind g (bind x e)) = push (SBind x g) >> perform e
perform (Superpose es)       = P.superpose <$> T.traverse perform es -- TODO: not quite right; need to push the SWeight in each branch
perform e | not (hnf e)      = evaluate e >>= perform


-- TODO: see the todo for 'constrainOutcome'
constrainValue :: abt '[] a -> Whnf (abt '[]) a -> M abt ()
constrainValue e0 v0 =
    case e0 of
    u | atomic u -> M $ \c h -> P.bot
    Real _       -> M $ \c h -> P.bot
    Fst e1 | not (atomic e1) -> evaluate e1 >>= ((`constrainValue` v0) . fst)
    Snd e1 | not (atomic e1) -> evaluate e1 >>= ((`constrainValue` v0) . snd)
    Negate e1 -> constrainValue e1 (negate v0)
    Recip e1 -> M $ \c h -> P.weight (P.recip (v0 P.^ P.nat_ 2)) P.>> unM (constrainValue e1 (recip v0)) c h
    Plus e1 e2 -> M $ \c h ->
        unM (evaluate e1) (\v1 -> unM (constrainValue e2 (v0 - v1)) c) h
        `P.lub`
        unM (evaluate e2) (\v2 -> unM (constrainValue e1 (v0 - v2)) c) h
    Times e1 e2 -> M $ \c h ->
        unM (evaluate e1) (\v1 -> abs v1 (\v1' h' -> P.weight (P.recip v1') P.>> unM (constrainValue e2 (v0 / v1)) c h')) h
        `P.lub`
        unM (evaluate e2) (\v2 -> abs v2 (\v2' h' -> P.weight (P.recip v2') P.>> unM (constrainValue e1 (v0 / v2)) c h')) h
    Var x ->  M $ \c h ->
        case lookup x h of
        Missing -> error "constrainValue: variable is missing in heap!"
        Found h1 binding h2 ->
            case binding of
            SBind _x e1 ->
                unM (constrainOutcome e1 v0) (\h1' -> c (glue h1' (SLet x v0) h2)) h1
            SLeft _x e1 ->
                unM (evaluate e1) (\v1 -> unleft v1 (\e2 -> unM (constrainValue e1 v0) (\h1' -> c (glue h1' (SLet x v0) h2)))) h1
            SRight _x e1 ->
                unM (evaluate e1) (\v1 -> unright v1 (\e2 -> unM (constrainValue e1 v0) (\h1' -> c (glue h1' (SLet x v0) h2)))) h1

-- TODO: do we really need to allow all Whnf, or do we just need
-- variables (or neutral terms)? Do we actually want (hnf)terms at
-- all, or do we want (hnf)patterns or something to more generally
-- capture (hnf)measurable events?
constrainOutcome :: abt '[] ('HMeasure a) -> Whnf (abt '[]) a -> M abt ()
constrainOutcome e0 v =
    case e0 of
    u | atomic u    -> M $ \c h -> P.bot
    Lebesgue        -> M $ \c h -> c h
    Uniform lo hi   -> M $ \c h -> P.observe (lo P.<= v P.&& v P.<= hi) P.>> P.weight (P.recip (hi P.- lo)) P.>> c h
    Return e        -> constrainValue e v
    MBind g (bind x e) -> push (SBind x g) >> constrainOutcome e v
    Superpose es    -> P.superpose <$> T.traverse (`constrainOutcome` v) es -- TODO: not quite right; need to push the SWeight in each branch
    e | not (hnf e) -> (`constrainOutcome` v) =<< evaluate e


unleft :: Whnf abt (HEither a b) -> M abt (abt '[] a)
unleft (Left  e) = M $ \c h -> c e h
unleft (Right e) = M $ \c h -> P.reject
unleft u         = M $ \c h -> P.uneither u (\x -> c x h) (\_ -> P.reject)

unright :: Whnf abt (HEither a b) -> M abt (abt '[] a)
unright (Right e) = M $ \c h -> c e h
unright (Left  e) = M $ \c h -> P.reject
unright u         = M $ \c h -> P.uneither u (\_ -> P.reject) (\x -> c x h)
-}

----------------------------------------------------------------
----------------------------------------------------------- fin.
