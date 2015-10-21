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
--                                                    2015.10.21
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

import           Data.IntMap           (IntMap)
import qualified Data.IntMap           as IM
import qualified Data.Text             as Text
import           Data.Number.LogFloat  (LogFloat)
#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..))
#endif

import Language.Hakaru.Syntax.IClasses (Eq1(..), List1(..), fmap21)
import Language.Hakaru.Syntax.Nat      (Nat, fromNat)
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.TypeEq
import Language.Hakaru.Syntax.Coercion
import Language.Hakaru.Syntax.AST
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
        ifM (equal_ a x) >>= \b -> if b then return () else reject
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
            _                  -> reject
    -}

----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: keep track of the original 'Variable', for its hint!
--
-- | A location is essentially the same thing as a variable (namely
-- for variable bound to some value), except that we brand it with
-- the @s@ to keep track of the 'Context' it belongs to.
newtype Loc s (a :: Hakaru) = Loc Nat
    deriving (Show)

instance Eq (Loc s a) where
    (==) = eq1
instance Eq1 (Loc s) where
    eq1 (Loc m) (Loc n) = m == n
-- Alas, no JmEq1 instance


-- | Lists of locations, not necessarily all of the same type.
type Locs s xs = List1 (Loc s) xs


-- | Weak head-normal forms.
-- TODO: we should distinguish between true-WHNFs and neutral terms!
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
-- BUG: how to capture that @abt@ in the type without making things too ugly for the case where @rec ~ Lazy s (abt '[])@ ?
    -- Neutral terms: (TODO: should we rename the type? These aren't typically considered part of head-normal form since they're not heads; albeit they are normal forms...)
    WhnfNeutral :: abt '[] a -> Whnf rec a
-}


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
data Statement s abt where
    SBind
        :: {-# UNPACK #-} !(Loc s a)
        -> {-# UNPACK #-} !(Lazy s abt a)
        -> Statement s abt
    SLet
        :: {-# UNPACK #-} !(Loc s a)
        -> !(Whnf (L s abt) a)
        -> Statement s abt
    SCase
        :: !(Locs s xs)
        -> !(Pattern xs a)
        -> {-# UNPACK #-} !(Lazy s abt a)
        -> Statement s abt
    SWeight 
        :: {-# UNPACK #-} !(Lazy s abt 'HProb)
        -> Statement s abt


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
data Context s abt = Context
    { freshNat   :: {-# UNPACK #-} !Nat
    , statements :: [Statement s abt] -- stored in reverse order.
    }
-- TODO: to the extent that we can ignore order of statements, we could use an @IntMap (Statement s abt)@ in order to speed up the lookup times in 'updateBy'. We just need to figure out (a) what to do with 'SWeight' statements, (b) how to handle 'SCase' so that we can update just once despite possibly binding multiple variables, and (c) figure out how to recover the order (to the extent that we must).

emptyContext :: Context s abt
emptyContext = Context 0 []

{-
-- | Given a context and a final statement, print them out as a complete expression.
residualizeContext
    :: (ABT abt)
    => Context s abt
    -> abt '[] ('HMeasure a)
    -> abt '[] ('HMeasure a)
residualizeContext = (runResidualizer .) . go . statements
    where
    -- TODO: something like this, where the Residualiser monad keeps track of a Loc-to-Variable mapping and 'freshVariable' adds a new entry in that mapping...
    go [] e =
        return e
    go (SBind loc body : ss) e = do
        x    <- freshVariable loc
        rest <- go ss e
        return $ syn (MBind :$ fromLazy body :* bind x rest :* End)
    go (SLet loc body : ss) e = do
        x    <- freshVariable loc
        rest <- go ss e
        return $ syn (Let_ :$ fromWhnf_L body :* bind x rest :* End)
    go (SCase locs pat body : ss) e = do
        xs   <- freshVariables locs
        rest <- go ss e
        return $ syn (Case_ (fromLazy body)
            [ Branch pat   rest
            , Branch PWild (P.superpose [])
            ])
    go (SWeight body : ss) e = do
        rest <- go ss e
        return (P.weight (fromLazy body) P.*> rest)
-}

----------------------------------------------------------------
-- TODO: is that actually Whnf like the paper says? or is it just any term?
type Ans s abt a = Context s abt -> Whnf (L s abt) ('HMeasure a)

-- TODO: replace the use of 'Ans' in the continuation with the defunctionalized verson.
newtype M s abt x = M { unM :: forall a. (x -> Ans s abt a) -> Ans s abt a }

instance Functor (M s abt) where
    fmap f (M m)  = M $ \c -> m (c . f)

instance Applicative (M s abt) where
    pure x        = M $ \c -> c x
    M mf <*> M mx = M $ \c -> mf $ \f -> mx $ \x -> c (f x)

instance Monad (M s abt) where
    return    = pure
    M m >>= k = M $ \c -> m $ \x -> unM (k x) c

freshLoc :: M s abt (Loc s a)
freshLoc = M $ \c h@Context{freshNat=n} -> c (Loc n) h{freshNat = 1+n}

push :: Statement s abt -> M s abt ()
push s = M $ \c h -> c () h{statements = s : statements h}

pushes :: [Statement s abt] -> M s abt ()
pushes ss = M $ \c h -> c () h{statements = ss ++ statements h}

pop :: M s abt (Statement s abt)
pop = M $ \c h ->
    case statements h of
    []   -> error "pop: empty context!"
    s:ss -> c s h{statements = ss}

{-
-- TODO: should the body really return @Whnf (L s abt) a@ or would @Whnf (abt '[]) a@ also work? Better/worse? cf., type mismatch between 'SLet' and 'evaluate'
updateBy
    :: Loc s a
    -> (Statement s abt -> M s abt (Whnf (L s abt) a))
    -> M s abt ()
updateBy l k = go []
    where
    go ss = do
        s <- pop
        case s `isBindingFor` l of
            Nothing   -> go (s:ss)
            Just Refl -> do
                v <- k s
                push   (SLet l v)
                pushes (reverse ss)

    -- BUG: no 'JmEq1' instance for 'Loc'
    isBindingFor (SBind l  _)   l' = jmEq1 l l'
    isBindingFor (SLet  l  _)   l' = jmEq1 l l'
    isBindingFor (SCase ls _ _) l' = l' `elem` ls
    isBindingFor (SWeight  _)   _  = Nothing
-}

----------------------------------------------------------------         
{-
-- | A partially defunctionalized representation of @x -> Ans s abt a@.
data DisintegrationCont s abt x a where
    -- The first argument is a difference list of ContextEffects
    -- TODO: for defunctionalizing the second argument: how can we get @Whnf (L s abt)@ to have an open-term variant like @abt '[ x ] a@?
    DC  :: (ContextCont s abt -> ContextCont s abt)
        -> (x -> Whnf (L s abt) ('HMeasure a))
        -> DisintegrationCont s abt x a

composeDC
    :: DisintegrationCont s abt (Whnf (L s abt) ('HMeasure b)) c
    -> DisintegrationCont s abt x b
    -> DisintegrationCont s abt x c
composeDC (DC k2 c2) (DC k1 c1) = DC (k1 . k2) (c2 . c1)

newtype N s abt x =
    N { unN :: forall a. DisintegrationCont s abt x a -> Ans s abt a }

instance Functor (N s abt) where
    fmap f (N n)  = N $ \ (DC k c) -> n $ DC k (c . f)

instance Applicative (N s abt) where
    pure x    = N $ \ (DC _ c) _ -> c x
    nf <*> nx = nf >>= (<$> nx) -- TODO: optimize?

instance Monad (N s abt) where
    return    = pure
    N n >>= f = N $ \ (DC k c) h -> n (DC k $ \x -> unN (f x) (DC k c) h) h
        -- TODO: optimize so we don't have to keep evaluating @k h@!!


-- | A defunctionalization of the heap-to-heap transformation
-- contained in the continuation argument for the four primitive
-- functions. Should be paired with some @abt '[x] a@ representing
-- the term-to-term transformation of the same continuation.
type ContextCont s abt = [ContextEffect s abt] 

data ContextEffect s abt where
    -- | Used in the @perform (MBind g e)@ case to push an 'SBind'
    Store :: Statement s abt -> ContextEffect s abt

    -- | Used for the cases of @evaluate (Var x)@ and @constrainValue (Var x)@
    Update :: Loc s a -> Whnf (L s abt) a -> ContextEffect s abt

runContextCont :: ContextCont s abt -> M s abt ()
runContextCont []                   = return ()
runContextCont (Store  entry   : k) = push  entry   >> runContextCont k
runContextCont (Update loc val : k) = update loc val >> runContextCont k
-}

----------------------------------------------------------------
data L s abt a = L
    { forward  :: M s abt (Whnf (L s abt) a)
    , backward :: Whnf (L s abt) a -> M s abt ()
    }


-- | Hide an existentially quantified parameter.
-- TODO: move elsewhere.
-- TODO: replace 'SomeVariable' with @(Some Variable)@
data Some :: (k -> *) -> * where
    Some :: !(f a) -> Some f

-- TODO: data C abt a = C { unC :: Fin n -> [Vec (Some abt) n -> a] }
data C abt a = C { unC :: Nat -> [[Some abt] -> a] }

type Lazy s abt a = L s (C abt) a

{-
----------------------------------------------------------------
disintegrate
    :: (ABT abt, SingI a, SingI b) -- Backward a a
    => abt '[] ('HMeasure (HPair a b))
    -> abt '[] (a ':-> 'HMeasure b) -- this Hakaru function is measurable
disintegrate m =
    P.lam $ \a ->
    fromWhnf $ unM (perform m) (\ab ->
      unM (constrainValue (fst ab) a) (\h' ->
        residualizeContext h' (P.dirac $ P.snd ab)))
      emptyContext


-- TODO: should that actually be Whnf or are neutral terms also allowed?
perform  :: abt '[] ('HMeasure a) -> M s abt (Whnf (abt '[]) a)
perform u | atomic u         = M $ \c h -> u P.>>= \z -> c z h
perform Lebesgue             = M $ \c h -> P.lebesgue P.>>= \z -> c z h
perform (Uniform lo hi)      = M $ \c h -> P.uniform lo hi P.>>= \z -> c z h
perform (Dirac e)            = evaluate e
perform (MBind g (bind x e)) = push (SBind x g) >> perform e
perform (Superpose es)       = P.superpose <$> T.traverse perform es
perform e | not (hnf e)      = evaluate e >>= perform


-- TODO: should that actually be Whnf or are neutral terms also allowed?
evaluate :: abt '[] a -> M s abt (Whnf (abt '[]) a)
evaluate v       | hnf v          = return v
evaluate (Fst e) | not (atomic e) = evaluate e >>= (evaluate . fst)
evaluate (Snd e) | not (atomic e) = evaluate e >>= (evaluate . snd)
evaluate (Negate e)               = negate <$> evaluate e
evaluate (Recip e)                = recip  <$> evaluate e
evaluate (Plus  e1 e2)            = (+)    <$> evaluate e1 <*> evaluate e2
evaluate (Times e1 e2)            = (*)    <$> evaluate e1 <*> evaluate e2
evaluate (LE    e1 e2)            = (<=)   <$> evaluate e1 <*> evaluate e2
evaluate (Var x) =
    -- TODO: do these get the effects in the right order?
    updateBy x $ \binding ->
        case binding of
        SBind  _ e -> perform e
        SLeft  _ e -> evaluate e >>= (`unleft`  evaluate)
        SRight _ e -> evaluate e >>= (`unright` evaluate)
    {-
    M $ \c h ->
        case lookup x h of
        Missing -> error "evaluate: variable is missing in heap!"
        Found h1 binding h2 ->
            case binding of
            SBind x e ->
                -- This is the only line with \"side effects\"
                unM (perform e) (\v h1' -> c v (glue h1' (SLet x v) h2)) h1
            SLeft x e ->
                unM (evaluate e) (\v ->
                unleft v (\e' ->
                unM (evaluate e') (\v' h1' ->
                c v (glue h1' (SLet x v) h2))) h1
            SRight x e ->
                unM (evaluate e) (\v ->
                unright v (\e' ->
                unM (evaluate e') (\v' h1' ->
                c v (glue h1' (SLet x v) h2))) h1
    -}


-- TODO: do we really need to allow all Whnf, or do we just need
-- variables (or neutral terms)? Do we actually want (hnf)terms at
-- all, or do we want (hnf)patterns or something to more generally
-- capture (hnf)measurable events?
constrainOutcome :: abt '[] ('HMeasure a) -> Whnf (abt '[]) a -> M s abt ()
constrainOutcome e0 v =
    case e0 of
    u | atomic u    -> M $ \c h -> P.bot
    Lebesgue        -> M $ \c h -> c h
    Uniform lo hi   -> M $ \c h -> P.observe (lo P.<= v P.&& v P.<= hi) P.>> P.weight (P.recip (hi P.- lo)) P.>> c h
    Return e        -> constrainValue e v
    MBind g (bind x e) -> push (SBind x g) >> constrainOutcome e v
    Superpose es    -> P.uperpose <$> T.traverse (`constrainOutcome` v) es
    e | not (hnf e) -> (`constrainOutcome` v) =<< evaluate e

-- TODO: see the todo for 'constrainOutcome'
constrainValue :: abt '[] a -> Whnf (abt '[]) a -> M s abt ()
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

unleft :: Whnf abt (HEither a b) -> M s abt (abt '[] a)
unleft (Left  e) = M $ \c h -> c e h
unleft (Right e) = M $ \c h -> reject
unleft u         = M $ \c h -> P.uneither u (\x -> c x h) (\_ -> reject)

unright :: Whnf abt (HEither a b) -> M s abt (abt '[] a)
unright (Right e) = M $ \c h -> c e h
unright (Left  e) = M $ \c h -> reject
unright u         = M $ \c h -> P.uneither u (\_ -> reject) (\x -> c x h)
-}

----------------------------------------------------------------
----------------------------------------------------------- fin.
