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

import Language.Hakaru.Syntax.IClasses (List1(..), fmap21)
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
    SBind :: Loc s a -> Lazy s abt a -> Statement s abt
    SLet  :: Loc s a -> Whnf (L s abt) a -> Statement s abt
    SCase :: Locs s xs -> Pattern xs a -> Lazy s abt a -> Statement s abt
    SWeight :: Lazy s abt 'HProb -> Statement s abt


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

----------------------------------------------------------------
-- TODO: is that actually Whnf like the paper says? or is it just any term?
type Ans s abt a = Context s abt -> Whnf (L s abt) ('HMeasure a)

-- TODO: replace the use of 'Ans' in the continuation with the defunctionalized verson.
newtype M s abt x =
    M { unM :: forall a. (x -> Ans s abt a) -> Ans s abt a }

instance Functor (M s abt) where
    fmap f (M m)  = M $ \c -> m $ \x -> c (f x)

instance Applicative (M s abt) where
    pure a        = M $ \c -> c a
    M mf <*> M mx = M $ \c -> mf $ \f -> mx $ \x -> c (f x)

instance Monad (M s abt) where
    return    = pure
    M m >>= k = M $ \c -> m $ \x -> unM (k x) c


-- | A defunctionalization of the heap-to-heap transformation
-- contained in the continuation argument for the four primitive
-- functions. Should be paired with some @abt '[x] a@ representing
-- the term-to-term transformation of the same continuation.
data ContextCont s abt where
    -- | The initial\/identity continuation.
    Nop :: ContextCont s abt

    -- | Used in the @perform (MBind g e)@ case to push an 'SBind'
    Store :: Statement s abt -> ContextCont s abt -> ContextCont s abt

    -- | Used for the cases of @evaluate (Var x)@ and @constrainValue (Var x)@
    Update :: Loc s a -> Whnf (L s abt) a -> ContextCont s abt -> ContextCont s abt

runContextCont :: ContextCont s abt -> M s abt ()
runContextCont Nop                = return ()
runContextCont (Store  entry   k) = store  entry   >> runContextCont k
runContextCont (Update loc val k) = update loc val >> runContextCont k

freshLoc :: M s abt (Loc s a)
freshLoc = M $ \c h@Context{freshNat=n} -> c (Loc n) h{freshNat = 1+n}

store :: Statement s abt -> M s abt ()
store entry = M $ \c h -> c () h{statements = entry : statements h}

update :: Loc s a -> Whnf (L s abt) a -> M s abt ()
update l v = store (SLet l v) -- TODO: walk the statements to replace the old one

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

--TODO: data C abt a = C { unC :: Fin n -> [Vec (Some abt) n -> a] }
data C abt a = C { unC :: Nat -> [[Some abt] -> a] }

type Lazy s abt a = L s (C abt) a

{-
----------------------------------------------------------------
disintegrate
    :: (ABT abt, SingI a, SingI b) -- Backward a a
    => abt '[] ('HMeasure (HPair a b))
    -> abt '[] (a ':-> 'HMeasure b) -- this Hakaru function is measurable
disintegrate m =
    lam $ \a ->
    fromWhnf $ unM (perform m) (\ab ->
      unM (constrainValue (fst ab) a) (\h' ->
        residuate h' `bind_` dirac (snd ab)))
      emptyContext

-- TODO: should that actually be Whnf or are neutral terms also allowed?
perform  :: abt '[] ('HMeasure a) -> M s abt (Whnf (abt '[]) a)
perform u | atomic u    = M $ \c h -> u `bind` \z -> c z h
perform Lebesgue        = M $ \c h -> Lebesgue `bind` \z -> c z h
perform (Uniform lo hi) = M $ \c h -> Uniform lo hi `bind` \z -> c z h
perform (Dirac e)       = evaluate e
perform (MBind g e)     = M $ \c h -> unM (perform e) c (h `snoc` g) -- TODO: move the bound variable from @e@ into the binding of @g@ we push on the heap
perform (Superpose es)  = Superpose Haskell.<$> T.traverse perform es
perform e | not (hnf e) = M $ \c h -> unM (evaluate e) (\m -> unM (perform m) c) h

-- TODO: should that actually be Whnf or are neutral terms also allowed?
evaluate :: abt '[] a -> M s abt (Whnf (abt '[]) a)
evaluate v | hnf v = M $ \c h -> c v h
evaluate (Fst e) | not (atomic e) = M $ \c h -> unM (evaluate e) (\v -> evaluate (fst v) c) h
evaluate (Snd e) | not (atomic e) = M $ \c h -> unM (evaluate e) (\v -> evaluate (snd v) c) h
evaluate (Negate e) = M $ \c h -> unM (evaluate e) (\v -> c (negate v)) h
evaluate (Recip e) = M $ \c h -> unM (evaluate e) (\v -> c (recip v)) h
evaluate (Plus e1 e2) =
    M $ \c h -> unM (evaluate e1) (\v1 ->
    unM (evaluate e2) (\v2 -> c (e1 + e2))) h
evaluate (Times e1 e2) =
    M $ \c h -> unM (evaluate e1) (\v1 ->
    unM (evaluate e2) (\v2 -> c (e1 * e2))) h
evaluate (LE e1 e2) =
    M $ \c h -> unM (evaluate e1) (\v1 ->
    unM (evaluate e2) (\v2 -> c (e1 <= e2))) h
evaluate (Var x) = M $ \c h ->
    case lookup x h of
    Missing -> error "evaluate: variable is missing in heap!"
    Found h1 binding h2 ->
        case binding of
        SBind _x e ->
            -- This is the only line with \"side effects\"
            unM (perform e) (\v h1' -> c v (glue h1' (SLet x v) h2)) h1
        SLeft _x e ->
            unM (evaluate e) (\v -> unleft v (\e' ->
            unM (evaluate e') (\v' h1' -> c v (glue h1' (SLet x v) h2))) h1
        SRight _x e ->
            unM (evaluate e) (\v -> unright v (\e' ->
            unM (evaluate e') (\v' h1' -> c v (glue h1' (SLet x v) h2))) h1

-- TODO: do we really need to allow all Whnf, or do we just need
-- variables (or neutral terms)? Do we actually want (hnf)terms at
-- all, or do we want (hnf)patterns or something to more generally
-- capture (hnf)measurable events?
constrainOutcome :: abt '[] ('HMeasure a) -> Whnf (abt '[]) a -> M s abt ()
constrainOutcome e0 v =
    case e0 of
    u | atomic u  -> M $ \c h -> bot
    Lebesgue      -> M $ \c h -> c h
    Uniform lo hi -> M $ \c h -> Prelude.observe (lo <= v && v <= hi) `bind_` weight (recip (hi - lo)) `bind_` c h
    Return e      -> constrainValue e v
    Bind g e      -> M $ \c h -> unM (constrainOutcome e v) c (h `snoc` g) -- TODO: move the bound variable from @e@ into the binding of @g@ we push on the heap
    Superpose es ->
        Superpose Haskell.<$> T.traverse (`constrainOutcome` v) es
    e | not (hnf e) -> M $ \c h -> unM (evaluate e) (\m -> unM (constrainOutcome m v) c) h

-- TODO: see the todo for 'constrainOutcome'
constrainValue :: abt '[] a -> Whnf (abt '[]) a -> M s abt ()
constrainValue e0 v0 =
    case e0 of
    u | atomic u -> M $ \c h -> bot
    Real _       -> M $ \c h -> bot
    Fst e1 | not (atomic e1) -> M $ \c h -> unM (evaluate e1) (\v1 -> unM (constrainValue (fst v1) v0) c) h
    Snd e1 | not (atomic e1) -> M $ \c h -> unM (evaluate e1) (\v1 -> unM (constrainValue (snd v1) v0) c) h
    Negate e1 -> constrainValue e1 (negate v0)
    Recip e1 -> M $ \c h -> weight (recip (v0^2)) `bind_` unM (constrainValue e1 (recip v0)) c h
    Plus e1 e2 -> M $ \c h ->
        unM (evaluate e1) (\v1 -> unM (constrainValue e2 (v0 - v1)) c) h
        `lub`
        unM (evaluate e2) (\v2 -> unM (constrainValue e1 (v0 - v2)) c) h
    Times e1 e2 -> M $ \c h ->
        unM (evaluate e1) (\v1 -> abs v1 (\v1' h' -> weight (recip v1') `bind_` unM (constrainValue e2 (v0 / v1)) c h')) h
        `lub`
        unM (evaluate e2) (\v2 -> abs v2 (\v2' h' -> weight (recip v2') `bind_` unM (constrainValue e1 (v0 / v2)) c h')) h
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
unleft u         = M $ \c h -> uneither u (\x -> c x h) (\_ -> reject)

unright :: Whnf abt (HEither a b) -> M s abt (abt '[] a)
unright (Right e) = M $ \c h -> c e h
unright (Left  e) = M $ \c h -> reject
unright u         = M $ \c h -> uneither u (\_ -> reject) (\x -> c x h)
-}

----------------------------------------------------------------
----------------------------------------------------------- fin.
