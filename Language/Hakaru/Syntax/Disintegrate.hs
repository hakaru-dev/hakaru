{-# LANGUAGE GADTs
           , EmptyCase
           , KindSignatures
           , DataKinds
           , TypeOperators
           , NoImplicitPrelude
           , ScopedTypeVariables
           , MultiParamTypeClasses
           , TypeSynonymInstances
           , FlexibleInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.08.18
-- |
-- Module      :  Language.Hakaru.Syntax.Disintegrate
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- This is a fork of "Language.Hakaru.Lazy" to work with our new
-- AST.
--
-- TODO: capture in the type signatures when things allow the use
-- of 'Lub' vs when they do not.
----------------------------------------------------------------
module Language.Hakaru.Syntax.Disintegrate
    ( disintegrate
    , density
    , observe
    , determine
    , Backward(..)
    ) where

import           Prelude (($), (.), flip, map, error, Maybe(..), Either(..))
import           Data.IntMap   (IntMap)
import qualified Data.IntMap   as IM
import qualified Data.Text     as Text

import Language.Hakaru.Syntax.IClasses (fmap21)
import Language.Hakaru.Syntax.Nat      (fromNat)
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.TypeEq
import Language.Hakaru.Syntax.Coercion
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.Prelude hiding (observe)
import Language.Hakaru.Syntax.Expect (total)

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
    -- TODO: actually implement the Disintegrate primop
    primOp1_ (Disintegrate sing sing) m
{-
    runCompose $
    lam $ \x ->
    runLazy $
    snd <$> conditionalize (pair (lazy . return $ Value x) unit) m
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
    lam $ \x -> total (conditionalize x m)
    -- BUG: we need to wrap @x@ in the @scalar0@ wrapper before handing it to 'conditionalize'
    -- @scalar0@ means forward is no-op and backward is bot.
{-
    [ \x -> total (d `app` x)
    | d <- runCompose $
        lam $ \x ->
        runLazy $
        conditionalize (lazy . return $ Value x) m
    ]
=== {assuming: (`app` x) <$> runCompose f == runCompose (f `app` x) }
    lam $ \x ->
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
    snd <$> conditionalize (pair x unit) m
    -- TODO: can we lift the @(snd <$>)@ over the @runCompose@ and @runLazy@ functions? if so, then we can make sure those functions only need to be called inside 'conditionalize'
    -- N.B., see the note at 'disintegrate' about the use of @unit@ here...


-- N.B., all arguments used to have type @Lazy s repr@ instead of @abt '[]@
-- | This is what used to be called @disintegrate@. I think this new name captures whatever it is that funtion was actually supposed to be doing?
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
{-
-- | A location is essentially the same thing as a variable (namely
-- for variable bound to some value), except that we brand it with
-- the @s@ to keep track of the 'Context' it belongs to.
newtype Loc s (a :: Hakaru) = Loc Nat
    deriving (Show)

data Locs s (xs :: [Hakaru]) where
    LNil  :: Locs s '[]
    LCons :: Loc s x -> Locs s xs -> Locs s (x ': xs)

-- | A single statement in the @HMeasure@ monad, where bound variables
-- are considered part of the \"statement\" that binds them rather
-- than part of the continuation. Thus, non-binding statements like
-- @Weight@ are also included here.
--
-- This type was formerly called @Binding@, but that is inaccurate
-- since it also includes non-binding statements.
data Statement s abt where
    SBind :: Loc s a -> Lazy s abt a -> Statement s abt
    SLet  :: Loc s a -> Hnf (L s abt) a -> Statement s abt
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
-- misnomer to me since this really has nothing to do with allocation
-- and does not allow reordering of components as is usually allowed
-- in heaps.
data Context s abt = Context
    { freshNat   :: {-# UNPACK #-} !Nat
    , statements :: [Statement s abt]
    }

freshLoc :: M s abt (Loc s a)
freshLoc = M $ \c h@Context{freshNat=n} -> c (Loc n) h{freshNat = succ n}

store :: Statement s abt -> M s abt ()
store entry = M $ \c h -> c () h{statements = entry : statements h}

update :: Loc s a -> Hnf (L s abt) a -> M s abt ()
update l v = store (SLet l v)

data Hnf rec a where
    -- 'Value'-like things:
    HnfNat  :: {-# UNPACK #-} !Natural     -> Hnf rec 'HNat
    HnfInt  :: {-# UNPACK #-} !Integer     -> Hnf rec 'HInt
    HnfProb :: {-# UNPACK #-} !PosRational -> Hnf rec 'HProb
    HnfReal :: {-# UNPACK #-} !Rational    -> Hnf rec 'HReal
    HnfDatum
        :: {-# UNPACK #-} !(Datum rec ('HData t (Code t)))
        -> Hnf rec ('HData t (Code t))

    -- Other stuff: (TODO: should probably be separated out, since this doesn't really fit with our usual notion of head-normal forms...)
    HnfMeasure :: rec a -> Hnf rec ('HMeasure a) -- TODO: not sure what's going on here...
    HnfArray :: rec 'HInt -> (rec 'HInt -> rec a) -> Hnf rec ('HArray a)
    -- TODO: shouldn't there be an @HnfLam@? (renaming to Whnf as appropriate)
    
    -- Neutral terms: (TODO: should we rename the type? These aren't typically considered part of head-normal form since they're not heads; albeit they are normal forms...)
    HnfNeutral :: abt '[] a -> Hnf rec a -- BUG: how to capture that @abt@ in the type without making things too ugly for the case where @rec ~ Lazy s (abt '[])@ ?


-- | formerly called @forget@, but this seems like a better name
fromHnf :: (ABT abt) => Hnf (abt '[]) a -> abt '[] a
fromHnf (HnfNat  n) = nat_ n
fromHnf (HnfInt  i) = int_ i
fromHnf (HnfProb p) = prob_ p
fromHnf (HnfReal r) = real_ r
fromHnf (HnfDatum d) = datum_ d
fromHnf (HnfNeutral e) = e
fromHnf _ = error "fromHnf: these cases should never be reached"

-- TODO: is that actually Hnf like the paper says? or is it just any term?
type Ans s abt a = Context s abt -> Hnf (L s abt) ('HMeasure a)

data M s abt x = M { unM :: forall a. (x -> Ans s abt a) -> Ans s abt a }

instance Functor (M s abt) where
    fmap f (M m) = M (\c -> m (c . f))

instance Applicative (M s abt) where
    pure a = M (\c -> c a)
    (<*>) = ap -- TODO: can we optimize this?

instance Monad (M s abt) where
    return    = pure
    M m >>= k = M (\c -> m (\a -> unM (k a) c))

data L s abt a = L
    { forward  :: M s abt (Hnf (L s abt) a)
    , backward :: Hnf (L s abt) a -> M s abt ()
    }

type Lazy s abt a = L s (C abt) a

data C abt a = C { unC :: Fin n -> [Vec (Some abt) n -> a] }


disintegrate
    :: (ABT abt, SingI a, SingI b) -- Backward a a
    => abt '[] ('HMeasure (HPair a b))
    -> abt '[] (a ':-> 'HMeasure b) -- this Hakaru function is measurable
disintegrate m =
    lam $ \a ->
    fromHnf $ unM (perform m) (\ab ->
      unM (constrainValue (fst ab) a) (\h' ->
        residuate h' `bind_` dirac (snd ab)))
      emptyContext

-- TODO: should that actually be Hnf or are neutral terms also allowed?
perform  :: abt '[] ('HMeasure a) -> M s abt (Hnf (abt '[]) a)
perform u | atomic u    = M $ \c h -> u `bind` \z -> c z h
perform Lebesgue        = M $ \c h -> Lebesgue `bind` \z -> c z h
perform (Uniform lo hi) = M $ \c h -> Uniform lo hi `bind` \z -> c z h
perform (Dirac e)       = evaluate e
perform (Bind g e)      = M $ \c h -> unM (perform e) c (h `snoc` g) -- TODO: move the bound variable from @e@ into the binding of @g@ we push on the heap
perform (Superpose es)  = Superpose Haskell.<$> T.traverse perform es
perform e | not (hnf e) = M $ \c h -> unM (evaluate e) (\m -> unM (perform m) c) h

-- TODO: should that actually be Hnf or are neutral terms also allowed?
evaluate :: abt '[] a -> M s abt (Hnf (abt '[]) a)
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

-- TODO: do we really need to allow all Hnf, or do we just need
-- variables (or neutral terms)? Do we actually want (hnf)terms at
-- all, or do we want (hnf)patterns or something to more generally
-- capture (hnf)measurable events?
constrainOutcome :: abt '[] ('HMeasure a) -> Hnf (abt '[]) a -> M s abt ()
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
constrainValue :: abt '[] a -> Hnf (abt '[]) a -> M s abt ()
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

unleft :: Hnf abt (HEither a b) -> M s abt (abt '[] a)
unleft (Left  e) = M $ \c h -> c e h
unleft (Right e) = M $ \c h -> reject
unleft u         = M $ \c h -> uneither u (\x -> c x h) (\_ -> reject)

unright :: Hnf abt (HEither a b) -> M s abt (abt '[] a)
unright (Right e) = M $ \c h -> c e h
unright (Left  e) = M $ \c h -> reject
unright u         = M $ \c h -> uneither u (\_ -> reject) (\x -> c x h)
-}

----------------------------------------------------------------
----------------------------------------------------------- fin.
