{-# LANGUAGE CPP
           , GADTs
           , KindSignatures
           , DataKinds
           , TypeOperators
           , Rank2Types
           , BangPatterns
           , FlexibleContexts
           , MultiParamTypeClasses
           , FunctionalDependencies
           , FlexibleInstances
           , UndecidableInstances
           , EmptyCase
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.01.08
-- |
-- Module      :  Language.Hakaru.Evaluation.Types
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- The data types for "Language.Hakaru.Evaluation.Lazy"
--
-- BUG: completely gave up on structure sharing. Need to add that back in.
--
-- TODO: once we figure out the exact API\/type of 'evaluate' and
-- can separate it from Disintegrate.hs vs its other clients (i.e.,
-- Sample.hs and Expect.hs), this file will prolly be broken up
-- into Lazy.hs itself vs Disintegrate.hs
----------------------------------------------------------------
module Language.Hakaru.Evaluation.Types
    (
    -- * Terms in particular known forms\/formats
      Head(..), fromHead, toHead, viewHeadDatum
    , Whnf(..), fromWhnf, toWhnf, caseWhnf, viewWhnfDatum
    , Lazy(..), fromLazy, caseLazy

    -- * The monad for partial evaluation
    , Statement(..), isBoundBy
    , EvaluationMonad(..)
    , freshVar
    , freshenVar
    , Hint(..), freshVars
    , freshenVars
    {- TODO: should we expose these?
    , freshenStatement
    , push_
    -}
    , push
    , pushes
    ) where

import           Prelude              hiding (id, (.))
import           Control.Category     (Category(..))
#if __GLASGOW_HASKELL__ < 710
import           Data.Monoid          (Monoid(..))
import           Data.Functor         ((<$>))
import           Control.Applicative  (Applicative(..))
#endif
import           Control.Arrow        ((***))
import qualified Data.Foldable        as F
import           Data.Text            (Text)

import Language.Hakaru.Syntax.IClasses
import Data.Number.Nat
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing    (Sing)
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
-- import Language.Hakaru.Syntax.TypeOf
import Language.Hakaru.Syntax.ABT
import qualified Language.Hakaru.Syntax.Prelude as P

----------------------------------------------------------------
----------------------------------------------------------------
-- N.B., when putting things into the context, be sure to freshen
-- the variables as if we were allocating a new location on the
-- heap.
--
-- For simplicity we don't actually distinguish between "variables"
-- and "locations". In the old finally-tagless code we had an @s@
-- parameter like the 'ST' monad does in order to keep track of
-- which heap things belong to. But since we might have nested
-- disintegration, and thus nested heaps, doing that means we'd
-- have to do some sort of De Bruijn numbering in the @s@ parameter
-- in order to keep track of the nested regions; and that's just
-- too much work to bother with.


-- TODO: for forward disintegration (which is not just partial evaluation) we really do mean proper HNFs not just WHNFs. This falls out from our needing to guarantee that heap-bound variables can't possibly escape; whence the assumption that the result of forward disintegration contains no heap-bound variables.
--
-- TODO: is there a way to integrate this into the actual 'Term'
-- definition in order to reduce repetition?
--
-- HACK: can't use \"H\" as the prefix because that clashes with
-- the Hakaru datakind
--
-- | A \"weak-head\" for the sake of 'Whnf'. N.B., this doesn't
-- exactly correlate with the usual notion of \"weak-head\"; in
-- particular we keep track of type annotations and coercions, and
-- don't reduce integration\/summation. So really we should use
-- some other name for 'Whnf'...
--
-- BUG: this may not force enough evaluation for "Language.Hakaru.Disintegrate"...
data Head :: ([Hakaru] -> Hakaru -> *) -> Hakaru -> * where
    -- Simple heads (aka, the usual stuff)
    WLiteral :: !(Literal a) -> Head abt a
    -- BUG: even though the 'Datum' type has a single constructor, we get a warning about not being able to UNPACK it in 'WDatum'... wtf?
    WDatum :: !(Datum (abt '[]) (HData' t)) -> Head abt (HData' t)
    WEmpty :: !(Sing ('HArray a)) -> Head abt ('HArray a)
    WArray :: !(abt '[] 'HNat) -> !(abt '[ 'HNat] a) -> Head abt ('HArray a)
    WLam   :: !(abt '[ a ] b) -> Head abt (a ':-> b)

    -- Measure heads (not just anything of 'HMeasure' type)
    WMeasureOp
        :: (typs ~ UnLCs args, args ~ LCs typs)
        => !(MeasureOp typs a)
        -> !(SArgs abt args)
        -> Head abt ('HMeasure a)
    WDirac :: !(abt '[] a) -> Head abt ('HMeasure a)
    WMBind
        :: !(abt '[] ('HMeasure a))
        -> !(abt '[ a ] ('HMeasure b))
        -> Head abt ('HMeasure b)
    WSuperpose
        :: [(abt '[] 'HProb, abt '[] ('HMeasure a))]
        -> Head abt ('HMeasure a)

    -- Type annotation\/coercion stuff. These are transparent re head-ness; that is, they behave more like HNF than WHNF.
    -- TODO: we prolly don't actually want\/need the coercion variants... we'd lose some proven-guarantees about cancellation, but everything should work just fine. The one issue that remains is if we have coercion of 'WIntegrate' or 'WSummate', since without the 'WCoerceTo'\/'WUnsafeFrom' constructors we'd be forced to call the coercion of an integration \"neutral\"--- even though it's not actually a neutral term!
    WAnn        :: !(Sing a)       -> !(Head abt a) -> Head abt a
    WCoerceTo   :: !(Coercion a b) -> !(Head abt a) -> Head abt b
    WUnsafeFrom :: !(Coercion a b) -> !(Head abt b) -> Head abt a

    -- Other funky stuff
    WIntegrate
        :: !(abt '[] 'HReal)
        -> !(abt '[] 'HReal)
        -> !(abt '[ 'HReal ] 'HProb)
        -> Head abt 'HProb
    WSummate
        :: !(abt '[] 'HReal)
        -> !(abt '[] 'HReal)
        -> !(abt '[ 'HInt ] 'HProb)
        -> Head abt 'HProb

    -- Quasi-/semi-/demi-/pseudo- normal form stuff
    {-
    NaryOp_ :: !(NaryOp a) -> !(Seq (abt '[] a)) -> Term abt a
    PrimOp_
        :: (typs ~ UnLCs args, args ~ LCs typs)
        => !(PrimOp typs a) -> SCon args a
    -- N.B., not 'ArrayOp_'
    -}


-- | Forget that something is a head.
fromHead :: (ABT Term abt) => Head abt a -> abt '[] a
fromHead (WLiteral    v)        = syn (Literal_ v)
fromHead (WDatum      d)        = syn (Datum_ d)
fromHead (WEmpty      typ)      = syn (Empty_ typ)
fromHead (WArray      e1 e2)    = syn (Array_ e1 e2)
fromHead (WLam        e1)       = syn (Lam_ :$ e1 :* End)
fromHead (WMeasureOp  o  es)    = syn (MeasureOp_ o :$ es)
fromHead (WDirac      e1)       = syn (Dirac :$ e1 :* End)
fromHead (WMBind      e1 e2)    = syn (MBind :$ e1 :* e2 :* End)
fromHead (WSuperpose  pes)      = syn (Superpose_ pes)
fromHead (WAnn        typ e1)   = syn (Ann_      typ :$ fromHead e1 :* End)
fromHead (WCoerceTo   c e1)     = syn (CoerceTo_   c :$ fromHead e1 :* End)
fromHead (WUnsafeFrom c e1)     = syn (UnsafeFrom_ c :$ fromHead e1 :* End)
fromHead (WIntegrate  e1 e2 e3) = syn (Integrate :$ e1 :* e2 :* e3 :* End)
fromHead (WSummate    e1 e2 e3) = syn (Summate   :$ e1 :* e2 :* e3 :* End)


-- | Identify terms which are already heads.
toHead :: (ABT Term abt) => abt '[] a -> Maybe (Head abt a)
toHead e =
    caseVarSyn e (const Nothing) $ \t ->
        case t of
        Literal_     v                      -> Just $ WLiteral   v
        Datum_       d                      -> Just $ WDatum     d
        Empty_       typ                    -> Just $ WEmpty     typ
        Array_       e1     e2              -> Just $ WArray     e1 e2
        Lam_      :$ e1  :* End             -> Just $ WLam       e1
        MeasureOp_   o   :$ es              -> Just $ WMeasureOp o  es
        Dirac     :$ e1  :* End             -> Just $ WDirac     e1
        MBind     :$ e1  :* e2 :* End       -> Just $ WMBind     e1 e2
        Superpose_   pes                    -> Just $ WSuperpose pes
        Ann_         typ :$ e1 :* End       -> WAnn      typ <$> toHead e1
        CoerceTo_    c   :$ e1 :* End       -> WCoerceTo   c <$> toHead e1
        UnsafeFrom_  c   :$ e1 :* End       -> WUnsafeFrom c <$> toHead e1
        Integrate :$ e1  :* e2 :* e3 :* End -> Just $ WIntegrate e1 e2 e3
        Summate   :$ e1  :* e2 :* e3 :* End -> Just $ WSummate   e1 e2 e3
        _ -> Nothing

instance Functor21 Head where
    fmap21 _ (WLiteral    v)        = WLiteral v
    fmap21 f (WDatum      d)        = WDatum (fmap11 f d)
    fmap21 _ (WEmpty      typ)      = WEmpty typ
    fmap21 f (WArray      e1 e2)    = WArray (f e1) (f e2)
    fmap21 f (WLam        e1)       = WLam (f e1)
    fmap21 f (WMeasureOp  o  es)    = WMeasureOp o (fmap21 f es)
    fmap21 f (WDirac      e1)       = WDirac (f e1)
    fmap21 f (WMBind      e1 e2)    = WMBind (f e1) (f e2)
    fmap21 f (WSuperpose  pes)      = WSuperpose (map (f *** f) pes)
    fmap21 f (WAnn        typ e1)   = WAnn      typ (fmap21 f e1)
    fmap21 f (WCoerceTo   c e1)     = WCoerceTo   c (fmap21 f e1)
    fmap21 f (WUnsafeFrom c e1)     = WUnsafeFrom c (fmap21 f e1)
    fmap21 f (WIntegrate  e1 e2 e3) = WIntegrate (f e1) (f e2) (f e3)
    fmap21 f (WSummate    e1 e2 e3) = WSummate   (f e1) (f e2) (f e3)

instance Foldable21 Head where
    foldMap21 _ (WLiteral    _)        = mempty
    foldMap21 f (WDatum      d)        = foldMap11 f d
    foldMap21 _ (WEmpty      _)        = mempty
    foldMap21 f (WArray      e1 e2)    = f e1 `mappend` f e2
    foldMap21 f (WLam        e1)       = f e1
    foldMap21 f (WMeasureOp  _  es)    = foldMap21 f es
    foldMap21 f (WDirac      e1)       = f e1
    foldMap21 f (WMBind      e1 e2)    = f e1 `mappend` f e2
    foldMap21 f (WSuperpose  pes)      = foldMapPairs f pes
    foldMap21 f (WAnn        _ e1)     = foldMap21 f e1
    foldMap21 f (WCoerceTo   _ e1)     = foldMap21 f e1
    foldMap21 f (WUnsafeFrom _ e1)     = foldMap21 f e1
    foldMap21 f (WIntegrate  e1 e2 e3) = f e1 `mappend` f e2 `mappend` f e3
    foldMap21 f (WSummate    e1 e2 e3) = f e1 `mappend` f e2 `mappend` f e3

instance Traversable21 Head where
    traverse21 _ (WLiteral    v)        = pure $ WLiteral v
    traverse21 f (WDatum      d)        = WDatum <$> traverse11 f d
    traverse21 _ (WEmpty      typ)      = pure $ WEmpty typ
    traverse21 f (WArray      e1 e2)    = WArray <$> f e1 <*> f e2
    traverse21 f (WLam        e1)       = WLam <$> f e1
    traverse21 f (WMeasureOp  o  es)    = WMeasureOp o <$> traverse21 f es
    traverse21 f (WDirac      e1)       = WDirac <$> f e1
    traverse21 f (WMBind      e1 e2)    = WMBind <$> f e1 <*> f e2
    traverse21 f (WSuperpose  pes)      = WSuperpose <$> traversePairs f pes
    traverse21 f (WAnn        typ e1)   = WAnn      typ <$> traverse21 f e1
    traverse21 f (WCoerceTo   c e1)     = WCoerceTo   c <$> traverse21 f e1
    traverse21 f (WUnsafeFrom c e1)     = WUnsafeFrom c <$> traverse21 f e1
    traverse21 f (WIntegrate  e1 e2 e3) = WIntegrate <$> f e1 <*> f e2 <*> f e3
    traverse21 f (WSummate    e1 e2 e3) = WSummate   <$> f e1 <*> f e2 <*> f e3


----------------------------------------------------------------
-- BUG: haddock doesn't like annotations on GADT constructors. So
-- here we'll avoid using the GADT syntax, even though it'd make
-- the data type declaration prettier\/cleaner.
-- <https://github.com/hakaru-dev/hakaru/issues/6>

-- | Weak head-normal forms are either heads or neutral terms (i.e.,
-- a term whose reduction is blocked on some free variable).
data Whnf (abt :: [Hakaru] -> Hakaru -> *) (a :: Hakaru)
    = Head_   !(Head abt a)
    | Neutral !(abt '[] a)
    -- TODO: would it be helpful to track which variable it's blocked
    -- on? To do so we'd need 'GotStuck' to return that info...

-- | Forget that something is a WHNF.
fromWhnf :: (ABT Term abt) => Whnf abt a -> abt '[] a
fromWhnf (Head_   e) = fromHead e
fromWhnf (Neutral e) = e


-- | Identify terms which are already heads. N.B., we make no attempt
-- to identify neutral terms, we just massage the type of 'toHead'.
toWhnf :: (ABT Term abt) => abt '[] a -> Maybe (Whnf abt a)
toWhnf e = Head_ <$> toHead e

-- | Case analysis on 'Whnf' as a combinator.
caseWhnf :: Whnf abt a -> (Head abt a -> r) -> (abt '[] a -> r) -> r
caseWhnf (Head_   e) k _ = k e
caseWhnf (Neutral e) _ k = k e


instance Functor21 Whnf where
    fmap21 f (Head_   v) = Head_ (fmap21 f v)
    fmap21 f (Neutral e) = Neutral (f e)

instance Foldable21 Whnf where
    foldMap21 f (Head_   v) = foldMap21 f v
    foldMap21 f (Neutral e) = f e

instance Traversable21 Whnf where
    traverse21 f (Head_   v) = Head_ <$> traverse21 f v
    traverse21 f (Neutral e) = Neutral <$> f e


-- | Given some WHNF, try to extract a 'Datum' from it.
viewWhnfDatum
    :: (ABT Term abt)
    => Whnf abt (HData' t)
    -> Maybe (Datum (abt '[]) (HData' t))
viewWhnfDatum (Head_   v) = Just $ viewHeadDatum v
viewWhnfDatum (Neutral _) = Nothing
    -- N.B., we always return Nothing for 'Neutral' terms because of
    -- what 'Neutral' is supposed to mean. If we wanted to be paranoid
    -- then we could use the following code to throw an error if
    -- we're given a \"neutral\" term which is in fact a head
    -- (because that indicates an error in our logic of constructing
    -- 'Neutral' values):
    {-
    caseVarSyn e (const Nothing) $ \t ->
        case t of
        Datum_ d -> error "bad \"neutral\" value!"
        _        -> Nothing
    -}

viewHeadDatum
    :: (ABT Term abt)
    => Head abt (HData' t)
    -> Datum (abt '[]) (HData' t)
viewHeadDatum (WAnn        _ w) = viewHeadDatum w
viewHeadDatum (WCoerceTo   c _) = case c of {}
viewHeadDatum (WUnsafeFrom c _) = case c of {}
viewHeadDatum (WDatum      d)   = d
viewHeadDatum (WLiteral    v)   = case v of {}


-- Alas, to avoid the orphanage, this instance must live here rather than in Lazy.hs where it more conceptually belongs.
-- TODO: better unify the two cases of Whnf
-- HACK: this instance requires -XUndecidableInstances
instance (ABT Term abt) => Coerce (Whnf abt) where
    coerceTo c w =
        case w of
        Neutral e ->
            Neutral . maybe (P.coerceTo_ c e) id
                $ caseVarSyn e (const Nothing) $ \t ->
                    case t of
                    Literal_ x          -> Just $ P.literal_ (coerceTo c x)
                    -- UnsafeFrom_ c' :$ es' -> TODO: cancellation
                    CoerceTo_ c' :$ es' ->
                        case es' of
                        e' :* End -> Just $ P.coerceTo_ (c . c') e'
                        _ -> error "coerceTo@Whnf: the impossible happened"
                    _ -> Nothing
        Head_ v ->
            case v of
            WLiteral x      -> Head_ $ WLiteral (coerceTo c x)
            -- WUnsafeFrom c' v' -> TODO: cancellation
            WCoerceTo c' v' -> Head_ $ WCoerceTo (c . c') v'
            _               -> Head_ $ WCoerceTo c v
    
    coerceFrom c w =
        case w of
        Neutral e ->
            Neutral . maybe (P.unsafeFrom_ c e) id
                $ caseVarSyn e (const Nothing) $ \t ->
                    case t of
                    Literal_ x -> Just $ P.literal_ (coerceFrom c x)
                    -- CoerceTo_ c' :$ es' -> TODO: cancellation
                    UnsafeFrom_ c' :$ es' ->
                        case es' of
                        e' :* End -> Just $ P.unsafeFrom_ (c' . c) e'
                        _ -> error "unsafeFrom@Whnf: the impossible happened"
                    _ -> Nothing
        Head_ v ->
            case v of
            WLiteral x        -> Head_ $ WLiteral (coerceFrom c x)
            -- WCoerceTo c' v' -> TODO: cancellation
            WUnsafeFrom c' v' -> Head_ $ WUnsafeFrom (c' . c) v'
            _                 -> Head_ $ WUnsafeFrom c v


----------------------------------------------------------------
-- BUG: haddock doesn't like annotations on GADT constructors. So
-- here we'll avoid using the GADT syntax, even though it'd make
-- the data type declaration prettier\/cleaner.
-- <https://github.com/hakaru-dev/hakaru/issues/6>

-- | Lazy terms are either thunks (i.e., any term, which we may
-- decide to evaluate later) or are already evaluated to WHNF.
data Lazy (abt :: [Hakaru] -> Hakaru -> *) (a :: Hakaru)
    = Whnf_ !(Whnf abt a)
    | Thunk !(abt '[] a)

-- | Forget whether a term has been evaluated to WHNF or not.
fromLazy :: (ABT Term abt) => Lazy abt a -> abt '[] a
fromLazy (Whnf_ e) = fromWhnf e
fromLazy (Thunk e) = e

-- | Case analysis on 'Lazy' as a combinator.
caseLazy :: Lazy abt a -> (Whnf abt a -> r) -> (abt '[] a -> r) -> r
caseLazy (Whnf_ e) k _ = k e
caseLazy (Thunk e) _ k = k e

instance Functor21 Lazy where
    fmap21 f (Whnf_ v) = Whnf_ (fmap21 f v)
    fmap21 f (Thunk e) = Thunk (f e)

instance Foldable21 Lazy where
    foldMap21 f (Whnf_ v) = foldMap21 f v
    foldMap21 f (Thunk e) = f e

instance Traversable21 Lazy where
    traverse21 f (Whnf_ v) = Whnf_ <$> traverse21 f v
    traverse21 f (Thunk e) = Thunk <$> f e

----------------------------------------------------------------
-- BUG: haddock doesn't like annotations on GADT constructors. So
-- here we'll avoid using the GADT syntax, even though it'd make
-- the data type declaration prettier\/cleaner.
-- <https://github.com/hakaru-dev/hakaru/issues/6>

-- | A single statement in the 'HMeasure' monad. In particular,
-- note that the the first argument to 'MBind' (or 'Let_') together
-- with the variable bound in the second argument forms the
-- \"statement\" (leaving out the body of the second argument, which
-- may be part of a following statement). In addition to these
-- binding constructs, we also include a few non-binding statements
-- like 'SWeight'.
--
-- This type was formerly called @Binding@, but that is inaccurate
-- since it also includes non-binding statements.
--
-- TODO: figure out a way to distinguish the pure statements (namely
-- 'SLet') from the statements which can only live in 'HMeasure';
-- so that we can run the partial evaluator on pure code and extract
-- an answer without needing to explain what to do with 'HMeasure'
-- stuff...
data Statement (abt :: [Hakaru] -> Hakaru -> *)
    -- | A variable bound by 'MBind' to a measure expression.
    = forall (a :: Hakaru) . SBind
        {-# UNPACK #-} !(Variable a)
        !(Lazy abt ('HMeasure a))

    -- | A variable bound by 'Let_' to an expression.
    | forall (a :: Hakaru) . SLet
        {-# UNPACK #-} !(Variable a)
        !(Lazy abt a)

    -- | A variable bound by 'Array_' underneath 'Index'. The first
    -- expression gives the index at which we are evaluating the
    -- array (i.e., the second argument to 'Index'); the second
    -- index gives the size of the array (i.e., the first argument
    -- to 'Array_'). If it turns out that the index expression is
    -- out of bounds, then evaluation should throw an error.
    --
    -- TODO: should we 'bot' rather than throwing an error?
    | SIndex
        {-# UNPACK #-} !(Variable 'HNat)
        !(Lazy abt 'HNat)
        !(Lazy abt 'HNat)

    -- | A weight; i.e., the first component of each argument to
    -- 'Superpose_'.
    | SWeight
        !(Lazy abt 'HProb)


-- | Is the variable bound by the statement?
isBoundBy :: Variable (a :: Hakaru) -> Statement abt -> Maybe ()
x `isBoundBy` SBind  y _   = const () <$> varEq x y
x `isBoundBy` SLet   y _   = const () <$> varEq x y
x `isBoundBy` SIndex y _ _ = const () <$> varEq x y
_ `isBoundBy` SWeight  _   = Nothing


----------------------------------------------------------------
-- | This class captures the monadic operations needed by the
-- 'evaluate' function in "Language.Hakaru.Lazy".
class (Functor m, Applicative m, Monad m, ABT Term abt)
    => EvaluationMonad abt m | m -> abt
    where
    -- TODO: should we have a *method* for arbitrarily incrementing the stored 'nextFreshNat'; or should we only rely on it being initialized correctly? Beware correctness issues about updating the lower bound after having called 'freshNat'...

    -- | Return a fresh natural number. That is, a number which is
    -- not the 'varID' of any free variable in the expressions of
    -- interest, and isn't a number we've returned previously.
    freshNat :: m Nat

    -- | Add a statement to the top of the context. This is unsafe
    -- because it may allow confusion between variables with the
    -- same name but different scopes (thus, may allow variable
    -- capture). Prefer using 'push_', 'push', or 'pushes'.
    unsafePush :: Statement abt -> m ()

    -- | Call 'unsafePush' repeatedly. Is part of the class since
    -- we may be able to do this more efficiently than actually
    -- calling 'unsafePush' repeatedly.
    --
    -- N.B., this should push things in the same order as 'pushes'
    -- does.
    unsafePushes :: [Statement abt] -> m ()
    unsafePushes = mapM_ unsafePush

    -- | Look for the statement @s@ binding the variable. If found,
    -- then call the continuation with @s@ in the context where @s@
    -- itself and everything @s@ (transitively)depends on is included
    -- but everything that (transitively)depends on @s@ is excluded;
    -- thus, the continuation may only alter the dependencies of
    -- @s@. After the continuation returns, restore all the bindings
    -- that were removed before calling the continuation. If no
    -- such @s@ can be found, then return 'Nothing' without altering
    -- the context at all.
    --
    -- N.B., the statement @s@ itself is popped! Thus, it is up to
    -- the continuation to make sure to push new statements that
    -- bind all the variables bound by @s@!
    select
        :: Variable (a :: Hakaru)
        -> (Statement abt -> Maybe (m r))
        -> m (Maybe r)


-- | Internal function for renaming the variables bound by a
-- statement. We return the renamed statement along with a substitution
-- for mapping the old variable names to their new variable names.
freshenStatement
    :: (ABT Term abt, EvaluationMonad abt m)
    => Statement abt
    -> m (Statement abt, Assocs abt)
freshenStatement s =
    case s of
    SWeight _    -> return (s, mempty)
    SBind x body -> do
        x' <- freshenVar x
        return (SBind x' body, singletonAssocs x (var x'))
    SLet x body -> do
        x' <- freshenVar x
        return (SLet x' body, singletonAssocs x (var x'))
    {-
    SBranch xs pat body -> do
        xs' <- freshenVars xs
        return (SBranch xs' pat body, toAssocs xs (fmap11 var xs'))
    -}
    SIndex x index size -> do
        x' <- freshenVar x
        return (SIndex x' index size, singletonAssocs x (var x'))


-- TODO: define a new NameSupply monad in "Language.Hakaru.Syntax.Variable" for encapsulating these four fresh(en) functions?


-- | Given some hint and type, generate a variable with a fresh
-- 'varID'.
freshVar
    :: (EvaluationMonad abt m)
    => Text
    -> Sing (a :: Hakaru)
    -> m (Variable a)
freshVar hint typ = (\i -> Variable hint i typ) <$> freshNat


-- TODO: move to "Language.Hakaru.Syntax.Variable" in case anyone else wants it too.
data Hint (a :: Hakaru) = Hint {-# UNPACK #-} !Text !(Sing a)

-- | Call 'freshVar' repeatedly.
-- TODO: make this more efficient than actually calling 'freshVar'
-- repeatedly.
freshVars
    :: (EvaluationMonad abt m)
    => List1 Hint xs
    -> m (List1 Variable xs)
freshVars Nil1         = return Nil1
freshVars (Cons1 x xs) = Cons1 <$> freshVar' x <*> freshVars xs
    where
    freshVar' (Hint hint typ) = freshVar hint typ


-- | Given a variable, return a new variable with the same hint and
-- type but with a fresh 'varID'.
freshenVar
    :: (EvaluationMonad abt m)
    => Variable (a :: Hakaru)
    -> m (Variable a)
freshenVar x = (\i -> x{varID=i}) <$> freshNat


-- | Call 'freshenVar' repeatedly.
-- TODO: make this more efficient than actually calling 'freshenVar'
-- repeatedly.
freshenVars
    :: (EvaluationMonad abt m)
    => List1 Variable (xs :: [Hakaru])
    -> m (List1 Variable xs)
freshenVars Nil1         = return Nil1
freshenVars (Cons1 x xs) = Cons1 <$> freshenVar x <*> freshenVars xs
{-
-- TODO: get this faster version to typecheck! And once we do, move it to IClasses.hs or wherever 'List1'\/'DList1' end up
freshenVars = go dnil1
    where
    go  :: (EvaluationMonad abt m)
        => DList1 Variable (ys :: [Hakaru])
        -> List1  Variable (zs :: [Hakaru])
        -> m (List1 Variable (ys ++ zs))
    go k Nil1         = return (unDList1 k Nil1) -- for typechecking, don't use 'toList1' here.
    go k (Cons1 x xs) = do
        x' <- freshenVar x
        go (k `dsnoc1` x') xs -- BUG: type error....
-}


-- | Add a statement to the top of the context, renaming any variables
-- the statement binds and returning the substitution mapping the
-- old variables to the new ones. This is safer than 'unsafePush'
-- because it avoids variable confusion; but it is still somewhat
-- unsafe since you may forget to apply the substitution to \"the
-- rest of the term\". You almost certainly should use 'push' or
-- 'pushes' instead.
push_
    :: (ABT Term abt, EvaluationMonad abt m)
    => Statement abt
    -> m (Assocs abt)
push_ s = do
    (s',rho) <- freshenStatement s
    unsafePush s'
    return rho


-- | Push a statement onto the context, renaming variables along
-- the way. The second argument represents \"the rest of the term\"
-- after we've peeled the statement off; it's passed so that we can
-- update the variable names there so that they match with the
-- (renamed)binding statement. The third argument is the continuation
-- for what to do with the renamed term. Rather than taking the
-- second and third arguments we could return an 'Assocs' giving
-- the renaming of variables; however, doing that would make it too
-- easy to accidentally drop the substitution on the floor rather
-- than applying it to the term before calling the continuation.
push
    :: (ABT Term abt, EvaluationMonad abt m)
    => Statement abt     -- ^ the statement to push
    -> abt xs a          -- ^ the \"rest\" of the term
    -> (abt xs a -> m r) -- ^ what to do with the renamed \"rest\"
    -> m r               -- ^ the final result
push s e k = do
    rho <- push_ s
    k (substs rho e)


-- | Call 'push' repeatedly. (N.B., is more efficient than actually
-- calling 'push' repeatedly.) The head is pushed first and thus
-- is the furthest away in the final context, whereas the tail is
-- pushed last and is the closest in the final context.
pushes
    :: (ABT Term abt, EvaluationMonad abt m)
    => [Statement abt]   -- ^ the statements to push
    -> abt xs a          -- ^ the \"rest\" of the term
    -> (abt xs a -> m r) -- ^ what to do with the renamed \"rest\"
    -> m r               -- ^ the final result
pushes ss e k = do
    -- TODO: is 'foldlM' the right one? or do we want 'foldrM'?
    rho <- F.foldlM (\rho s -> mappend rho <$> push_ s) mempty ss
    k (substs rho e)

{-
-- The old finally-tagless code also had the equivalents of these functions (called @memo@ in that code). Would they be helpful for us?

pushLet
    :: (ABT Term abt, EvaluationMonad abt m)
    => Lazy abt a     -- ^ the expression to push
    -> m (Variable a) -- ^ the variable the expression is bound to
pushLet e = do
    x <- freshVar Text.empty (typeOf e)
    unsafePush (SLet x e)
    return x

pushBind
    :: (ABT Term abt, EvaluationMonad abt m)
    => Lazy abt ('HMeasure a) -- ^ the expression to push
    -> m (Variable a)         -- ^ the variable the expression is bound to
pushBind e = do
    x <- freshVar Text.empty (sUnMeasure $ typeOf e)
    unsafePush (SBind x e)
    return x
-}

----------------------------------------------------------------
----------------------------------------------------------- fin.
