{-# LANGUAGE CPP
           , GADTs
           , KindSignatures
           , DataKinds
           , TypeOperators
           , RankNTypes
           , BangPatterns
           , FlexibleContexts
           , MultiParamTypeClasses
           , FunctionalDependencies
           , FlexibleInstances
           , EmptyCase
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.11.17
-- |
-- Module      :  Language.Hakaru.Lazy.Types
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- The data types for "Language.Hakaru.Lazy"
--
-- BUG: completely gave up on structure sharing. Need to add that back in.
--
-- TODO: once we figure out the exact API\/type of 'evaluate' and
-- can separate it from Disintegrate.hs vs its other clients (i.e.,
-- Sample.hs and Expect.hs), this file will prolly be broken up
-- into Lazy.hs itself vs Disintegrate.hs
----------------------------------------------------------------
module Language.Hakaru.Lazy.Types
    (
    -- * Terms in particular known forms\/formats
      Head(..), fromHead
    , Whnf(..), fromWhnf, caseWhnf, viewWhnfDatum
    , Lazy(..), fromLazy, caseLazy

    -- * The monad for partial evaluation
    , Statement(..), isBoundBy
    , EvaluationMonad(..)
    , freshVar
    , freshenVar
    {- TODO: should we expose these?
    , freshenVars
    , freshenStatement
    , push_
    -}
    , push
    , pushes

    -- * The disintegration monad
    -- ** List-based version
    , ListContext(..), Ans, M(..), runM
    -- ** TODO: IntMap-based version
    ) where

#if __GLASGOW_HASKELL__ < 710
import           Data.Monoid          (Monoid(..))
import           Data.Functor         ((<$>))
import           Control.Applicative  (Applicative(..))
#endif
import qualified Data.Foldable        as F
import           Data.Text            (Text)

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.Nat
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Sing    (Sing)
import Language.Hakaru.Syntax.Coercion
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.TypeOf
import Language.Hakaru.Syntax.ABT

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


-- TODO: is there a way to integrate this into the actual 'AST'
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
    WValue :: !(Value a) -> Head abt a
    WDatum
        :: {-# UNPACK #-} !(Datum (abt '[]) (HData' t))
        -> Head abt (HData' t)
    WEmpty :: Head abt ('HArray a)
    WArray :: !(abt '[] 'HNat) -> !(abt '[ 'HNat] a) -> Head abt ('HArray a)
    WLam   :: !(abt '[ a ] b) -> Head abt (a ':-> b)
    WFix   :: !(abt '[ a ] a) -> Head abt a

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
    -- TODO: we prolly don't actually want\/need the coercion variants... we'd lose some proven-guarantees about cancellation, but everything should work just fine if we update 'Value' to use Integer and Rational rather than Int and Double...
    WAnn        :: !(Sing a)       -> !(Head abt a) -> Head abt a
    WCoerceTo   :: !(Coercion a b) -> !(Head abt a) -> Head abt b
    WUnsafeFrom :: !(Coercion a b) -> !(Head abt b) -> Head abt a

    -- Other funky stuff
    -- TODO: is there any way we can get rid of 'WLub'? cuz dealing with it is gross
    WLub :: [Head abt a] -> Head abt a
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
    NaryOp_ :: !(NaryOp a) -> !(Seq (abt '[] a)) -> AST abt a
    PrimOp_
        :: (typs ~ UnLCs args, args ~ LCs typs)
        => !(PrimOp typs a) -> SCon args a
    -- N.B., not 'ArrayOp_'
    -}


-- | Forget that something is a head.
fromHead :: (ABT AST abt) => Head abt a -> abt '[] a
fromHead (WValue     v)     = syn (Value_ v)
fromHead (WDatum     d)     = syn (Datum_ d)
fromHead WEmpty             = syn Empty_
fromHead (WArray     e1 e2) = syn (Array_ e1 e2)
fromHead (WLam       e1)    = syn (Lam_ :$ e1 :* End)
fromHead (WFix       e1)    = syn (Fix_ :$ e1 :* End)
fromHead (WMeasureOp o  es) = syn (MeasureOp_ o :$ es)
fromHead (WDirac     e1)    = syn (Dirac :$ e1 :* End)
fromHead (WMBind     e1 e2) = syn (MBind :$ e1 :* e2 :* End)
fromHead (WSuperpose pes)   = syn (Superpose_ pes)
fromHead (WAnn      typ e1) = syn (Ann_      typ :$ fromHead e1 :* End)
fromHead (WCoerceTo   c e1) = syn (CoerceTo_   c :$ fromHead e1 :* End)
fromHead (WUnsafeFrom c e1) = syn (UnsafeFrom_ c :$ fromHead e1 :* End)
fromHead (WLub es)          = syn (Lub_ (fromHead <$> es))
fromHead (WIntegrate e1 e2 e3) = syn (Integrate :$ e1 :* e2 :* e3 :* End)
fromHead (WSummate   e1 e2 e3) = syn (Summate   :$ e1 :* e2 :* e3 :* End)


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
fromWhnf :: (ABT AST abt) => Whnf abt a -> abt '[] a
fromWhnf (Head_   e) = fromHead e
fromWhnf (Neutral e) = e

-- | Case analysis on 'Whnf' as a combinator.
caseWhnf :: Whnf abt a -> (Head abt a -> r) -> (abt '[] a -> r) -> r
caseWhnf (Head_   e) k _ = k e
caseWhnf (Neutral e) _ k = k e


-- | Given some WHNF, try to extract a 'Datum' from it.
viewWhnfDatum
    :: (ABT AST abt)
    => Whnf abt (HData' t)
    -> Maybe (Datum (abt '[]) (HData' t))
viewWhnfDatum (Head_   v) = viewHeadDatum v
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
        Value_ (VDatum d) -> error "bad \"neutral\" value!"
        Datum_         d  -> error "bad \"neutral\" value!"
        _                 -> Nothing
    -}

viewHeadDatum
    :: (ABT AST abt)
    => Head abt (HData' t)
    -> Maybe (Datum (abt '[]) (HData' t))
viewHeadDatum (WAnn        _ w)   = viewHeadDatum w
viewHeadDatum (WCoerceTo   c _)   = case c of {}
viewHeadDatum (WUnsafeFrom c _)   = case c of {}
viewHeadDatum (WValue (VDatum d)) = Just (fmap11 (syn . Value_) d)
viewHeadDatum (WDatum d)          = Just d
viewHeadDatum (WFix e)            = error "TODO: viewHeadDatum{WFix}" -- probably should be Nothing, if we disallow infinite data values
viewHeadDatum (WLub [])           = Nothing
viewHeadDatum (WLub es)           = error "TODO: viewHeadDatum{WLub}"


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
fromLazy :: (ABT AST abt) => Lazy abt a -> abt '[] a
fromLazy (Whnf_ e) = fromWhnf e
fromLazy (Thunk e) = e

-- | Case analysis on 'Lazy' as a combinator.
caseLazy :: Lazy abt a -> (Whnf abt a -> r) -> (abt '[] a -> r) -> r
caseLazy (Whnf_ e) k _ = k e
caseLazy (Thunk e) _ k = k e


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
class (Functor m, Applicative m, Monad m, ABT AST abt)
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
    :: (ABT AST abt, EvaluationMonad abt m)
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


-- | Given some hint and type, generate a variable with a fresh
-- 'varID'.
freshVar
    :: (EvaluationMonad abt m)
    => Text
    -> Sing (a :: Hakaru)
    -> m (Variable a)
freshVar hint typ = do
    i <- freshNat
    return $ Variable hint i typ


-- | Given a variable, return a new variable with the same hint and
-- type but with a fresh 'varID'.
freshenVar
    :: (EvaluationMonad abt m)
    => Variable (x :: Hakaru)
    -> m (Variable x)
freshenVar x = do
    i <- freshNat
    return x{varID=i}


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
    :: (ABT AST abt, EvaluationMonad abt m)
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
    :: (ABT AST abt, EvaluationMonad abt m)
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
    :: (ABT AST abt, EvaluationMonad abt m)
    => [Statement abt]   -- ^ the statements to push
    -> abt xs a          -- ^ the \"rest\" of the term
    -> (abt xs a -> m r) -- ^ what to do with the renamed \"rest\"
    -> m r               -- ^ the final result
pushes ss e k = do
    -- TODO: is 'foldlM' the right one? or do we want 'foldrM'?
    rho <- F.foldlM (\rho s -> mappend rho <$> push_ s) mempty ss
    k (substs rho e)


----------------------------------------------------------------
----------------------------------------------------------------
-- | An ordered collection of statements representing the context
-- surrounding the current focus of our program transformation.
-- That is, since some transformations work from the bottom up, we
-- need to keep track of the statements we passed along the way
-- when reaching for the bottom.
--
-- The tail of the list takes scope over the head of the list. Thus,
-- the back\/end of the list is towards the top of the program,
-- whereas the front of the list is towards the bottom.
--
-- This type was formerly called @Heap@ (presumably due to the
-- 'Statement' type being called @Binding@) but that seems like a
-- misnomer to me since this really has nothing to do with allocation.
-- However, it is still like a heap inasmuch as it's a dependency
-- graph and we may wish to change the topological sorting or remove
-- \"garbage\" (subject to correctness criteria).
--
-- TODO: Figure out what to do with 'SWeight' so that we can use
-- an @IntMap (Statement abt)@ in order to speed up the lookup times
-- in 'select'. (Assuming callers don't use 'unsafePush' unsafely:
-- we can recover the order things were inserted from their 'varID'
-- since we've freshened them all and therefore their IDs are
-- monotonic in the insertion order.)
data ListContext (abt :: [Hakaru] -> Hakaru -> *) = ListContext
    { nextFreshNat :: {-# UNPACK #-} !Nat
    , statements   :: [Statement abt]
    }


-- Argument order is to avoid flipping in 'runM'
-- TODO: generalize to non-measure types too!
-- TODO: if any SLet bindings are unused, then drop them. If any are used exactly once, maybe inline them?
residualizeListContext
    :: (ABT AST abt)
    => abt '[] ('HMeasure a)
    -> ListContext abt
    -> abt '[] ('HMeasure a)
residualizeListContext e0 = foldl step e0 . statements
    where
    step e s = syn $
        case s of
        SBind x body -> MBind :$ fromLazy body :* bind x e :* End
        SLet  x body -> Let_  :$ fromLazy body :* bind x e :* End
        {-
        SBranch xs pat body ->
            Case_ (fromLazy body)
                [ Branch pat $
                    case eqAppendIdentity xs of
                    Refl -> binds xs e
                , Branch PWild P.reject
                ]
        -}
        SWeight body -> Superpose_ [(fromLazy body, e)]
        SIndex x index size ->
            -- The obvious thing to do:
            ArrayOp_ (Index $ typeOf e)
                :$ syn (Array_ (fromLazy size) (bind x e))
                :* fromLazy index
                :* End
            -- An alternative thing, making it clearer that we've evaluated:
            {-
            Let_
                :$ fromLazy index
                :* bind x
                    (P.if_
                        (P.nat_ 0 P.<= var x P.&& var x P.< fromLazy size)
                        e
                        P.reject)
                :* End
            -}

-- In the paper we say that result must be a 'Whnf'; however, in
-- the paper it's also always @HMeasure a@ and everything of that
-- type is a WHNF (via 'WMeasure') so that's a trivial statement
-- to make. If we turn it back into some sort of normal form, then
-- it must be one preserved by 'residualizeContext'.
type Ans abt a = ListContext abt -> abt '[] ('HMeasure a)


-- TODO: defunctionalize the continuation. In particular, the only
-- heap modifications we need are 'push' and a variant of 'update'
-- for finding\/replacing a binding once we have the value in hand.
--
-- TODO: give this a better, more informative name!
--
-- N.B., This monad is used not only for both 'perform' and 'constrainOutcome', but also for 'constrainValue'.
newtype M abt x = M { unM :: forall a. (x -> Ans abt a) -> Ans abt a }


-- | Run a computation in the 'M' monad, residualizing out all the
-- statements in the final evaluation context. The second argument
-- should include all the terms altered by the 'M' expression; this
-- is necessary to ensure proper hygiene; for example(s):
--
-- > runM (perform e) [Some2 e]
-- > runM (constrainOutcome e v) [Some2 e, Some2 v]
--
-- We use 'Some2' on the inputs because it doesn't matter what their
-- type or locally-bound variables are, so we want to allow @f@ to
-- contain terms with different indices.
runM :: (ABT AST abt, F.Foldable f)
    => M abt (Whnf abt a)
    -> f (Some2 abt)
    -> abt '[] ('HMeasure a)
runM (M m) es = m c0 (ListContext i0 [])
    where
    -- HACK: we only have @c0@ build up a WHNF since that's what
    -- 'Ans' says we need (see the comment at 'Ans' for why this
    -- may not be what we actually mean).
    c0 x = residualizeListContext $ syn (Dirac :$ fromWhnf x :* End)
    
    i0 = unMaxNat (F.foldMap (\(Some2 e) -> MaxNat $ nextFree e) es)


instance Functor (M abt) where
    fmap f (M m)  = M $ \c -> m (c . f)

instance Applicative (M abt) where
    pure x        = M $ \c -> c x
    M mf <*> M mx = M $ \c -> mf $ \f -> mx $ \x -> c (f x)

instance Monad (M abt) where
    return    = pure
    M m >>= k = M $ \c -> m $ \x -> unM (k x) c

instance (ABT AST abt) => EvaluationMonad abt (M abt) where
    freshNat =
        M $ \c (ListContext i ss) ->
            c i (ListContext (i+1) ss)

    unsafePush s =
        M $ \c (ListContext i ss) ->
            c () (ListContext i (s:ss))

    -- N.B., the use of 'reverse' is necessary so that the order
    -- of pushing matches that of 'pushes'
    unsafePushes ss =
        M $ \c (ListContext i ss') ->
            c () (ListContext i (reverse ss ++ ss'))

    select x p = loop []
        where
        -- TODO: use a DList to avoid reversing inside 'unsafePushes'
        loop ss = do
            ms <- unsafePop
            case ms of
                Nothing -> do
                    unsafePushes ss
                    return Nothing
                Just s  ->
                    -- Alas, @p@ will have to recheck 'isBoundBy'
                    -- in order to grab the 'Refl' proof we erased;
                    -- but there's nothing to be done for it.
                    case x `isBoundBy` s >> p s of
                    Nothing -> loop (s:ss)
                    Just mr -> do
                        r <- mr
                        unsafePushes ss
                        return (Just r)

-- | Not exported because we only need it for defining 'select' on 'M'.
unsafePop :: M abt (Maybe (Statement abt))
unsafePop =
    M $ \c h@(ListContext i ss) ->
        case ss of
        []    -> c Nothing  h
        s:ss' -> c (Just s) (ListContext i ss')

----------------------------------------------------------------
----------------------------------------------------------- fin.
