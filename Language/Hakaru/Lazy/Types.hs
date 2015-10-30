{-# LANGUAGE CPP
           , GADTs
           , KindSignatures
           , DataKinds
           , TypeOperators
           , RankNTypes
           , BangPatterns
           , FlexibleContexts
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.29
-- |
-- Module      :  Language.Hakaru.Lazy.Types
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- The data types for "Language.Hakaru.Lazy"
----------------------------------------------------------------
module Language.Hakaru.Lazy.Types
    (
    -- * Terms in particular known forms\/formats
      Head(..), fromHead
    , Whnf(..), fromWhnf
    , Lazy(..), fromLazy, caseLazy

    -- * Evaluation contexts
    , Statement(..)
    , Context(..), initContext, residualizeContext
    
    -- * The monad(s) for term-to-term translations
    , Ans
    , M(..), push, pushes, pop, push_, naivePush, naivePushes
    , M'(..), m2mprime, runM', push', pushes', pop'
    ) where

#if __GLASGOW_HASKELL__ < 710
import           Data.Monoid          (Monoid(..))
import           Data.Functor         ((<$>))
import           Control.Applicative  (Applicative(..))
#endif
import qualified Data.Foldable        as F

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.Nat
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.ABT
import qualified Language.Hakaru.Syntax.Prelude as P

----------------------------------------------------------------
----------------------------------------------------------------
-- N.B., when putting things into the context, be sure to freshen the variables as if we were allocating a new location on the heap.

-- For simplicity we don't actually distinguish between "variables" and "locations". In the old finally-tagless code we had an @s@ parameter like the 'ST' monad does in order to keep track of which heap things belong to. But since we might have nested disintegration, and thus nested heaps, doing that means we'd have to do some sort of De Bruijn numbering in the @s@ parameter in order to keep track of the nested regions; and that's just too much work to bother with.


-- TODO: is there a way to integrate this into the actual 'AST' definition in order to reduce repetition?
-- HACK: can't use \"H\" as the prefix because that clashes with the Hakaru datakind
-- | A \"weak-head\" for the sake of 'Whnf'.
data Head :: ([Hakaru] -> Hakaru -> *) -> Hakaru -> * where
    WValue :: !(Value a) -> Head abt a

    WDatum
        :: {-# UNPACK #-} !(Datum (abt '[]) (HData' t))
        -> Head abt (HData' t)

    WEmpty :: Head abt ('HArray a)

    WArray
        :: !(abt '[] 'HNat)
        -> !(abt '[ 'HNat ] a)
        -> Head abt ('HArray a)

    WLam
        :: !(abt '[ a ] b)
        -> Head abt (a ':-> b)

    -- TODO: should probably be separated out, since this doesn't really fit with our usual notion of head-normal forms...
    -- TODO: the old version just recursed as type @a@. What's up with that?
    WMeasure :: !(abt '[] ('HMeasure a)) -> Head abt ('HMeasure a)


-- | Forget that something is a head.
fromHead :: (ABT AST abt) => Head abt a -> abt '[] a
fromHead (WValue   v)     = syn (Value_ v)
fromHead (WDatum   d)     = syn (Datum_ d)
fromHead WEmpty           = syn Empty_
fromHead (WArray   e1 e2) = syn (Array_ e1 e2)
fromHead (WLam     e1)    = syn (Lam_ :$ e1 :* End)
fromHead (WMeasure e1)    = e1


----------------------------------------------------------------
-- BUG: haddock doesn't like annotations on GADT constructors. So
-- here we'll avoid using the GADT syntax, even though it'd make
-- the data type declaration prettier\/cleaner.
-- <https://github.com/hakaru-dev/hakaru/issues/6>

-- | Weak head-normal forms.
data Whnf (abt :: [Hakaru] -> Hakaru -> *) (a :: Hakaru)
    -- | An actual (weak-)head.
    = Head_ !(Head abt a)

    -- TODO: would it be helpful to track which variable it's blocked on? To do so we'd need 'GotStuck' to return that info...
    -- | A neutral term; i.e., a term whose reduction is blocked
    -- on some free variable.
    | Neutral !(abt '[] a)


-- | Forget that something is in WHNF.
fromWhnf :: (ABT AST abt) => Whnf abt a -> abt '[] a
fromWhnf (Head_   e) = fromHead e
fromWhnf (Neutral e) = e


----------------------------------------------------------------
-- BUG: haddock doesn't like annotations on GADT constructors. So
-- here we'll avoid using the GADT syntax, even though it'd make
-- the data type declaration prettier\/cleaner.
-- <https://github.com/hakaru-dev/hakaru/issues/6>

-- | Lazy terms are either thunks or already evaluated to WHNF.
data Lazy (abt :: [Hakaru] -> Hakaru -> *) (a :: Hakaru)
    -- | Already evaluated to WHNF.
    = Whnf_ !(Whnf abt a)

    -- | A thunk; i.e., any term, which we may decide to evaluate
    -- later (or may not).
    | Thunk !(abt '[] a)


-- | Forget that something is Lazy.
fromLazy :: (ABT AST abt) => Lazy abt a -> abt '[] a
fromLazy (Whnf_ e) = fromWhnf e
fromLazy (Thunk e) = e

caseLazy :: Lazy abt a -> (Whnf abt a -> r) -> (abt '[] a -> r) -> r
caseLazy (Whnf_ e) k _ = k e
caseLazy (Thunk e) _ k = k e


----------------------------------------------------------------
-- BUG: haddock doesn't like annotations on GADT constructors. So
-- here we'll avoid using the GADT syntax, even though it'd make
-- the data type declaration prettier\/cleaner.
-- <https://github.com/hakaru-dev/hakaru/issues/6>

-- | A single statement in the @HMeasure@ monad, where bound variables
-- are considered part of the \"statement\" that binds them rather
-- than part of the continuation. Thus, non-binding statements like
-- @Weight@ are also included here.
--
-- This type was formerly called @Binding@, but that is inaccurate
-- since it also includes non-binding statements.
data Statement (abt :: [Hakaru] -> Hakaru -> *)
    -- | A variable bound by 'MBind' to a measure expression.
    = forall (a :: Hakaru) . SBind
        {-# UNPACK #-} !(Variable a)
        !(Lazy abt ('HMeasure a))

    -- | A variable bound by 'Let_' to an expression.
    | forall (a :: Hakaru) . SLet
        {-# UNPACK #-} !(Variable a)
        !(Lazy abt a)

    -- TODO: to make a proper zipper for 'AST'\/'ABT' we'd want to
    -- also store the other branches here...
    --
    -- | A collection of variables bound by a 'Pattern' to
    -- subexpressions of the some 'Case_' scrutinee.
    | forall (xs :: [Hakaru]) (a :: Hakaru) . SBranch
        !(List1 Variable xs) -- could use 'SArgs' for more strictness
        !(Pattern xs a)
        !(Lazy abt a)

    -- | A weight; i.e., the first component of each argument to
    -- 'Superpose_'.
    | SWeight
        !(Lazy abt 'HProb)

    -- TODO: if we do proper HNFs then we should add all the other binding forms (Lam_, Array_, Expect,...) as \"statements\" too


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
data Context (abt :: [Hakaru] -> Hakaru -> *) = Context
    { freshNat   :: {-# UNPACK #-} !Nat
    , statements :: [Statement abt]
    }
-- TODO: to the extent that we can ignore order of statements, we could use an @IntMap (Statement abt)@ in order to speed up the lookup times in 'update'. We just need to figure out (a) what to do with 'SWeight' statements, (b) how to handle 'SBranch' so that we can just make one map modification despite possibly binding multiple variables, and (c) figure out how to recover the order (to the extent that we must).


-- | Create an initial context, making sure not to capture any of
-- the free variables in the collection of arguments.
--
-- We use 'Some2' on the inputs because it doesn't matter what their
-- type or locally-bound variables are, so we want to allow @f@ to
-- contain terms with different indices.
initContext :: (ABT AST abt, F.Foldable f) => f (Some2 abt) -> Context abt
initContext es = Context (1 + maximumFree es) []
    where
    maximumFree :: (ABT AST abt, F.Foldable f) => f (Some2 abt) -> Nat
    maximumFree = unMaxNat . F.foldMap (\(Some2 e) -> MaxNat $ maxFree e)
    -- N.B., 'Foldable' doesn't get 'F.null' until ghc-7.10


-- Argument order is to avoid flipping in 'runM'
-- TODO: generalize to non-measure types too!
residualizeContext
    :: (ABT AST abt)
    => Whnf abt ('HMeasure a)
    -> Context abt
    -> abt '[] ('HMeasure a)
residualizeContext = \e h -> foldl step (fromWhnf e) (statements h)
    where
    step e s = syn $
        case s of
        SBind x body -> MBind :$ fromLazy body :* bind x e :* End
        SLet  x body -> Let_  :$ fromLazy body :* bind x e :* End
        SBranch xs pat body ->
            Case_ (fromLazy body)
                [ Branch pat $
                    case eqAppendIdentity xs of
                    Refl -> binds xs e
                , Branch PWild P.reject
                ]
        SWeight body -> Superpose_ [(fromLazy body, e)]


----------------------------------------------------------------
-- TODO: is that actually Whnf like the paper says? or can it be any term?
type Ans abt a = Context abt -> Whnf abt a

-- TODO: defunctionalize the continuation. In particular, the only heap modifications we need are 'push' and a variant of 'update' for finding\/replacing a binding once we have the value in hand.
-- TODO: give this a better, more informative name!
newtype M abt x = M { unM :: forall a. (x -> Ans abt a) -> Ans abt a }

{-
-- TODO: implement 'residualizeContext' at the correct type.
-- TODO: can we legit call the result of 'residualizeContext' a neutral term? Really we should change the definition of 'Ans', ne?
runM :: M abt (Whnf abt a) -> Context abt -> Whnf abt a
runM (M m) = m (\x -> Head_ . ??? . residualizeContext x)
-}

instance Functor (M abt) where
    fmap f (M m)  = M $ \c -> m (c . f)

instance Applicative (M abt) where
    pure x        = M $ \c -> c x
    M mf <*> M mx = M $ \c -> mf $ \f -> mx $ \x -> c (f x)

instance Monad (M abt) where
    return    = pure
    M m >>= k = M $ \c -> m $ \x -> unM (k x) c


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
    :: (ABT AST abt)
    => Statement abt
    -> abt xs a
    -> (abt xs a -> M abt r)
    -> M abt r
push s e k = do
    rho <- push_ s
    k (substs rho e)


-- | Internal function for renaming variables when we push a new
-- statement, without applying that renaming to \"the rest of the
-- term\". You almost certainly should use 'push' or 'pushes'
-- instead.
push_
    :: (ABT AST abt)
    => Statement abt
    -> M abt (Assocs abt)
push_ s = M $ \c (Context i ss) ->
    case s of
    SWeight body -> c mempty (Context i (SWeight body : ss))
    SBind x body ->
        let x'  = x{varID=i}
            rho = singletonAssocs x (var x')
            s'  = SBind x' body
        in c rho (Context (i+1) (s':ss))
    SLet x body ->
        let x'  = x{varID=i}
            rho = singletonAssocs x (var x')
            s'  = SLet x' body
        in c rho (Context (i+1) (s':ss))
    SBranch xs pat body ->
        let (i', xs') = renameFrom xs i
            rho = toAssocs xs $ fmap11 var xs'
            s'  = SBranch xs' pat body
        in c rho (Context i' (s':ss))


renameFrom
    :: List1 Variable (xs :: [Hakaru]) -> Nat -> (Nat, List1 Variable xs)
renameFrom = go
    where
    go Nil1         !i = (i, Nil1)
    go (Cons1 x xs)  i =
        case renameFrom xs (i+1) of
        (i', xs') -> (i', Cons1 (x{varID=i}) xs')


-- | Call 'push' repeatedly. (N.B., is more efficient than actually
-- calling 'push' repeatedly.)
pushes
    :: (ABT AST abt)
    => [Statement abt]
    -> abt xs a
    -> (abt xs a -> M abt r)
    -> M abt r
pushes ss e k = do
    -- TODO: is 'foldlM' the right one? or do we want 'foldrM'?
    rho <- F.foldlM (\rho s -> mappend rho <$> push_ s) mempty ss
    k (substs rho e)


-- | N.B., this can be unsafe. If a binding statement is returned,
-- then the caller must be sure to push back on statements binding
-- all the same variables!
pop :: M abt (Maybe (Statement abt))
pop = M $ \c h ->
    case statements h of
    []   -> c Nothing  h
    s:ss -> c (Just s) h{statements = ss}


-- | Push a statement onto the heap /without renaming variables/.
-- This function should only be used to put a statement from 'pop'
-- back onto the context.
naivePush :: Statement abt -> M abt ()
naivePush s = M $ \c h -> c () h{statements = s : statements h}


-- TODO: replace this function with a @DList@ variant, to avoid the need to 'reverse' @ss@.
-- | Call 'naivePush' repeatedly. (N.B., is more efficient than
-- actually calling 'naivePush' repeatedly.)
naivePushes :: [Statement abt] -> M abt ()
naivePushes ss =
    M $ \c h -> c () h{statements = reverse ss ++ statements h}

----------------------------------------------------------------
----------------------------------------------------------------
-- HACK: how can we cleanly unify this with the implementation of 'M'?
newtype M' abt x =
    M' { unM' :: forall a. (x -> Ans abt ('HMeasure a)) -> Ans abt ('HMeasure a) }

m2mprime :: M abt x -> M' abt x
m2mprime (M m) = M' m

-- TODO: mprime2m


-- TODO: can we legit call the result of 'residualizeContext' a
-- neutral term? Really we should change the definition of 'Ans',
-- ne?
--
-- BUG: the argument type doesn't match up with what 'perform' returns! We hack around that by using 'SingI', for now; but really should clean it all up.
--
-- | Run a computation in the 'M'' monad, residualizing out all the
-- statements in the final 'Context'. The initial context argument
-- should be constructed by 'initContext' to ensure proper hygiene;
-- for example:
--
-- > \e -> runM' (perform e) (initContext [e])
runM' :: (ABT AST abt, SingI a)
    => M' abt (Whnf abt a)
    -> Context abt
    -> Whnf abt ('HMeasure a)
runM' m = unM' m (\x -> Head_ . WMeasure . residualizeContext (lift x))
-- HACK: can't eta-shorten away the @x@; won't typecheck for some reason
    where
    lift :: (ABT AST abt, SingI a) => Whnf abt a -> Whnf abt ('HMeasure a)
    lift (Head_   v) = Head_ . WMeasure $ P.dirac (fromHead v)
    lift (Neutral e) = Neutral $ P.dirac e


instance Functor (M' abt) where
    fmap f (M' m)  = M' $ \c -> m (c . f)

instance Applicative (M' abt) where
    pure x          = M' $ \c -> c x
    M' mf <*> M' mx = M' $ \c -> mf $ \f -> mx $ \x -> c (f x)

instance Monad (M' abt) where
    return     = pure
    M' m >>= k = M' $ \c -> m $ \x -> unM' (k x) c

push'
    :: (ABT AST abt)
    => Statement abt
    -> abt xs a
    -> (abt xs a -> M' abt r)
    -> M' abt r
push' s e k = do
    rho <- m2mprime (push_ s)
    k (substs rho e)

pushes'
    :: (ABT AST abt)
    => [Statement abt]
    -> abt xs a
    -> (abt xs a -> M' abt r)
    -> M' abt r
pushes' ss e k = do
    -- TODO: is 'foldlM' the right one? or do we want 'foldrM'?
    rho <- F.foldlM (\rho s -> mappend rho <$> m2mprime (push_ s)) mempty ss
    k (substs rho e)

pop' :: M' abt (Maybe (Statement abt))
pop' = m2mprime pop

----------------------------------------------------------------
----------------------------------------------------------- fin.
