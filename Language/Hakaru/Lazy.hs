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
           , FunctionalDependencies
           , BangPatterns
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs -fno-warn-unused-binds -fno-warn-unused-imports #-}
----------------------------------------------------------------
--                                                    2015.10.27
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
    -- * Terms in particular known forms\/formats
      Head(..), fromHead
    , Whnf(..), fromWhnf
    , Lazy(..), fromLazy, caseLazy

    -- * The monad for term-to-term translations
    -- TODO: how much of this do we actually need to export?
    , Statement(..)
    , Context(..), initContext
    , Ans
    , M(..), push, pushes, pop
    , M'(..), push', pushes', pop'

    -- * Lazy partial evaluation
    , evaluate
    , perform
    -- ** Helper functions
    ) where

import           Data.Proxy           (Proxy(..))
import           Data.Sequence        (Seq)
import           Data.Number.LogFloat (LogFloat)
#if __GLASGOW_HASKELL__ < 710
import           Data.Monoid          (Monoid(..))
import           Data.Functor         ((<$>))
import           Control.Applicative  (Applicative(..))
#endif
import           Data.IntMap          (IntMap)
import qualified Data.IntMap          as IM
import qualified Data.Foldable        as F
import qualified Data.Traversable     as T

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.Nat
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.DatumCase
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.Coercion
import qualified Language.Hakaru.Syntax.Prelude as P
import qualified Language.Hakaru.Expect         as E
import Language.Hakaru.PrettyPrint -- HACK: for ghci use only

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
fromHead :: (ABT abt) => Head abt a -> abt '[] a
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
fromWhnf :: (ABT abt) => Whnf abt a -> abt '[] a
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

    -- | A thunk; i.e., any term we decide to maybe evaluate later.
    | Thunk !(abt '[] a)


-- | Forget that something is Lazy.
fromLazy :: (ABT abt) => Lazy abt a -> abt '[] a
fromLazy (Whnf_ e) = fromWhnf e
fromLazy (Thunk e) = e

caseLazy :: Lazy abt a -> (Whnf abt a -> r) -> (abt '[] a -> r) -> r
caseLazy (Whnf_ e) k _ = k e
caseLazy (Thunk e) _ k = k e


----------------------------------------------------------------
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
data Statement abt
    -- | A variable bound by 'MBind' to a measure expression.
    = forall a. SBind
        {-# UNPACK #-} !(Variable a)
        !(Lazy abt ('HMeasure a))

    -- | A variable bound by 'Let_' to an expression.
    | forall a. SLet
        {-# UNPACK #-} !(Variable a)
        !(Lazy abt a)

    -- TODO: to make a proper zipper for 'AST'\/'ABT' we'd want to
    -- also store the other branches here...
    --
    -- | A collection of variables bound by a 'Pattern' to
    -- subexpressions of the some 'Case_' scrutinee.
    | forall xs a. SBranch
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
-- TODO: to the extent that we can ignore order of statements, we could use an @IntMap (Statement abt)@ in order to speed up the lookup times in 'update'. We just need to figure out (a) what to do with 'SWeight' statements, (b) how to handle 'SBranch' so that we can just make one map modification despite possibly binding multiple variables, and (c) figure out how to recover the order (to the extent that we must).


-- | Create an initial context, making sure not to capture any of
-- the free variables in the collection of arguments.
--
-- TODO: generalize the argument's type to use @Some2@ (or @Foldable20@)
-- instead, so that the @xs@ and @a@ can vary for each term.
initContext :: (ABT abt, F.Foldable f) => f (abt xs a) -> Context abt
initContext es =
    Context (1 + unMaxNat (F.foldMap (MaxNat . maxFree) es)) []
    -- N.B., 'Foldable' doesn't get 'F.null' until ghc-7.10


-- Argument order is to avoid flipping in 'runM'
-- TODO: generalize to non-measure types too!
residualizeContext
    :: (ABT abt)
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
-- TODO: is that actually Whnf like the paper says? or is it just any term?
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
    :: (ABT abt)
    => Statement abt
    -> abt xs a
    -> (abt xs a -> M abt r)
    -> M abt r
push s e k = do
    rho <- push_ s
    k (substs rho e)


push_
    :: (ABT abt)
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


renameFrom :: List1 Variable xs -> Nat -> (Nat, List1 Variable xs)
renameFrom = go
    where
    go Nil1         !i = (i, Nil1)
    go (Cons1 x xs)  i =
        case renameFrom xs (i+1) of
        (i', xs') -> (i', Cons1 (x{varID=i}) xs')

-- TODO: move this to ABT.hs\/Variable.hs
singletonAssocs :: Variable a -> abt '[] a -> Assocs abt
singletonAssocs x e =
    Assocs $ IM.singleton (fromNat $ varID x) (Assoc x e)

-- TODO: move this to ABT.hs\/Variable.hs
toAssocs :: List1 Variable xs -> List1 (abt '[]) xs -> Assocs abt
toAssocs = \xs es -> Assocs (go xs es)
    where
    go :: List1 Variable xs -> List1 (abt '[]) xs -> IntMap (Assoc abt)
    -- BUG: GHC claims the patterns are non-exhaustive here
    go Nil1         Nil1         = IM.empty
    go (Cons1 x xs) (Cons1 e es) =
        IM.insert (fromNat $ varID x) (Assoc x e) (go xs es)

-- TODO: move this to ABT.hs\/Variable.hs
-- TODO: what is the actual monoid instance for IntMap; left-biased shadowing I assume? We should make it an error if anything's multiply defined.
instance Monoid (Assocs abt) where
    mempty  = Assocs IM.empty
    mappend (Assocs xs) (Assocs ys) = Assocs (mappend xs ys)
    mconcat = Assocs . mconcat . map unAssocs


-- | Call 'push' repeatedly. (N.B., is more efficient than actually
-- calling 'push' repeatedly.)
pushes
    :: (ABT abt)
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
        MeasureOp_ _ :$ _ -> return . Head_ $ WMeasure e0
        MBind        :$ _ -> return . Head_ $ WMeasure e0 -- N.B., not HNF
        Superpose_ _      -> return . Head_ $ WMeasure e0


        -- Everything else needs some evaluation

        App_ :$ e1 :* e2 :* End -> do
            w1 <- evaluate e1
            case w1 of
                Neutral e1'    -> return . Neutral $ P.app e1' e2
                Head_ (WLam f) ->
                    caseBind f $ \x f' ->
                        push (SLet x (Thunk e2)) f' evaluate
                Head_ v1 -> case v1 of {} -- HACK: impossible

        Let_ :$ e1 :* e2 :* End ->
            caseBind e2 $ \x e2' ->
                push (SLet x (Thunk e1)) e2' evaluate

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
runM' :: (ABT abt, SingI a)
    => M' abt (Whnf abt a)
    -> Context abt
    -> Whnf abt ('HMeasure a)
runM' m = unM' m (\x -> Head_ . WMeasure . residualizeContext (lift x))
-- HACK: can't eta-shorten away the @x@; won't typecheck for some reason
    where
    lift :: (ABT abt, SingI a) => Whnf abt a -> Whnf abt ('HMeasure a)
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
    :: (ABT abt)
    => Statement abt
    -> abt xs a
    -> (abt xs a -> M' abt r)
    -> M' abt r
push' s e k = do
    rho <- m2mprime (push_ s)
    k (substs rho e)

pushes'
    :: (ABT abt)
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


-- N.B., that return type is correct, albeit strange. The idea is that the continuation takes in the variable of type @a@ bound by the expression of type @'HMeasure a@. However, this requires that the continuation of the 'Ans' type actually does @forall a. ...('HMeasure a)@ which is at odds with what 'evaluate' wants (or at least, what *I* think it should want.)
-- BUG: eliminate the 'SingI' requirement (comes from using @(P.>>=)@)
perform
    :: (ABT abt, SingI a) => abt '[] ('HMeasure a) -> M' abt (Whnf abt a)
perform e0 =
    caseVarSyn e0 (error "TODO: perform{Var}") $ \t ->
        case t of
        MeasureOp_ (Dirac _) :$ e1 :* End ->
            m2mprime $ evaluate e1
        MeasureOp_ _ :$ _ ->
            M' $ \c h -> Head_ $ WMeasure (e0 P.>>= \z -> fromWhnf (c (Neutral z) h))
        MBind :$ e1 :* e2 :* End ->
            caseBind e2 $ \x e2' ->
                push' (SBind x (Thunk e1)) e2' perform
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
    Nothing                 -> error "tryMatch: nothing matched!"
    Just GotStuck           -> return . Neutral . syn $ Case_ e bs
    Just (Matched ss body') -> pushes (toStatements ss) body' k


type DList a = [a] -> [a]

toStatements
    :: DList (Assoc abt)
    -> [Statement abt]
toStatements = map toStatement . ($ [])

toStatement :: Assoc abt -> Statement abt
toStatement (Assoc x e) = SLet x (Thunk e)


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

-- Essentially, these should all do @f <$> evaluate e1 <*> evaluate e2...@ where @f@ is the interpretation of the 'PrimOp', which residualizes as necessary if it gets stuck.
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
-- TODO: figure out how to abstract this so it can be reused by 'constrainValue'. Especially the 'SBranch case of 'step'
-- BUG: we need (a) a variant of 'update' which doesn't 'perform' if it finds an 'SBind' or else, (b) better ways of converting between 'M' and 'M''.
update :: (ABT abt) => Variable a -> M abt (Whnf abt a)
update x = loop []
    where
    loop ss = do
        ms <- pop
        case ms of
            Nothing -> do
                naivePushes ss
                return (Neutral (var x))
            Just s  ->
                case step s of
                Nothing -> loop (s:ss)
                Just mw -> do
                    w <- mw        -- evaluate the body of @s@
                    naivePush (SLet x (Whnf_ w)) -- push the updated binding
                    naivePushes ss -- put the rest of the context back
                    return w       -- TODO: return (NamedWhnf x v)

    -- BUG: existential escapes; need to cps
    step (SBind y e0) = do
        Refl <- varEq x y
        Just $ error "TODO: update{SBind}" -- caseLazy e0 return perform
    step (SLet y e0) = do
        Refl <- varEq x y
        Just $ caseLazy e0 return evaluate
    step (SBranch ys pat e0) =
        error "TODO: update{SBranch}"
        {-
        Refl <- varEqAny x ys
        Just $ caseLazy e0 return $ \e -> do
            w <- evaluate e
            case w of
                Neutral e' -> M $ \c h ->
                    Neutral . syn $ Case_ e'
                        [ Branch pat   (binds ys (c x h))
                        , Branch PWild P.reject
                        ]
                Head_ v ->
                    case
                        matchBranches (fromHead v)
                            [ Branch pat   (binds ys P.true)
                            , Branch PWild P.false
                            ]
                    of
                    Nothing -> error "TODO: update: match failed"
                    Just GotStuck -> error "TODO: update: got stuck"
                    Just (Matched ss b) ->
                        if reify b
                        then pushes ss x update
                        else P.reject
        -}
    step _ = Nothing


----------------------------------------------------------------
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
----------------------------------------------------------- fin.
