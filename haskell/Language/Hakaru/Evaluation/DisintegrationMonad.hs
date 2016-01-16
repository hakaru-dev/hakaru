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
           , ScopedTypeVariables
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.01.15
-- |
-- Module      :  Language.Hakaru.Evaluation.DisintegrationMonad
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- The 'EvaluationMonad' for "Language.Hakaru.Disintegrate"
----------------------------------------------------------------
module Language.Hakaru.Evaluation.DisintegrationMonad
    (
    -- * The disintegration monad
    -- ** List-based version
      ListContext(..), Ans, Dis(..), runDis
    -- ** TODO: IntMap-based version
    
    -- * Operators on the disintegration monad
    -- ** The \"zero\" and \"one\"
    , bot
    , reject
    -- ** Emitting code
    , emit
    , emitMBind
    , emitLet
    , emitLet'
    , emitUnpair
    -- TODO: emitUneither
    , emit_
    , emitMBind_
    , emitObserve
    , emitWeight
    , emitFork_
    , emitSuperpose
    , choose
    -- ** Case analysis stuff
    , GBranch(..)
    , fromGBranch
    , toGBranch
    , emitCase
    , freshenBranch
    , freshenGBranch
    , freshenBranchG
    , applyBranch
    ) where

import           Prelude              hiding (id, (.))
import           Control.Category     (Category(..))
#if __GLASGOW_HASKELL__ < 710
import           Data.Monoid          (Monoid(..))
import           Data.Functor         ((<$>))
import           Control.Applicative  (Applicative(..))
#endif
import qualified Data.Foldable        as F
import qualified Data.Traversable     as T
import           Control.Applicative  (Alternative(..))
import           Control.Monad        (MonadPlus(..))
import           Data.Functor.Compose (Compose(..))
import           Data.Text            (Text)
import qualified Data.Text            as Text

import Language.Hakaru.Syntax.IClasses
import Data.Number.Nat
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing    (Sing, sUnMeasure, sUnPair)
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.TypeOf
import Language.Hakaru.Syntax.ABT
import qualified Language.Hakaru.Syntax.Prelude as P
import Language.Hakaru.Evaluation.Types
import Language.Hakaru.Evaluation.Lazy (reifyPair)

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


lazyIsVariable :: (ABT Term abt) => Lazy abt a -> Bool
lazyIsVariable e =
    case e of
    Whnf_ (Head_   _)  -> False
    Whnf_ (Neutral e') -> isVariable e'
    Thunk e'           -> isVariable e'
    where
    isVariable :: (ABT Term abt) => abt '[] a -> Bool
    isVariable e' = caseVarSyn e' (const True) (const False)

lazyIsLiteral :: (ABT Term abt) => Lazy abt a -> Bool
lazyIsLiteral e =
    case e of
    Whnf_ (Head_ (WLiteral _)) -> True
    Whnf_ _                    -> False -- by construction
    Thunk e' ->
        caseVarSyn e' (const False) $ \t ->
            case t of
            Literal_ _ -> True
            _          -> False

-- Argument order is to avoid flipping in 'runDis'
-- TODO: generalize to non-measure types too!
residualizeListContext
    :: forall abt a
    .  (ABT Term abt)
    => abt '[] ('HMeasure a)
    -> ListContext abt
    -> abt '[] ('HMeasure a)
residualizeListContext e0 = foldl step e0 . statements
    where
    step :: abt '[] ('HMeasure a) -> Statement abt -> abt '[] ('HMeasure a)
    step e s =
        case s of
        SBind x body -> syn (MBind :$ fromLazy body :* bind x e :* End)
        SLet  x body
            | not (x `memberVarSet` freeVars e) -> e
            -- TODO: if used exactly once in @e@, then inline.
            | lazyIsVariable body -> subst x (fromLazy body) e
            | lazyIsLiteral  body -> subst x (fromLazy body) e
            | otherwise ->
                syn (Let_ :$ fromLazy body :* bind x e :* End)
        {-
        SBranch xs pat body ->
            syn $ Case_ (fromLazy body)
                [ Branch pat   (binds_ xs e)
                , Branch PWild P.reject
                ]
        -}
        SWeight body -> syn $ Superpose_ [(fromLazy body, e)]
        SIndex x index size ->
            -- The obvious thing to do:
            syn (ArrayOp_ (Index $ typeOf e)
                :$ syn (Array_ (fromLazy size) (bind x e))
                :* fromLazy index
                :* End)
            -- An alternative thing, making it clearer that we've evaluated:
            {-
            syn (Let_
                :$ fromLazy index
                :* bind x
                    (P.if_
                        (P.nat_ 0 P.<= var x P.&& var x P.< fromLazy size)
                        e
                        P.reject)
                :* End)
            -}

----------------------------------------------------------------
-- In the paper we say that result must be a 'Whnf'; however, in
-- the paper it's also always @HMeasure a@ and everything of that
-- type is a WHNF (via 'WMeasure') so that's a trivial statement
-- to make. If we turn it back into some sort of normal form, then
-- it must be one preserved by 'residualizeContext'.
--
-- Also, we add the list in order to support "lub" without it living in the AST.
-- TODO: really we should use ListT or the like...
type Ans abt a = ListContext abt -> [abt '[] ('HMeasure a)]


----------------------------------------------------------------
-- TODO: defunctionalize the continuation. In particular, the only
-- heap modifications we need are 'push' and a variant of 'update'
-- for finding\/replacing a binding once we have the value in hand;
-- and the only 'freshNat' modifications are to allocate new 'Nat'.
-- We could defunctionalize the second arrow too by relying on the
-- @Codensity (ReaderT e m) ~= StateT e (Codensity m)@ isomorphism,
-- which makes explicit that the only thing other than 'ListContext'
-- updates is emitting something like @[Statement]@ to serve as the
-- beginning of the final result.
--
-- TODO: give this a better, more informative name!
--
-- N.B., This monad is used not only for both 'perform' and 'constrainOutcome', but also for 'constrainValue'.
newtype Dis abt x = Dis { unDis :: forall a. (x -> Ans abt a) -> Ans abt a }
    -- == @Codensity (Ans abt)@, assuming 'Codensity' is poly-kinded like it should be
    -- If we don't want to allow continuations that can make nondeterministic choices, then we should use the right Kan extension itself, rather than the Codensity specialization of it.


-- | Run a computation in the 'Dis' monad, residualizing out all the
-- statements in the final evaluation context. The second argument
-- should include all the terms altered by the 'Dis' expression; this
-- is necessary to ensure proper hygiene; for example(s):
--
-- > runDis (perform e) [Some2 e]
-- > runDis (constrainOutcome e v) [Some2 e, Some2 v]
--
-- We use 'Some2' on the inputs because it doesn't matter what their
-- type or locally-bound variables are, so we want to allow @f@ to
-- contain terms with different indices.
runDis :: (ABT Term abt, F.Foldable f)
    => Dis abt (abt '[] a)
    -> f (Some2 abt)
    -> [abt '[] ('HMeasure a)]
runDis (Dis m) es = m c0 (ListContext i0 [])
    where
    -- TODO: we only use dirac because 'residualizeListContext' requires it to already be a measure; unfortunately this can result in an extraneous @(>>= \x -> dirac x)@ redex at the end of the program. In principle, we should be able to eliminate that redex by changing the type of 'residualizeListContext'...
    c0 e = (:[]) . residualizeListContext (syn(Dirac :$ e :* End))
    
    i0 = unMaxNat (F.foldMap (\(Some2 e) -> MaxNat $ nextFree e) es)


instance Functor (Dis abt) where
    fmap f (Dis m)  = Dis $ \c -> m (c . f)

instance Applicative (Dis abt) where
    pure x            = Dis $ \c -> c x
    Dis mf <*> Dis mx = Dis $ \c -> mf $ \f -> mx $ \x -> c (f x)

instance Monad (Dis abt) where
    return      = pure
    Dis m >>= k = Dis $ \c -> m $ \x -> unDis (k x) c

instance Alternative (Dis abt) where
    empty           = Dis $ \_ _ -> []
    Dis m <|> Dis n = Dis $ \c h -> m c h ++ n c h
    
instance MonadPlus (Dis abt) where
    mzero = empty -- aka "bot"
    mplus = (<|>) -- aka "lub"

instance (ABT Term abt) => EvaluationMonad abt (Dis abt) where
    freshNat =
        Dis $ \c (ListContext i ss) ->
            c i (ListContext (i+1) ss)

    unsafePush s =
        Dis $ \c (ListContext i ss) ->
            c () (ListContext i (s:ss))

    -- N.B., the use of 'reverse' is necessary so that the order
    -- of pushing matches that of 'pushes'
    unsafePushes ss =
        Dis $ \c (ListContext i ss') ->
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

-- | Not exported because we only need it for defining 'select' on 'Dis'.
unsafePop :: Dis abt (Maybe (Statement abt))
unsafePop =
    Dis $ \c h@(ListContext i ss) ->
        case ss of
        []    -> c Nothing  h
        s:ss' -> c (Just s) (ListContext i ss')

----------------------------------------------------------------
----------------------------------------------------------------

-- | It is impossible to satisfy the constraints, or at least we
-- give up on trying to do so. This function is identical to 'empty'
-- and 'mzero' for 'Dis'; we just give it its own name since this is
-- the name used in our papers.
bot :: (ABT Term abt) => Dis abt a
bot = Dis $ \_ _ -> []


-- | The empty measure is a solution to the constraints.
reject :: (ABT Term abt) => Dis abt a
reject = Dis $ \_ _ -> [syn (Superpose_ [])]


-- Something essentially like this function was called @insert_@
-- in the finally-tagless code.
--
-- | Emit some code that binds a variable, and return the variable
-- thus bound. The function says what to wrap the result of the
-- continuation with; i.e., what we're actually emitting.
emit
    :: (ABT Term abt)
    => Text
    -> Sing a
    -> (forall r. abt '[a] ('HMeasure r) -> abt '[] ('HMeasure r))
    -> Dis abt (Variable a)
emit hint typ f = do
    x <- freshVar hint typ
    Dis $ \c h -> (f . bind x) <$> c x h


-- This function was called @lift@ in the finally-tagless code.
-- | Emit an 'MBind' (i.e., \"@m >>= \x ->@\") and return the
-- variable thus bound (i.e., @x@).
emitMBind :: (ABT Term abt) => abt '[] ('HMeasure a) -> Dis abt (Variable a)
emitMBind m =
    emit Text.empty (sUnMeasure $ typeOf m) $ \e ->
        syn (MBind :$ m :* e :* End)


-- | A smart constructor for emitting let-bindings. If the input
-- is already a variable then we just return it; otherwise we emit
-- the let-binding. N.B., this function provides the invariant that
-- the result is in fact a variable; whereas 'emitLet'' does not.
emitLet :: (ABT Term abt) => abt '[] a -> Dis abt (Variable a)
emitLet e =
    caseVarSyn e return $ \_ ->
        emit Text.empty (typeOf e) $ \m ->
            syn (Let_ :$ e :* m :* End)

-- | A smart constructor for emitting let-bindings. If the input
-- is already a variable or a literal constant, then we just return
-- it; otherwise we emit the let-binding. N.B., this function
-- provides weaker guarantees on the type of the result; if you
-- require the result to always be a variable, then see 'emitLet'
-- instead.
emitLet' :: (ABT Term abt) => abt '[] a -> Dis abt (abt '[] a)
emitLet' e =
    caseVarSyn e (const $ return e) $ \t ->
        case t of
        Literal_ _ -> return e
        _          -> do
            x <- emit Text.empty (typeOf e) $ \m ->
                syn (Let_ :$ e :* m :* End)
            return (var x)

-- | A smart constructor for emitting \"unpair\". If the input
-- argument is actually a constructor then we project out the two
-- components; otherwise we emit the case-binding and return the
-- two variables.
emitUnpair
    :: (ABT Term abt)
    => Whnf abt (HPair a b)
    -> Dis abt (abt '[] a, abt '[] b)
emitUnpair (Head_   e) = return $ reifyPair e
emitUnpair (Neutral e) = do
    let (a,b) = sUnPair (typeOf e)
    x <- freshVar Text.empty a
    y <- freshVar Text.empty b
    Dis $ \c h ->
        ( syn
        . Case_ e
        . (:[])
        . Branch (pPair PVar PVar)
        . bind x
        . bind y
        ) <$> c (var x, var y) h

-- TODO: emitUneither


-- This function was called @insert_@ in the old finally-tagless code.
-- | Emit some code that doesn't bind any variables. This function
-- provides an optimisation over using 'emit' and then discarding
-- the generated variable.
emit_
    :: (ABT Term abt)
    => (forall r. abt '[] ('HMeasure r) -> abt '[] ('HMeasure r))
    -> Dis abt ()
emit_ f = Dis $ \c h -> f <$> c () h


-- | Emit an 'MBind' that discards its result (i.e., \"@m >>@\").
-- We restrict the type of the argument to be 'HUnit' so as to avoid
-- accidentally dropping things.
emitMBind_ :: (ABT Term abt) => abt '[] ('HMeasure HUnit) -> Dis abt ()
emitMBind_ m = emit_ (m P.>>)


-- TODO: if the argument is a value, then we can evaluate the 'P.if_' immediately rather than emitting it.
-- | Emit an assertion that the condition is true.
emitObserve :: (ABT Term abt) => abt '[] HBool -> Dis abt ()
emitObserve b = emit_ (P.observe b) -- == emit_ $ \m -> P.if_ b m P.reject

-- TODO: if the argument is the literal 1, then we can avoid emitting anything.
emitWeight :: (ABT Term abt) => abt '[] 'HProb -> Dis abt ()
emitWeight w = emit_ (P.pose w)


-- N.B., this use of 'T.traverse' is definitely correct. It's
-- sequentializing @t [abt '[] ('HMeasure a)]@ into @[t (abt '[]
-- ('HMeasure a))]@ by chosing one of the possibilities at each
-- position in @t@. No heap\/context effects can escape to mess
-- things up. In contrast, using 'T.traverse' to sequentialize @t
-- (Dis abt a)@ as @Dis abt (t a)@ is /wrong/! Doing that would give
-- the conjunctive semantics where we have effects from one position
-- in @t@ escape to affect the other positions. This has to do with
-- the general issue in partial evaluation where we need to duplicate
-- downstream work (as we do by passing the same heap to everyone)
-- because there's no general way to combing the resulting heaps
-- for each branch.
--
-- | Run each of the elements of the traversable using the same
-- heap and continuation for each one, then pass the results to a
-- function for emitting code.
emitFork_
    :: (ABT Term abt, T.Traversable t)
    => (forall r. t (abt '[] ('HMeasure r)) -> abt '[] ('HMeasure r))
    -> t (Dis abt a)
    -> Dis abt a
emitFork_ f ms = Dis $ \c h -> f <$> T.traverse (\m -> unDis m c h) ms


-- | Emit a 'Superpose_' of the alternatives, each with unit weight.
emitSuperpose
    :: (ABT Term abt)
    => [abt '[] ('HMeasure a)]
    -> Dis abt (Variable a)
emitSuperpose [e] = emitMBind e
emitSuperpose es  = emitMBind (P.superpose [(P.prob_ 1, e) | e <- es])


-- | Emit a 'Superpose_' of the alternatives, each with unit weight.
choose :: (ABT Term abt) => [Dis abt a] -> Dis abt a
choose [m] = m
choose ms  = emitFork_ (\es -> P.superpose [(P.prob_ 1, e) | e <- es]) ms


-- TODO: move this to Datum.hs; also, use it elsewhere as needed to clean up code.
-- | A generalization of the 'Branch' type to allow a \"body\" of
-- any Haskell type.
data GBranch (a :: Hakaru) (r :: *)
    = forall xs. GBranch
        !(Pattern xs a)
        !(List1 Variable xs)
        r

fromGBranch
    :: (ABT Term abt)
    => GBranch a (abt '[] b)
    -> Branch a abt b
fromGBranch (GBranch pat vars e) =
    Branch pat (binds_ vars e)

toGBranch
    :: (ABT Term abt)
    => Branch a abt b
    -> GBranch a (abt '[] b)
toGBranch (Branch pat body) =
    uncurry (GBranch pat) (caseBinds body)

instance Functor (GBranch a) where
    fmap f (GBranch pat vars x) = GBranch pat vars (f x)

instance F.Foldable (GBranch a) where
    foldMap f (GBranch _ _ x) = f x

instance T.Traversable (GBranch a) where
    traverse f (GBranch pat vars x) = GBranch pat vars <$> f x

-- N.B., this function does not freshen the variables bound by each
-- 'GBranch'. It's the caller's responsability to perform that
-- freshening when turning each original @Branch a abt b@ into
-- @GBranch a (Dis abt x)@. This organization is necessary since we
-- need to have already done the renaming when we turn the underlying
-- @abt xs b@ into @(List1 Variable xs, Dis abt x)@.
--
-- TODO: we want a variant of this function which returns the list
-- of bound variables along with the @b@; since that's required for
-- the continuation to do things that might vary depending on the
-- bound variables.
emitCase
    :: (ABT Term abt)
    => abt '[] a
    -> [GBranch a (Dis abt b)]
    -> Dis abt b
emitCase e =
    emitFork_ (syn . Case_ e . fmap fromGBranch . getCompose) . Compose
{-
-- Alternative implementation which I believe has the same semantics:
emitCase e ms =
    Dis $ \c h -> (syn . Case_ e) <$> T.traverse (runBranch c h) ms
    where
    -- This function has a type isomorphic to:
    -- > GBranch a (Dis abt b) -> Ran (Ans abt) (Ans' abt) b
    -- where:
    -- > Ans' abt b = ListContext abt -> [Branch a abt ('HMeasure b)]
    -- This is very similar to but not quite the same as:
    -- > GBranch a (Dis abt b) -> Dis abt b
    -- Since @Dis abt = Codensity (Ans abt) = Ran (Ans abt) (Ans abt)@.
    runBranch c h = fmap fromGBranch . T.traverse (\m -> unDis m c h)
-}

freshenBranch
    :: (ABT Term abt, EvaluationMonad abt m)
    => Branch a abt b
    -> m (Branch a abt b)
freshenBranch (Branch pat e) = do
    let (vars, body) = caseBinds e
    vars' <- freshenVars vars
    let rho = toAssocs vars (fmap11 var vars')
    return . Branch pat . binds_ vars' $ substs rho body

freshenGBranch
    :: (ABT Term abt, EvaluationMonad abt m)
    => GBranch a b
    -> m (GBranch a b)
freshenGBranch (GBranch pat vars x) = do
    vars' <- freshenVars vars
    return $ GBranch pat vars' x

-- We should have that:
-- > fmap fromGBranch . freshenBranchG = freshenBranch
-- > freshenBranchG . fromGBranch = freshenGBranch
freshenBranchG
    :: (ABT Term abt, EvaluationMonad abt m)
    => Branch a abt b
    -> m (GBranch a (abt '[] b))
freshenBranchG (Branch pat e) = do
    let (vars, body) = caseBinds e
    vars' <- freshenVars vars
    let rho = toAssocs vars (fmap11 var vars')
    return . GBranch pat vars' $ substs rho body


-- | This function will freshen the variables bound by the branch,
-- and then map the function over the body. This only really does
-- what you want provided the function can safely (and does) treat
-- the case-bound variables as if they were free variables.
--
-- We should have that:
-- > T.sequence <=< applyBranch return = freshenBranchG
-- or more generally that:
-- > T.sequence <=< applyBranch f = f <=< freshenBranchG
applyBranch
    :: (ABT Term abt, EvaluationMonad abt m)
    => (abt '[] b -> r)
    -> Branch a abt b
    -> m (GBranch a r)
applyBranch f (Branch pat e) = do
    let (vars, body) = caseBinds e
    vars' <- freshenVars vars
    let rho = toAssocs vars (fmap11 var vars')
    return . GBranch pat vars' . f $ substs rho body

{-
-- This typechecks! It gives an example of how we might use the
-- above in order to do evaluation of the branches under case. Of
-- course, the control flow is a bit strange; the 'Whnf' returned
-- is the result of evaluating the body of whichever branch you
-- happen to be in. We should prolly also return some sort of
-- information about what branch it happens to be, since folks may
-- wish to make decisions based on that. (N.B., using 'emitCase'
-- directly gives you that information via the lexical context since
-- we's give the bodies inline within the 'GBranch'es.)
foo :: (ABT Term abt)
    => abt '[] a
    -> [Branch a abt b]
    -> Dis abt (Whnf abt b)
foo e bs =
    emitCase e =<< T.traverse (applyBranch evaluate_) bs

-- This function should be equivalent to 'foo', just moving the
-- call to 'evaluate_' from the argument of 'applyBranch' to the
-- continuation. Assuming that's actually true and works, then we
-- can implement @applyBranch return@ by @fmap toGBranch .
-- freshenBranch@
foo' :: (ABT Term abt)
    => abt '[] a
    -> [Branch a abt b]
    -> Dis abt (Whnf abt b)
foo' e bs = do
    myBody <- emitCase e =<< T.traverse (applyBranch return) bs
    evaluate_ myBody
-}

----------------------------------------------------------------
----------------------------------------------------------- fin.
