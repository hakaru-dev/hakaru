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
           , FlexibleContexts
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs -fno-warn-unused-binds -fno-warn-unused-imports #-}
----------------------------------------------------------------
--                                                    2015.12.08
-- |
-- Module      :  Language.Hakaru.Disintegrate
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Disintegration via lazy partial evaluation.
--
-- N.B., the forward direction of disintegration is /not/ just
-- partial evaluation! In the version discussed in the paper we
-- must also ensure that no heap-bound variables occur in the result,
-- which requires using HNFs rather than WHNFs. That condition is
-- sound, but a bit too strict; we could generalize this to handle
-- cases where there may be heap-bound variables remaining in neutral
-- terms, provided we (a) don't end up trying to go both forward
-- and backward on the same variable, and (more importantly) (b)
-- end up with the proper Jacobian. The paper version is rigged to
-- ensure that whenever we recurse into two subexpressions (e.g.,
-- the arguments to addition) one of them has a Jacobian of zero,
-- thus when going from @x*y@ to @dx*y + x*dy@ one of the terms
-- cancels out.
----------------------------------------------------------------
module Language.Hakaru.Disintegrate
    (
    -- * the Hakaru API
      disintegrate
    , density
    , observe
    , determine
    
    -- * Implementation details
    , Backward(..)
    , perform
    , constrainValue
    , constrainOutcome
    ) where

#if __GLASGOW_HASKELL__ < 710
import           Data.Functor         ((<$>))
import           Control.Applicative  (Applicative(..))
#endif
import           Data.Functor.Compose (Compose(..))
import           Control.Monad        ((<=<))
import           Data.Foldable        (Foldable)
import qualified Data.Foldable        as F
import           Data.Traversable     (Traversable)
import qualified Data.Traversable     as T
import qualified Data.Text            as Text

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.Nat (Nat)
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.TypeOf
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.DatumCase
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Evaluation.Types
import Language.Hakaru.Evaluation.Lazy
import qualified Language.Hakaru.Syntax.Prelude as P
import qualified Language.Hakaru.Expect         as E

----------------------------------------------------------------

fst_Whnf :: (ABT Term abt) => Whnf abt (HPair a b) -> abt '[] a
fst_Whnf (Neutral e) = P.fst e
fst_Whnf (Head_   v) = fst (reifyPair v)

snd_Whnf :: (ABT Term abt) => Whnf abt (HPair a b) -> abt '[] b
snd_Whnf (Neutral e) = P.snd e
snd_Whnf (Head_   v) = snd (reifyPair v)


-- N.B., the old version used to use the @env@ hack in order to
-- handle the fact that free variables can change their type
-- (eewww!!); we may need to do that again, but we should avoid it
-- if we can possibly do so.
--
-- N.B., the Backward requirement is probably(?) phrased to be overly strict
--
-- | This function fils the role that the old @runDisintegrate@
-- did. It's unclear what exactly the old @disintegrate@ was supposed
-- to be doing...
disintegrate
    :: (ABT Term abt, Backward a a)
    => abt '[] ('HMeasure (HPair a b))
    -> [abt '[] (a ':-> 'HMeasure b)] -- this Hakaru function is measurable
disintegrate m =
    [ syn (Lam_ :$ bind x m' :* End)
    | m' <- runDisintegrate
    ]
    where
    x = Variable Text.empty (nextFree m)
            (fst . sUnPair . sUnMeasure $ typeOf m)

    runDisintegrate =
        flip runM [Some2 m, Some2 (var x)] $ do
            ab <- perform m
            -- TODO: improve sharing by: if @ab@ is neutral, then
            -- generate a let-binding and return the variables;
            -- else, project out the parts.
            a <- evaluate_ (fst_Whnf ab) -- must factor out since 'constrainValue' asks for a 'Whnf'
            constrainValue a (var x)
            evaluate_ (snd_Whnf ab) -- not just 'return' since we need 'Whnf'
{-
-- old CPS version:
    P.lam $ \a ->
    fromWhnf $ unM (perform m) (\ab ->
      unM (constrainValue (fst ab) a) (\h' ->
        residualizeContext h' (P.dirac $ P.snd ab)))
      emptyContext

-- old finally-tagless version:
    runCompose $
    P.lam $ \x ->
    runLazy $
    P.snd <$> conditionalize (P.pair (lazy . return $ Value x) P.unit) m
    -- N.B., I think that use of @unit@ is for giving a "don't care" pattern; rather than actually having anything to do with the @HUnit@ type. We should avoid this by having 'conditionalize' actually accept some form of pattern (for possible observations) rather than accepting terms.
    -- TODO: can we lift the @lam(\x ->@ over the @runCompose@? if so, then we can make sure those functions only need to be called inside 'conditionalize'
-}


-- N.B., the old version used to use the @env@ hack in order to
-- handle the fact that free variables can change their type
-- (eewww!!); we may need to do that again, but we should avoid it
-- if we can possibly do so.
--
-- N.B., we intentionally phrase the Backward requirement to be
-- overly strict
density
    :: (ABT Term abt, Backward a a)
    => abt '[] ('HMeasure a)
    -> [abt '[] (a ':-> 'HProb)] -- TODO: make this a Haskell function?
density m =
    [ syn (Lam_ :$ bind x (E.total m') :* End)
    | m' <- conditionalize (var x) m
    ]
    where
    x = Variable Text.empty (nextFree m) (sUnMeasure $ typeOf m)
{-
    -- > P.lam $ \x -> E.total (conditionalize x m)
    -- BUG: we need to wrap @x@ in the @scalar0@ wrapper before handing it to 'conditionalize'
    -- @scalar0@ means forward is no-op and backward is bot.
-}{-
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


-- N.B., the old version used to use the @env@ hack (but not on the
-- first argument) in order to handle the fact that free variables
-- can change their type (eewww!!); we may need to do that again,
-- but we should avoid it if we can possibly do so.
--
-- TODO: what's the point of having this function instead of just
-- using @disintegrate m `app` x@ ? I.E., what does the @scalar0@
-- wrapper actually achieve; i.e., how does it direct things instead
-- of just failing when we try to go the wrong direction?
--
-- BUG: come up with new names avoid name conflict vs the Prelude
-- function.
observe
    :: (ABT Term abt, Backward a a)
    => abt '[] a
    -> abt '[] ('HMeasure (HPair a b))
    -> [abt '[] ('HMeasure b)]
observe x m =
    (P.snd P.<$>) <$> conditionalize (P.pair x P.unit) m
    -- N.B., see the note at 'disintegrate' about the use of @unit@ here...


-- N.B., all arguments used to have type @Lazy s repr@ instead of @abt '[]@
--
-- | This is what used to be called @disintegrate@. I think this
-- new name captures whatever it is that funtion was actually
-- supposed to be doing?
--
-- The first argument is a representation of a projection function
-- followed by equality; for example @(pair x unit)@ rather than
-- @(x ==) . fst@. This trick isn't used in the paper, and probably
-- doesn't generalize...
--
-- TODO: whatever this function is supposed to do, it should probably
-- be the one that's the primop rather than 'disintegrate'.
conditionalize
    :: (ABT Term abt, Backward ab a)
    => abt '[] a
    -> abt '[] ('HMeasure ab)
    -> [abt '[] ('HMeasure ab)]
conditionalize a m =
    error "TODO: conditionalize"
    {-
    let n = do
            x  <- forward m
            ab <- memo (unMeasure x)
            backward_ ab a
            return ab
    in Lazy
        (return . Measure $ Lazy
            (n >>= forward)
            (\t -> n >>= (`backward` t)))
        (\_ -> bot)
    -}


-- | Arbitrarily choose one of the possible alternatives. In the
-- future, this function should be replaced by a better one that
-- takes some sort of strategy for deciding which alternative to
-- choose.
determine :: (ABT Term abt) => [abt '[] a] -> Maybe (abt '[] a)
determine []    = Nothing
determine (m:_) = Just m


----------------------------------------------------------------
----------------------------------------------------------------
-- BUG: replace all the -XTypeSynonymInstances with a single general instance for all @'HData@

class Backward (b :: Hakaru) (a :: Hakaru) where
    {-
    backward_ :: (ABT Term abt) => Lazy s abt b -> Lazy s abt a -> M s abt ()
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
{-
data L s abt a = L
    { forward  :: M s abt (Whnf (L s abt) a)
    , backward :: Whnf (L s abt) a -> M s abt ()
    }

-- TODO: make the length indexing explicit:
-- > data C abt a = C { unC :: forall n. Sing n -> [Vec (Some1 abt) n -> a] }
--
-- TODO: does the old version actually mean to erase type info? or should we rather use:
-- > data C abt a = C { unC :: forall xs. Sing xs -> [List1 abt xs -> a] }
--
-- TODO: should we add back in something like @C@ for interpreting\/erasing the uses of 'Lub_'?
data C abt a = C { unC :: Nat -> [[Some1 abt] -> a] }

type Lazy s abt a = L s (C abt) a
-}

----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: move these helper functions into Lazy/Types.hs or wherever else we move the definition of the 'M' monad.

{- -- Is called 'empty' or 'mzero'
-- | It is impossible to satisfy the constraints, or at least we
-- give up on trying to do so.
bot :: (ABT Term abt) => M abt a
bot = M $ \_ _ -> []
-}

-- | The empty measure is a solution to the constraints.
reject :: (ABT Term abt) => M abt a
reject = M $ \_ _ -> [syn (Superpose_ [])]


-- Something essentially like this function was called @insert_@
-- in the finally-tagless code.
--
-- | Emit some code that binds a variable, and return the variable
-- thus bound. The function says what to wrap the result of the
-- continuation with; i.e., what we're actually emitting.
emit
    :: (ABT Term abt)
    => Text.Text
    -> Sing a
    -> (forall r. abt '[a] ('HMeasure r) -> abt '[] ('HMeasure r))
    -> M abt (Variable a)
emit hint typ f = do
    x <- freshVar hint typ
    M $ \c h -> (f . bind x) <$> c x h

-- This function was called @lift@ in the finally-tagless code.
-- | Emit an 'MBind' (i.e., \"@m >>= \x ->@\") and return the
-- variable thus bound (i.e., @x@).
emitMBind :: (ABT Term abt) => abt '[] ('HMeasure a) -> M abt (Variable a)
emitMBind m =
    emit Text.empty (sUnMeasure $ typeOf m)
        (\e -> syn (MBind :$ m :* e :* End))

-- | A variant of 'emitMBind' that returns the variable as a 'Whnf'.
emitMBind_Whnf :: (ABT Term abt) => MeasureEvaluator abt (M abt)
emitMBind_Whnf e = (Neutral . var) <$> emitMBind e

-- This function was called @insert_@ in the old finally-tagless code.
-- | Emit some code that doesn't bind any variables. This function
-- provides an optimisation over using 'emit' and then discarding
-- the generated variable.
emit_
    :: (ABT Term abt)
    => (forall r. abt '[] ('HMeasure r) -> abt '[] ('HMeasure r))
    -> M abt ()
emit_ f = M $ \c h -> f <$> c () h

-- | Emit an 'MBind' that discards its result (i.e., \"@m >>@\").
-- We restrict the type of the argument to be 'HUnit' so as to avoid
-- accidentally dropping things.
emitMBind_ :: (ABT Term abt) => abt '[] ('HMeasure HUnit) -> M abt ()
emitMBind_ m = emit_ (m P.>>)


-- N.B., this use of 'T.traverse' is definitely correct. It's
-- sequentializing @t [abt '[] ('HMeasure a)]@ into @[t (abt '[]
-- ('HMeasure a))]@ by chosing one of the possibilities at each
-- position in @t@. No heap\/context effects can escape to mess
-- things up. In contrast, using 'T.traverse' to sequentialize @t
-- (M abt a)@ as @M abt (t a)@ is /wrong/! Doing that would give
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
    :: (ABT Term abt, Traversable t)
    => (forall r. t (abt '[] ('HMeasure r)) -> abt '[] ('HMeasure r))
    -> t (M abt a)
    -> M abt a
emitFork_ f ms = M $ \c h -> f <$> T.traverse (\m -> unM m c h) ms

-- | Emit a 'Superpose_' of the alternatives, each with unit weight.
emitSuperpose :: (ABT Term abt) => [M abt a] -> M abt a
emitSuperpose [m] = m
emitSuperpose ms  =
    emitFork_ (\es -> P.superpose [(P.prob_ 1, e) | e <- es]) ms

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

instance Foldable (GBranch a) where
    foldMap f (GBranch _ _ x) = f x

instance Traversable (GBranch a) where
    traverse f (GBranch pat vars x) = GBranch pat vars <$> f x

-- N.B., this function does not freshen the variables bound by each
-- 'GBranch'. It's the caller's responsability to perform that
-- freshening when turning each original @Branch a abt b@ into
-- @GBranch a (M abt x)@. This organization is necessary since we
-- need to have already done the renaming when we turn the underlying
-- @abt xs b@ into @(List1 Variable xs, M abt x)@.
--
-- TODO: we want a variant of this function which returns the list
-- of bound variables along with the @b@; since that's required for
-- the continuation to do things that might vary depending on the
-- bound variables.
emitCase
    :: (ABT Term abt)
    => abt '[] a
    -> [GBranch a (M abt b)]
    -> M abt b
emitCase e =
    emitFork_ (syn . Case_ e . fmap fromGBranch . getCompose) . Compose
{-
-- Alternative implementation which I believe has the same semantics:
emitCase e ms =
    M $ \c h -> (syn . Case_ e) <$> T.traverse (runBranch c h) ms
    where
    -- This function has a type isomorphic to:
    -- > GBranch a (M abt b) -> Ran (Ans abt) (Ans' abt) b
    -- where:
    -- > Ans' abt b = ListContext abt -> [Branch a abt ('HMeasure b)]
    -- This is very similar to but not quite the same as:
    -- > GBranch a (M abt b) -> M abt b
    -- Since @M abt = Codensity (Ans abt) = Ran (Ans abt) (Ans abt)@.
    runBranch c h = fmap fromGBranch . T.traverse (\m -> unM m c h)
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
    -> M abt (Whnf abt b)
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
    -> M abt (Whnf abt b)
foo' e bs = do
    myBody <- emitCase e =<< T.traverse (applyBranch return) bs
    evaluate_ myBody

----------------------------------------------------------------
-- BUG: forward disintegration is not identical to partial evaluation,
-- as noted at the top of the file. We need to ensure that no
-- heap-bound variables remain in the result; namely, we need to
-- ensure that in the two places where we call 'emitMBind_Whnf'
evaluate_ :: (ABT Term abt) => TermEvaluator abt (M abt)
evaluate_ = evaluate perform

-- | Simulate performing 'HMeasure' actions by simply emiting code
-- for those actions, returning the bound variable.
perform :: (ABT Term abt) => MeasureEvaluator abt (M abt)
perform e0 =
    caseVarSyn e0 performVar $ \t ->
        case t of
        Dirac :$ e1 :* End       -> evaluate_ e1
        MeasureOp_ _ :$ _        -> emitMBind_Whnf e0
        {- -- TODO: something more like this:
        MeasureOp_ o :$ es -> do
            es' <- traverse21 evaluate_ es
            emitMBind_Whnf (MeasureOp_ o :$ es')
        -- where that call to 'evaluate_' only does whatever work is needed to ensure that no heap-bound variables occur in @es'@; doesn't need to generate a 'Whnf' or anything
        -}
        MBind :$ e1 :* e2 :* End ->
            caseBind e2 $ \x e2' ->
                push (SBind x $ Thunk e1) e2' perform
        Superpose_ pes ->
            emitSuperpose
                [ unsafePush (SWeight $ Thunk p) >> perform e
                | (p,e) <- pes ]

        -- N.B., be sure you've covered all the heads before falling
        -- through to this branch. (The 'WAnn' head works fine on
        -- fallthrough.)
        --
        -- TODO: add a @mustPerform@ predicate like we have 'mustCheck'
        -- in TypeCheck.hs...?
        _ -> evaluate_ e0 >>= performWhnf


-- TODO: I think this is the right definition...
performVar :: (ABT Term abt) => Variable ('HMeasure a) -> M abt (Whnf abt a)
performVar = performWhnf <=< update perform evaluate_

performWhnf
    :: (ABT Term abt) => Whnf abt ('HMeasure a) -> M abt (Whnf abt a)
performWhnf (Head_   v) = perform $ fromHead v
performWhnf (Neutral e) = emitMBind_Whnf e


----------------------------------------------------------------
-- TODO: see the todo for 'constrainOutcome'
constrainValue :: (ABT Term abt) => Whnf abt a -> abt '[] a -> M abt ()
constrainValue = error "TODO: constrainValue"
{-
constrainValue v0 e0 =
    {-
    case e0 of
    u | atomic u -> bot
    -}
    caseVarSyn e0 (constrainVariable v0) $ \t ->
        case t of
        Value_ v
            | "dirac v has a density wrt the ambient measure" -> todo
            | otherwise -> bot

        Datum_  d         ->
        Empty_            ->
        Array_  e1 e2     ->
        Lam_ :$ e1 :* End ->
        Dirac        :$ _ ->
        MBind        :$ _ ->
        MeasureOp_ _ :$ _ ->
        Superpose_ _      ->

        App_ :$ e1 :* e2 :* End ->
        Let_ :$ e1 :* e2 :* End ->
        Ann_      typ :$ e1 :* End -> constrainValue v0 e1
        CoerceTo_   c :$ e1 :* End -> constrainValue (unsafeFrom c v0) e1
        UnsafeFrom_ c :$ e1 :* End -> constrainValue (coerceTo   c v0) e1
        NaryOp_     o    es        -> constrainNaryOp v0 o es
        PrimOp_     o :$ es        -> constrainPrimOp v0 o es
        Expect  :$ e1 :* e2 :* End ->

        Case_ e bs -> do
            match <- matchBranches evaluateDatum e bs
            case match of
                Nothing -> error "constrainValue{Case_}: nothing matched!"
                Just (GotStuck, _) -> do
                    -- TODO: if any branch returns 'bot' then the whole thing should be 'bot'. But we should 'lub' together against the alternative choice of trying to go forward on the scrutinee in order to eliminate the 'bot'
                    -- TODO: how to percolate constraints up through the scrutinee?
                    bs' <- T.traverse (\b -> constrainBranch v0 e b) bs
                    return . Neutral . syn $ Case_ e bs'
                Just (Matched ss Nil1, body) ->
                    pushes (toStatements ss) body (constrainValue v0)
    {-
    Var x ->  M $ \c h ->
        case lookup x h of
        Found h1 binding h2 ->
            case binding of
            SLeft _x e1 ->
                -- TODO: figure out how to reuse the implementation of @unleft@\/@unright@ from 'update'
                unM (evaluate e1) (\v1 -> unleft v1 (\e2 -> unM (constrainValue e1 v0) (\h1' -> c (glue h1' (SLet x v0) h2)))) h1
            SRight _x e1 ->
                unM (evaluate e1) (\v1 -> unright v1 (\e2 -> unM (constrainValue e1 v0) (\h1' -> c (glue h1' (SLet x v0) h2)))) h1
    -}
    

constrainVariable
    :: (ABT Term abt)
    => Whnf abt a
    -> Variable a
    -> M abt ()
constrainVariable v0 x =
    -- If we get 'Nothing', then it turns out @x@ is a free variable. If @x@ is a free variable, then it's a neutral term; and we return 'bot' for neutral terms
    fmap (maybe bot id) . select x $ \s ->
        case s of
        SBind y e -> do
            Refl <- varEq x y
            Just $ do
                constrainOutcome v0 e
                unsafePush (SLet x $ Whnf_ v0)
        SLet y e -> do
            Refl <- varEq x y
            Just $ do
                constrainValue v0 e
                unsafePush (SLet x $ Whnf_ v0)
        SWeight _ -> Nothing


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
-- <https://github.com/hakaru-dev/hakaru/blob/v0.2.0/Language/Hakaru/Lazy.hs>
-}

-- TODO: do we really need to allow all Whnf, or do we just need
-- variables (or neutral terms)? Do we actually want (hnf)terms at
-- all, or do we want (hnf)patterns or something to more generally
-- capture (hnf)measurable events?
constrainOutcome
    :: (ABT Term abt) => Whnf abt a -> abt '[] ('HMeasure a) -> M abt ()
constrainOutcome = error "TODO: constrainOutcome"
{-
constrainOutcome v0 e0 = do
    w0 <- evaluate e0
    case w0 of
        Neutral _ -> bot
        Head_ v0 ->
            case v0 of
             WValue v
             WDatum d
             WEmpty
             WArray e1 e2
             WLam e1
             WMeasure e1 ->
                caseVarSyn (error "TODO") $ \t ->
                    case t of
                    -- Impossible cases because wrong type:
                    -- Value_ v
                    -- Datum_ d
                    -- Empty_
                    -- Array_ e1 e2
                    -- Lam_ :$ e1 :* End
                    -- CoerceTo_   c :$ e1 :* End
                    -- UnsafeFrom_ c :$ e1 :* End
                    -- NaryOp_ o es
                    -- PrimOp o :$ es -- other than the two below
                    -- Expect :$ e1 :* e2 :* End ->
                    
                    Dirac :$ e1 :* End -> constrainValue v0 e1

                    MBind :$ e1 :* e2 :* End ->
                        caseBind e2 $ \x e2' -> do
                            push (SBind x e1) e2' (constrainOutcome v0)

                    Superpose_ pes ->
                        -- BUG: not quite right; we need to pop the weight back off again to build up the new superpose, or something...
                        fmap P.superpose . T.for pes $ \(p,e) -> do
                            unsafePush (SWeight p)
                            constrainOutcome v0 e

                    MeasureOp_ o :$ es -> constrainMeasureOp v0 o es
                    
                    
                    PrimOp_ (Index _) :$ e1 :* e2 :* End ->
                    PrimOp_ (Reduce _) :$ e1 :* e2 :* e3 :* End ->

                    
                    App_ :$ e1 :* e2 :* End ->
                    Let_ :$ e1 :* e2 :* End ->
                    Ann_ typ :$ e1 :* End -> constrainOutcome v0 e1
                    Case_ e bs ->


-- TODO: define helper methods of 'M' for emitting 'observe' and 'weight'

constrainMeasureOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => Whnf abt a
    -> MeasureOp typs a
    -> SCon args ('HMeasure a)
    -> M abt ()
constrainMeasureOp v0 = go
    where
    -- Per the paper
    go Lebesgue End -> M $ \c h -> c h

    -- TODO: I think, based on Hakaru v0.2.0
    go Counting End -> M $ \c h -> c h

    go Categorical (e1 :* End) ->

    -- Per the paper
    -- BUG: must make sure @lo@ and @hi@ don't have heap-bound vars!
    -- TODO: let-bind @v0@ to avoid repeating it (ditto for @lo@,@hi@)
    go Uniform (lo :* hi :* End) -> M $ \c h ->
        P.observe (lo P.<= v0 P.&& v0 P.<= hi)
        P.>> P.weight (P.recip (hi P.- lo))
        P.>> c h

    -- TODO: I think, based on Hakaru v0.2.0
    -- BUG: where does @v0@ come into it?
    -- BUG: must make sure @mu@ and @sd@ don't have heap-bound vars!
    -- TODO: let-binding to avoid repeating @mu@ and @sd@
    go Normal (mu :* sd :* End) -> M $ \c h ->
        P.weight
            (P.exp (P.negate (x P.- mu) P.^ P.int_ 2
                P./ P.fromProb (2 P.* sd P.** 2))
            P./ sd
            P./ P.sqrt (2 P.* P.pi))
        P.>> c h

    go Poisson (e1 :* End) ->
    go Gamma (e1 :* e2 :* End) ->
    go Beta (e1 :* e2 :* End) ->
    go (DirichletProcess _) (e1 :* e2 :* End) ->
    go (Plate _) (e1 :* End) ->
    go (Chain _ _) (e1 :* e2 :* End) ->
    


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
