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

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.12.14
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
    , Condition(..)
    , conditionalize
    , perform
    , atomize
    , constrainValue
    , constrainOutcome
    ) where

#if __GLASGOW_HASKELL__ < 710
import           Data.Functor         ((<$>))
import           Data.Foldable        (Foldable, foldMap)
import           Data.Traversable     (Traversable)
import           Control.Applicative  (Applicative(..))
#endif
import           Control.Applicative  (Alternative(..))
import           Data.Functor.Compose (Compose(..))
import           Control.Monad        ((<=<))
import qualified Data.Traversable     as T
import qualified Data.Text            as Text
import           Data.Sequence        (Seq)
import qualified Data.Sequence        as S

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.HClasses
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.TypeOf
import qualified Language.Hakaru.Syntax.Coercion as C
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Evaluation.Types
import Language.Hakaru.Evaluation.Lazy
import qualified Language.Hakaru.Syntax.Prelude as P
import qualified Language.Hakaru.Expect         as E

----------------------------------------------------------------
-- N.B., for all these functions the old version used to use the
-- @env@ hack in order to handle the fact that free variables can
-- change their type (eewww!!); we may need to do that again, but
-- we should avoid it if we can possibly do so.


-- | Disintegrate a measure over pairs with respect to the lebesgue
-- measure on the first component. That is, for each measure kernel
-- @n <- disintegrate m@ we have that @m == bindx lebesgue n@.
--
-- This function fills the role that the old @runDisintegrate@ did.
-- It's unclear what exactly the old function called @disintegrate@
-- was supposed to be doing...
disintegrate
    :: (ABT Term abt)
    => abt '[] ('HMeasure (HPair a b))
    -> [abt '[] (a ':-> 'HMeasure b)] -- this Hakaru function is measurable
disintegrate m = do
    let x = Variable Text.empty (nextFree m)
            (fst . sUnPair . sUnMeasure $ typeOf m)
    m' <- flip runM [Some2 m, Some2 (var x)] $ do
        ab    <- perform m
        (a,b) <- emitUnpair ab
        a'    <- atomize a
        constrainValue a' (var x)
        evaluate_ b -- TODO: 'atomize' instead?
    return $ syn (Lam_ :$ bind x m' :* End)


-- TODO: is the resulting function guaranteed to be measurable? if
-- not, should we make it into a Haskell function instead?
--
-- | Return the density function for a given measure.
density
    :: (ABT Term abt)
    => abt '[] ('HMeasure a)
    -> [abt '[] (a ':-> 'HProb)]
density m = do
    let x = Variable Text.empty (nextFree m) (sUnMeasure $ typeOf m)
    m' <- conditionalize (Condition PVar (var x)) m
    return $ syn (Lam_ :$ bind x (E.total m') :* End)

    -- TODO: In the old code we wrapped @x@ in @scalar0@ before
    -- handing it to 'conditionalize'; where @scalar0@ means forward
    -- is no-op and backward is bot. Do we still need to do anything
    -- like that?


-- TODO: what's the point of having this function instead of just
-- using @observe x m = disintegrate m `app` x@?
--
-- BUG: come up with new names avoid name conflict vs the Prelude
-- function.
observe
    :: (ABT Term abt)
    => abt '[] a
    -> abt '[] ('HMeasure (HPair a b))
    -> [abt '[] ('HMeasure b)]
observe x m =
    (P.snd P.<$>) <$> conditionalize (Condition (pPair PVar PWild) x) m


-- | A condition is a projection function followed by an equality
-- constraint. This serves the same role as the old @Backward@
-- class. That class used an ad-hoc representation of projection
-- functions where we take an arbitrary term and consider it a
-- pattern, using 'P.unit' as the \"don't care\" wildcard; for
-- example @(P.pair e P.unit)@ is the old representation of the
-- constraint @\x -> P.fst x == e@. We replace the old encoding by
-- using an actual 'Pattern' (with a single variable) to make things
-- a bit more explicit\/clear; thus @(Condition pat e)@ represents
-- the constraint @\x -> case x of { pat y -> y == e ; _ -> False }@.
-- Naturally, this doesn't account for other non-structural forms
-- of \"projection functions\", but then neither did the old code.
--
-- This trick isn't used in the paper, and probably doesn't generalize.
--
-- TODO: If we're trying to generalize what 'disintegrate' does
-- (rather than what 'observe' does), then we just need the pattern
-- and can treat the value of type @b@ at that position as a
-- lambda-bound variable. Of course, ideally, we'd want some sort
-- of dual projection function allowing us to return something of
-- \"@a - b@\" type (i.e., the appropriate one-hole version of the
-- \"@∂a/∂b@\" type).
data Condition (abt :: [Hakaru] -> Hakaru -> *) (a :: Hakaru) =
    forall b. Condition (Pattern '[b] a) (abt '[] b)


-- | This is what used to be called @disintegrate@. I think this
-- new name captures whatever it is that funtion was actually
-- supposed to be doing?
--
-- TODO: whatever this function is supposed to do, it should probably
-- be the one that's the primop rather than 'disintegrate'.
conditionalize
    :: (ABT Term abt)
    => Condition abt a
    -> abt '[] ('HMeasure a)
    -> [abt '[] ('HMeasure a)]
conditionalize (Condition pat b) m =
    -- TODO: is this at all right??
    flip runM [Some2 b, Some2 m] $ do
        a <- perform m
        -- According to the old code, we should memoize here...
        -- TODO: what was the purpose of using @unMeasure@ before memoizing?
        x <- var <$> emitLet (fromWhnf a)
        -- TODO: maybe just store the @typeOf b@ rather than computing it?
        y <- freshVar Text.empty (typeOf b)
        -- TODO: get 'emitCase' to partially evaluate the case expression away when it can (assuming we don't @emitLet a@). In order to do this in a nice clean way, we'll have to go back to trying to implement my previous @GGBranch@ approach.
        emitCase x
            [ GBranch pat (Cons1 y Nil1) $ do
                b' <- atomize b
                constrainValue b' (var y)
                return (Neutral x)
            , GBranch PWild Nil1 $ reject
            ]


-- | Arbitrarily choose one of the possible alternatives. In the
-- future, this function should be replaced by a better one that
-- takes some sort of strategy for deciding which alternative to
-- choose.
determine :: (ABT Term abt) => [abt '[] a] -> Maybe (abt '[] a)
determine []    = Nothing
determine (m:_) = Just m


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

{-
fst_Whnf :: (ABT Term abt) => Whnf abt (HPair a b) -> abt '[] a
fst_Whnf (Neutral e) = P.fst e
fst_Whnf (Head_   v) = fst (reifyPair v)

snd_Whnf :: (ABT Term abt) => Whnf abt (HPair a b) -> abt '[] b
snd_Whnf (Neutral e) = P.snd e
snd_Whnf (Head_   v) = snd (reifyPair v)

ifte_Whnf :: (ABT Term abt) => Whnf abt HBool -> abt '[] a -> abt '[] a -> abt '[] a
ifte_Whnf (Neutral e) t f = P.if_ e t f
ifte_Whnf (Head_   v) t f = if reify v then t else f
-}


-- | It is impossible to satisfy the constraints, or at least we
-- give up on trying to do so. This function is identical to 'empty'
-- and 'mzero' for 'M'; we just give it its own name since this is
-- the name used in our papers.
bot :: (ABT Term abt) => M abt a
bot = M $ \_ _ -> []


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


-- | A smart constructor for emitting let-bindings. If the input
-- is already a variable then we just return it; otherwise we emit
-- the let-binding.
emitLet :: (ABT Term abt) => abt '[] a -> M abt (Variable a)
emitLet e =
    caseVarSyn e return $ \_ ->
        emit Text.empty (typeOf e)
            (\m -> syn (Let_ :$ e :* m :* End))


-- | A smart constructor for emitting \"unpair\". If the input
-- argument is actually a constructor then we project out the two
-- components; otherwise we emit the case-binding and return the
-- two variables.
emitUnpair
    :: (ABT Term abt)
    => Whnf abt (HPair a b)
    -> M abt (abt '[] a, abt '[] b)
emitUnpair (Head_   e) = return $ reifyPair e
emitUnpair (Neutral e) = do
    let (a,b) = sUnPair (typeOf e)
    x <- freshVar Text.empty a
    y <- freshVar Text.empty b
    M $ \c h ->
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
    -> M abt ()
emit_ f = M $ \c h -> f <$> c () h


-- | Emit an 'MBind' that discards its result (i.e., \"@m >>@\").
-- We restrict the type of the argument to be 'HUnit' so as to avoid
-- accidentally dropping things.
emitMBind_ :: (ABT Term abt) => abt '[] ('HMeasure HUnit) -> M abt ()
emitMBind_ m = emit_ (m P.>>)


-- | Emit an assertion that the condition is true.
emitObserve :: (ABT Term abt) => abt '[] HBool -> M abt ()
emitObserve b = emit_ (P.observe b) -- == emit_ $ \m -> P.if_ b m P.reject


emitWeight :: (ABT Term abt) => abt '[] 'HProb -> M abt ()
emitWeight w = emit_ (P.pose w)


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
emitSuperpose
    :: (ABT Term abt)
    => [abt '[] ('HMeasure a)]
    -> M abt (Variable a)
emitSuperpose es =
    emitMBind (P.superpose [(P.prob_ 1, e) | e <- es])


-- | Emit a 'Superpose_' of the alternatives, each with unit weight.
choose :: (ABT Term abt) => [M abt a] -> M abt a
choose [m] = m
choose ms  =
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
-- ensure that in the two places where we call 'emitMBind'
evaluate_ :: (ABT Term abt) => TermEvaluator abt (M abt)
evaluate_ = evaluate perform


-- | Simulate performing 'HMeasure' actions by simply emiting code
-- for those actions, returning the bound variable.
perform :: (ABT Term abt) => MeasureEvaluator abt (M abt)
perform e0 =
    caseVarSyn e0 performVar $ \t ->
        case t of
        Dirac :$ e1 :* End       -> evaluate_ e1
        MeasureOp_ o :$ es       -> do
            es' <- traverse21 atomizeCore es
            x   <- emitMBind $ syn (MeasureOp_ o :$ es')
            return (Neutral $ var x)
        MBind :$ e1 :* e2 :* End ->
            caseBind e2 $ \x e2' ->
                push (SBind x $ Thunk e1) e2' perform
        Superpose_ pes ->
            -- TODO: may want to do this directly rather than using 'choose' and then adjusting the weight...
            choose
                [ unsafePush (SWeight $ Thunk p) >> perform e
                | (p,e) <- pes ]

        -- N.B., be sure you've covered all the heads before falling
        -- through to this branch. (The 'WAnn' head works fine on
        -- fallthrough.)
        --
        -- TODO: add a @mustPerform@ predicate like we have 'mustCheck'
        -- in TypeCheck.hs...?
        --
        -- TODO: we should jump right into the 'Term'-analyzing part of 'evaluate' rather than repeating the 'caseVarSyn' there...
        _ -> evaluate_ e0 >>= performWhnf


-- TODO: I think this is the right definition...
performVar :: (ABT Term abt) => Variable ('HMeasure a) -> M abt (Whnf abt a)
performVar = performWhnf <=< update perform evaluate_


-- HACK: we have to special case the 'WAnn' constructor in order
-- to avoid looping forever (since annotations just evaluate to
-- themselves). We'd prolly have the same issue with coercions
-- excepting that there are no coercions for 'HMeasure' types.
--
-- TODO: for the 'WAnn' constructor we push the annotation down
-- into the 'Whnf' result. This is better than dropping it on the
-- floor, but may still end up producing programs which don't
-- typecheck (or don't behave nicely with 'typeOf') since it moves
-- the annotation around. To keep the annotation in the same place
-- as the input, we need to pass it to 'perform' somehow so that
-- it can emit the annotation when it emits 'MBind' etc. (That
-- prolly means we shouldn't handle 'WAnn' here, but rather should
-- handle it in the definition of 'perform' itself...)
performWhnf
    :: (ABT Term abt) => Whnf abt ('HMeasure a) -> M abt (Whnf abt a)
performWhnf (Head_ (WAnn typ v)) =
    ann (sUnMeasure typ) <$> performWhnf (Head_ v)
performWhnf (Head_   v) = perform $ fromHead v
performWhnf (Neutral e) = (Neutral . var) <$> emitMBind e


-- TODO: now that we've broken 'atomize' and 'atomizeCore' out into
-- separate top-level functions, we should check to make sure we
-- don't pay too much for passing the dictionaries back and forth.
-- If we do, then we should inline the definitions into each other
-- and use -XScopedTypeVaribles to ensure the recursive calls close
-- over the dictionary parameter.

-- | This name is taken from the old finally tagless code. This
-- does something like giving us full-beta reduction, which should
-- really be the purview of 'evaluate', but the goal of which is
-- to ensure that no heap-bound variables occur in the input term.
atomize :: (ABT Term abt) => TermEvaluator abt (M abt)
atomize e = traverse21 atomizeCore =<< evaluate_ e

-- | Factored out from 'atomize' because we often need this more
-- polymorphic variant when using our indexed 'Traversable' classes.
atomizeCore :: (ABT Term abt) => abt xs a -> M abt (abt xs a)
atomizeCore e =
    let (xs, e') = caseBinds e
    in  (binds_ xs . fromWhnf) <$> atomize e'


----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: see the todo for 'constrainOutcome'
--
-- | N.B., We assume that the first argument, @v0@, is already
-- atomized. So, this must be ensured before recursing, but we can
-- assume it's already been done by the IH.
constrainValue :: (ABT Term abt) => Whnf abt a -> abt '[] a -> M abt ()
constrainValue v0 e0 =
    caseVarSyn e0 (constrainVariable v0) $ \t ->
        case t of
        -- There's a bunch of stuff we don't even bother trying to handle
        Empty_   _               -> error "TODO: disintegrate arrays"
        Array_   _ _             -> error "TODO: disintegrate arrays"
        ArrayOp_ _ :$ _          -> error "TODO: disintegrate arrays"
        Lam_  :$ _  :* End       -> error "TODO: disintegrate lambdas"
        App_  :$ _  :* _ :* End  -> error "TODO: disintegrate lambdas"
        Integrate :$ _ :* _ :* _ :* End ->
            error "TODO: disintegrate integration"
        Summate   :$ _ :* _ :* _ :* End ->
            error "TODO: disintegrate integration"


        -- TODO: where to fit this in?
        -- > u | atomic u -> bot

        -- TODO: Actually, the semantically correct definition is:
        -- > Literal_ v
        -- >     | "dirac v has a density wrt the ambient measure" -> ...
        -- >     | otherwise -> bot
        Literal_ v               -> bot

        Datum_   d               -> bot -- according to the old code. Though there's some discrepancy about whether they used @lazy foo@ vs @scalar0 foo@...
        -- These 'bot's are according to the old finally-tagless code...
        Dirac :$ _ :* End        -> bot
        MBind :$ _ :* _ :* End   -> bot
        MeasureOp_ o :$ es       -> constrainValueMeasureOp v0 o es
        Superpose_ pes           -> bot
        Let_ :$ e1 :* e2 :* End ->
            caseBind e2 $ \x e2' ->
                push (SLet x $ Thunk e1) e2' (constrainValue v0)

        Ann_      typ :$ e1 :* End -> constrainValue  v0 e1
        CoerceTo_   c :$ e1 :* End -> constrainValue  (C.coerceFrom c v0) e1
        -- BUG: for the safe coercions we need to 'emitObserve' as well!
        UnsafeFrom_ c :$ e1 :* End -> constrainValue  (C.coerceTo   c v0) e1
        NaryOp_     o    es        -> constrainNaryOp v0 o es
        PrimOp_     o :$ es        -> constrainPrimOp v0 o es
        Expect  :$ e1 :* e2 :* End -> error "TODO: constrainValue{Expect}"

        Case_ e bs -> error "TODO: constrainValue{Case_}"
            {- -- something like:
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
                -}

        _ :$ _ -> error "constrainValue: the impossible happened"


----------------------------------------------------------------
-- | N.B., We assume that the first argument, @v0@, is already
-- atomized. So, this must be ensured before recursing, but we can
-- assume it's already been done by the IH.
constrainVariable :: (ABT Term abt) => Whnf abt a -> Variable a -> M abt ()
constrainVariable v0 x =
    -- If we get 'Nothing', then it turns out @x@ is a free variable. If @x@ is a free variable, then it's a neutral term; and we return 'bot' for neutral terms
    (maybe bot return =<<) . select x $ \s ->
        case s of
        SBind y e -> do
            Refl <- varEq x y
            Just $ do
                constrainOutcome v0 (fromLazy e)
                unsafePush (SLet x $ Whnf_ v0)
        SLet y e -> do
            Refl <- varEq x y
            Just $ do
                constrainValue v0 (fromLazy e)
                unsafePush (SLet x $ Whnf_ v0)
        SWeight _ -> Nothing
        SIndex y e1 e2 -> do
            Refl <- varEq x y
            Just $ error "TODO: constrainVariable{SIndex}"


----------------------------------------------------------------
-- | N.B., We assume that the first argument, @v0@, is already
-- atomized. So, this must be ensured before recursing, but we can
-- assume it's already been done by the IH.
constrainValueMeasureOp
    :: forall abt typs args a
    .  (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => Whnf abt ('HMeasure a)
    -> MeasureOp typs a
    -> SArgs abt args
    -> M abt ()
constrainValueMeasureOp v0 = go
    where
    -- HACK: we need the -XScopedTypeVariables in order to remove \"ambiguity\" about the choice of 'ABT' instance
    go :: MeasureOp typs a -> SArgs abt args -> M abt ()
    go Lebesgue    = \End               -> bot
    go Counting    = \End               -> bot
    go Categorical = \(e1 :* End)       ->
        constrainValue v0 (P.categorical e1)
    go Uniform     = \(e1 :* e2 :* End) ->
        constrainValue v0 (P.uniform' e1 e2)
    go Normal      = \(e1 :* e2 :* End) ->
        constrainValue v0 (P.normal'  e1 e2)
    go Poisson     = \(e1 :* End)       ->
        constrainValue v0 (P.poisson' e1)
    go Gamma       = \(e1 :* e2 :* End) ->
        constrainValue v0 (P.gamma'   e1 e2)
    go Beta        = \(e1 :* e2 :* End) ->
        constrainValue v0 (P.beta'    e1 e2)
    go (DirichletProcess a) = \(e1 :* e2 :* End) ->
        error "TODO: constrainValueMeasureOp{DirichletProcess}"
    go (Plate a)   = \(e1 :* End)       -> bot -- TODO: can we use P.plate'?
    go (Chain s a) = \(e1 :* e2 :* End) ->
        error "TODO: constrainValueMeasureOp{Chain}" -- We might could use P.chain' except that has a SingI constraint


----------------------------------------------------------------
-- | N.B., We assume that the first argument, @v0@, is already
-- atomized. So, this must be ensured before recursing, but we can
-- assume it's already been done by the IH.
--
-- N.B., we also rely on the fact that our 'HSemiring' instances
-- are actually all /commutative/ semirings. If that ever becomes
-- not the case, then we'll need to fix things here.
--
-- As written, this will do a lot of redundant work in atomizing
-- the subterms other than the one we choose to go backward on.
-- Because evaluation has side-effects on the heap and is heap
-- dependent, it seems like there may not be a way around that
-- issue. (I.e., we could use dynamic programming to efficiently
-- build up the 'M' computations, but not to evaluate them.) Of
-- course, really we shouldn't be relying on the structure of the
-- program here; really we should be looking at the heap-bound
-- variables in the term: choosing each @x@ to go backward on, treat
-- the term as a function of @x@, atomize that function (hence going
-- forward on the rest of the variables), and then invert it and
-- get the Jacobian.
constrainNaryOp
    :: (ABT Term abt)
    => Whnf abt a
    -> NaryOp a
    -> Seq (abt '[] a)
    -> M abt ()
constrainNaryOp v0 o =
    case o of
    Sum theSemi ->
        lubSeq $ \es1 e es2 -> do
            u <- atomize $ syn (NaryOp_ (Sum theSemi) (es1 S.>< es2))
            v <- evaluate_ $ unsafeMinus_ theSemi (fromWhnf v0) (fromWhnf u)
            constrainValue v e
    Prod theSemi ->
        lubSeq $ \es1 e es2 -> do
            u <- atomize $ syn (NaryOp_ (Prod theSemi) (es1 S.>< es2))
            let u' = fromWhnf u -- TODO: emitLet?
            emitWeight $ P.recip (toProb_abs theSemi u')
            v <- evaluate_ $ unsafeDiv_ theSemi (fromWhnf v0) u'
            constrainValue v e
    _ -> error "TODO: constrainNaryOp"


-- TODO: move to Prelude? is this generally useful? Or should we factor out the @toProb@ and @semiringAbs@ parts of it?
toProb_abs :: (ABT Term abt) => HSemiring a -> abt '[] a -> abt '[] 'HProb
toProb_abs HSemiring_Nat  = P.nat2prob
toProb_abs HSemiring_Int  = P.nat2prob . P.abs_
toProb_abs HSemiring_Prob = id
toProb_abs HSemiring_Real = P.abs_


-- TODO: (a) simplify the logic here, (b) move this to Prelude
unsafeMinus_
    :: (ABT Term abt) => HSemiring a -> abt '[] a -> abt '[] a -> abt '[] a
unsafeMinus_ HSemiring_Nat  e1 e2 =
    let signed  = C.singletonCoercion (C.Signed HRing_Int)
        e1' = P.coerceTo_ signed e1
        e2' = P.coerceTo_ signed e2
    in P.unsafeFrom_ signed (e1' P.- e2')
unsafeMinus_ HSemiring_Int  e1 e2 = e1 P.- e2
unsafeMinus_ HSemiring_Prob e1 e2 =
    let signed  = C.singletonCoercion (C.Signed HRing_Real)
        e1' = P.coerceTo_ signed e1
        e2' = P.coerceTo_ signed e2
    in P.unsafeFrom_ signed (e1' P.- e2')
unsafeMinus_ HSemiring_Real e1 e2 = e1 P.- e2


-- TODO: (a) simplify the logic here, (b) move this to Prelude
-- BUG: beware, this is /really unsafe/! We can't rely on unsafe coercions to get things back to the original type when dealing with Nat\/Int. It'd be safer (though no doubt less correct) to use some analog of 'div'\/'quot' rather than @(/)@... but really, we should just handle the 'Prod' cases separately for integral\/non-fractional types.
unsafeDiv_
    :: (ABT Term abt) => HSemiring a -> abt '[] a -> abt '[] a -> abt '[] a
unsafeDiv_ HSemiring_Nat  e1 e2 =
    let continuous  = C.singletonCoercion (C.Continuous HContinuous_Prob)
        e1' = P.coerceTo_ continuous e1
        e2' = P.coerceTo_ continuous e2
    in P.unsafeFrom_ continuous (e1' P./ e2')
unsafeDiv_ HSemiring_Int  e1 e2 =
    let continuous  = C.singletonCoercion (C.Continuous HContinuous_Real)
        e1' = P.coerceTo_ continuous e1
        e2' = P.coerceTo_ continuous e2
    in P.unsafeFrom_ continuous (e1' P./ e2')
unsafeDiv_ HSemiring_Prob e1 e2 = e1 P./ e2
unsafeDiv_ HSemiring_Real e1 e2 = e1 P./ e2


-- TODO: is there any way to optimise the zippering over the Seq, a la 'S.inits' or 'S.tails'?
-- TODO: really we want a dynamic programming approach to avoid unnecessary repetition of calling @evaluateNaryOp evaluate_@ on the two subsequences...
lubSeq :: (Alternative m) => (Seq a -> a -> Seq a -> m b) -> Seq a -> m b
lubSeq f = go S.empty
    where
    go xs ys =
        case S.viewl ys of
        S.EmptyL   -> empty
        y S.:< ys' -> f xs y ys' <|> go (xs S.|> y) ys'

----------------------------------------------------------------
-- HACK: for a lot of these, we can't use the prelude functions
-- because Haskell can't figure out our polymorphism, so we have
-- to define our own versions for manually passing dictionaries
-- around.
--
-- | N.B., We assume that the first argument, @v0@, is already
-- atomized. So, this must be ensured before recursing, but we can
-- assume it's already been done by the IH.
constrainPrimOp
    :: forall abt typs args a
    .  (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => Whnf abt a
    -> PrimOp typs a
    -> SArgs abt args
    -> M abt ()
constrainPrimOp v0 = go
    where
    error_TODO op = error $ "TODO: constrainPrimOp{" ++ op ++"}"

    -- HACK: we need the -XScopedTypeVariables in order to remove \"ambiguity\" about the choice of 'ABT' instance
    go :: PrimOp typs a -> SArgs abt args -> M abt ()
    go Not  = \(e1 :* End)       -> error_TODO "Not"
    go Impl = \(e1 :* e2 :* End) -> error_TODO "Impl"
    go Diff = \(e1 :* e2 :* End) -> error_TODO "Diff"
    go Nand = \(e1 :* e2 :* End) -> error_TODO "Nand"
    go Nor  = \(e1 :* e2 :* End) -> error_TODO "Nor"

    go Pi = \End -> bot -- because @dirac pi@ has no density wrt lebesgue

    go Sin = \(e1 :* End) -> do
        x0 <- var <$> emitLet (fromWhnf v0)
        n  <- var <$> emitMBind P.counting
        let tau_n = P.real_ 2 P.* P.fromInt n P.* P.pi -- TODO: emitLet?
        emitObserve (P.negate P.one P.< x0 P.&& x0 P.< P.one)
        v  <- var <$> emitSuperpose
            [ P.dirac (tau_n P.+ P.asin x0)
            , P.dirac (tau_n P.+ P.pi P.- P.asin x0)
            ]
        emitWeight
            . P.recip
            . P.sqrt
            . P.unsafeProb
            $ (P.one P.- x0 P.^ P.nat_ 2)
        constrainValue (Neutral v) e1

    go Cos = \(e1 :* End) -> do
        x0 <- var <$> emitLet (fromWhnf v0)
        n  <- var <$> emitMBind P.counting
        let tau_n = P.real_ 2 P.* P.fromInt n P.* P.pi
        emitObserve (P.negate P.one P.< x0 P.&& x0 P.< P.one)
        r  <- var <$> emitLet (tau_n P.+ P.acos x0)
        v  <- var <$> emitSuperpose [P.dirac r, P.dirac (r P.+ P.pi)]
        emitWeight
            . P.recip
            . P.sqrt
            . P.unsafeProb
            $ (P.one P.- x0 P.^ P.nat_ 2)
        constrainValue (Neutral v) e1

    go Tan = \(e1 :* End) -> do
        x0 <- var <$> emitLet (fromWhnf v0)
        n  <- var <$> emitMBind P.counting
        r  <- var <$> emitLet (P.fromInt n P.* P.pi P.+ P.atan x0)
        emitWeight $ P.recip (P.one P.+ P.square x0)
        constrainValue (Neutral r) e1

    go Asin = \(e1 :* End) -> do
        x0 <- var <$> emitLet (fromWhnf v0)
        -- TODO: may want to evaluate @cos v0@ before emitting the weight
        emitWeight $ P.unsafeProb (P.cos x0)
        -- TODO: bounds check for -pi/2 <= v0 < pi/2
        constrainValue (Neutral $ P.sin x0) e1

    go Acos = \(e1 :* End) -> do
        x0 <- var <$> emitLet (fromWhnf v0)
        -- TODO: may want to evaluate @sin v0@ before emitting the weight
        emitWeight $ P.unsafeProb (P.sin x0)
        constrainValue (Neutral $ P.cos x0) e1

    go Atan = \(e1 :* End) -> do
        x0 <- var <$> emitLet (fromWhnf v0)
        -- TODO: may want to evaluate @cos v0 ^ 2@ before emitting the weight
        emitWeight $ P.recip (P.unsafeProb (P.cos x0 P.^ P.nat_ 2))
        constrainValue (Neutral $ P.tan x0) e1

    go Sinh      = \(e1 :* End)       -> error_TODO "Sinh"
    go Cosh      = \(e1 :* End)       -> error_TODO "Cosh"
    go Tanh      = \(e1 :* End)       -> error_TODO "Tanh"
    go Asinh     = \(e1 :* End)       -> error_TODO "Asinh"
    go Acosh     = \(e1 :* End)       -> error_TODO "Acosh"
    go Atanh     = \(e1 :* End)       -> error_TODO "Atanh"
    go RealPow   = \(e1 :* e2 :* End) -> error_TODO "RealPow"
        {- -- something like:
        -- TODO: There's a discrepancy between @(**)@ and @pow_@ in the old code...
        do
            v1 <- evaluate_ e1
            -- TODO: if @v1@ is 0 or 1 then bot. Maybe the @log v1@ in @w@ takes care of the 0 case?
            u <- atomize v0
            -- either this from @(**)@:
            emitObserve  $ P.zero P.< u
            w <- atomize $ recip (abs (v0 * log v1))
            emitWeight $ unsafeProb w
            constrainValue (logBase v1 v0) e2
            -- or this from @pow_@:
            w <- atomize $ recip (u * unsafeProb (abs (log v1))
            emitWeight w
            constrainValue (log u / log v1) e2
            -- end.
        <|> do
            v2 <- evaluate_ e2
            -- TODO: if @v2@ is 0 then bot. Maybe the weight @w@ takes care of this case?
            u <- atomize v0
            let ex = v0 ** recip v2
            -- either this from @(**)@:
            emitObserve $ P.zero P.< u
            w <- atomize $ abs (ex / (v2 * v0))
            -- or this from @pow_@:
            let w = abs (fromProb ex / (v2 * fromProb u))
            -- end.
            emitWeight $ unsafeProb w
            constrainValue ex e1
        -}
    go Exp = \(e1 :* End) -> do
        x0 <- var <$> emitLet (fromWhnf v0)
        -- TODO: do we still want/need the @emitObserve (0 < x0)@ which is now equivalent to @emitObserve (0 /= x0)@ thanks to the types?
        emitWeight (P.recip x0)
        constrainValue (Neutral $ P.log x0) e1

    go Log = \(e1 :* End) -> do
        exp_x0 <- var <$> emitLet (P.exp $ fromWhnf v0)
        emitWeight exp_x0
        constrainValue (Neutral exp_x0) e1

    go Infinity         = \End               -> error_TODO "Infinity" -- scalar0
    go NegativeInfinity = \End               -> error_TODO "NegativeInfinity" -- scalar0
    go GammaFunc        = \(e1 :* End)       -> error_TODO "GammaFunc" -- scalar1
    go BetaFunc         = \(e1 :* e2 :* End) -> error_TODO "BetaFunc" -- scalar2
    go (Equal  theOrd)  = \(e1 :* e2 :* End) -> error_TODO "Equal"
    go (Less   theOrd)  = \(e1 :* e2 :* End) -> error_TODO "Less"
    go (NatPow theSemi) = \(e1 :* e2 :* End) -> error_TODO "NatPow"
    go (Negate theRing) = \(e1 :* End) ->
        -- TODO: figure out how to merge this implementation of @rr1 negate@ with the one in 'evaluatePrimOp' to DRY
        -- TODO: just emitLet the @v0@ and pass the neutral term to the recursive call?
        let negate_v0 =
                case v0 of
                Neutral e ->
                    Neutral $ syn (PrimOp_ (Negate theRing) :$ e :* End)
                Head_ v ->
                    case theRing of
                    HRing_Int  -> Head_ . reflect . negate $ reify v
                    HRing_Real -> Head_ . reflect . negate $ reify v
        in constrainValue negate_v0 e1
        {-
        -- We could use this instead, if we don't care about the verbosity of so many let-bindings (or if we were willing to lie about the first argument to 'constrainValue' being \"neutral\"
        let neg = P.primOp1_ $ Negate theRing
        x0 <- var <$> emitLet (fromWhnf v0)
        constrainValue (Neutral $ neg x0) e1
        -}

    go (Abs theRing) = \(e1 :* End) -> do
        let theSemi = hSemiring_HRing theRing
            theOrd  =
                case theRing of
                HRing_Int  -> HOrd_Int
                HRing_Real -> HOrd_Real
            theEq   = hEq_HOrd theOrd
            signed  = C.singletonCoercion (C.Signed theRing)
            zero    = P.zero_ theSemi
            lt      = P.primOp2_ $ Less   theOrd
            eq      = P.primOp2_ $ Equal  theEq
            neg     = P.primOp1_ $ Negate theRing

        x0 <- var <$> emitLet (P.coerceTo_ signed $ fromWhnf v0)
        v  <- var <$> emitMBind
            (P.if_ (lt zero x0)
                (P.superpose
                    [ (P.one, P.dirac x0)
                    , (P.one, P.dirac (neg x0))
                    ])
                (P.if_ (eq zero x0)
                    (P.dirac zero)
                    P.reject))
        constrainValue (Neutral v) e1

    go (Signum theRing) = \(e1 :* End) ->
        case theRing of
        HRing_Real -> bot
        HRing_Int  -> do
            x <- var <$> emitMBind P.counting
            emitObserve $ P.signum x P.== fromWhnf v0
            constrainValue (Neutral x) e1

    go (Recip theFractional) = \(e1 :* End) -> do
        -- TODO: may want to inline @x0@ and try evaluating @e0 ^ 2@ and @recip e0@...
        x0 <- var <$> emitLet (fromWhnf v0)
        emitWeight
            . P.recip
            . P.unsafeProbFraction_ theFractional
            -- TODO: define a dictionary-passing variant of 'P.square' instead, to include the coercion in there explicitly...
            $ square (hSemiring_HFractional theFractional) x0
        constrainValue (Neutral $ P.primOp1_ (Recip theFractional) x0) e1

    go (NatRoot theRadical) = \(e1 :* e2 :* End) ->
        case theRadical of
        HRadical_Prob -> do
            -- TODO: may want to inline @x0@ and try evaluating @u2 * e0@ and @e0 ^ u2@...
            x0 <- var <$> emitLet (fromWhnf v0)
            u2 <- fromWhnf <$> atomize e2
            emitWeight (P.nat2prob u2 P.* x0)
            constrainValue (Neutral $ x0 P.^ u2) e1

    go (Erf theContinuous) = \(e1 :* End) ->
        error "TODO: constrainPrimOp: need InvErf to disintegrate Erf"


-- HACK: can't use @(P.^)@ because Haskell can't figure out our polymorphism
square :: (ABT Term abt) => HSemiring a -> abt '[] a -> abt '[] a
square theSemiring e =
    syn (PrimOp_ (NatPow theSemiring) :$ e :* P.nat_ 2 :* End)


----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: do we really need to allow all Whnf, or do we just need
-- variables (or neutral terms)? Do we actually want (hnf)terms at
-- all, or do we want (hnf)patterns or something to more generally
-- capture (hnf)measurable events?
--
-- | N.B., We assume that the first argument, @v0@, is already
-- atomized. So, this must be ensured before recursing, but we can
-- assume it's already been done by the IH.
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

                    MeasureOp_ o :$ es -> constrainOutcomeMeasureOp v0 o es


                    PrimOp_ (Index _) :$ e1 :* e2 :* End ->
                    PrimOp_ (Reduce _) :$ e1 :* e2 :* e3 :* End ->


                    App_ :$ e1 :* e2 :* End ->
                    Let_ :$ e1 :* e2 :* End ->
                    Ann_ typ :$ e1 :* End -> constrainOutcome v0 e1
                    Case_ e bs ->


-- TODO: should this really be different from 'constrainValueMeasureOp'?
constrainOutcomeMeasureOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => Whnf abt a
    -> MeasureOp typs a
    -> SCon args ('HMeasure a)
    -> M abt ()
constrainOutcomeMeasureOp v0 = go
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
