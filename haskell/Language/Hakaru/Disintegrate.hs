{-# LANGUAGE CPP
           , GADTs
           , EmptyCase
           , KindSignatures
           , DataKinds
           , PolyKinds
           , TypeOperators
           , ScopedTypeVariables
           , Rank2Types
           , MultiParamTypeClasses
           , TypeSynonymInstances
           , FlexibleInstances
           , FlexibleContexts
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.02.09
-- |
-- Module      :  Language.Hakaru.Disintegrate
-- Copyright   :  Copyright (c) 2016 the Hakaru team
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
--
-- /Developer's Note:/ To help keep the code clean, we use the
-- worker\/wrapper transform. However, due to complexities in
-- typechecking GADTs, this often confuses GHC if you don't give
-- just the right type signature on definitions. This confusion
-- shows up whenever you get error messages about an \"ambiguous\"
-- choice of 'ABT' instance, or certain types of \"couldn't match
-- @a@ with @a1@\" error messages. To eliminate these issues we use
-- @-XScopedTypeVariables@. In particular, the @abt@ type variable
-- must be bound by the wrapper (i.e., the top-level definition),
-- and the workers should just refer to that same type variable
-- rather than quantifying over abother @abt@ type. In addition,
-- whatever other type variables there are (e.g., the @xs@ and @a@
-- of an @abt xs a@ argument) should be polymorphic in the workers
-- and should /not/ reuse the other analogous type variables bound
-- by the wrapper.
----------------------------------------------------------------
module Language.Hakaru.Disintegrate
    (
    -- * the Hakaru API
      disintegrateWithVar
    , disintegrate
    , densityWithVar
    , density
    , observe
    , determine
    
    -- * Implementation details
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
import           Control.Monad        ((<=<))
import           Data.Functor.Compose (Compose(..))
import qualified Data.Traversable     as T
import qualified Data.Text            as Text
import qualified Data.IntMap          as IM
import           Data.Sequence        (Seq)
import qualified Data.Sequence        as S
import           Data.Proxy           (KProxy(..))

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing
import qualified Language.Hakaru.Types.Coercion as C
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Syntax.TypeOf
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.DatumCase
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Evaluation.Types
import Language.Hakaru.Evaluation.Lazy
import Language.Hakaru.Evaluation.DisintegrationMonad
import qualified Language.Hakaru.Syntax.Prelude as P
import qualified Language.Hakaru.Expect         as E

{-
import Language.Hakaru.Pretty.Haskell (pretty)
import Debug.Trace (trace)
-}

----------------------------------------------------------------

lam_ :: (ABT Term abt) => Variable a -> abt '[] b -> abt '[] (a ':-> b)
lam_ x e = syn (Lam_ :$ bind x e :* End)


-- | Disintegrate a measure over pairs with respect to the lebesgue
-- measure on the first component. That is, for each measure kernel
-- @n <- disintegrate m@ we have that @m == bindx lebesgue n@. The
-- first two arguments give the hint and type of the lambda-bound
-- variable in the result. If you want to automatically fill those
-- in, then see 'disintegrate'.
--
-- N.B., the resulting functions from @a@ to @'HMeasure b@ are
-- indeed measurable, thus it is safe\/appropriate to use Hakaru's
-- @(':->)@ rather than Haskell's @(->)@.
--
-- BUG: Actually, disintegration is with respect to the /Borel/
-- measure on the first component of the pair! Alas, we don't really
-- have a clean way of describing this since we've no primitive
-- 'MeasureOp' for Borel measures.
--
-- /Developer's Note:/ This function fills the role that the old
-- @runDisintegrate@ did (as opposed to the old function called
-- @disintegrate@). [Once people are familiar enough with the new
-- code base and no longer recall what the old code base was doing,
-- this note should be deleted.]
disintegrateWithVar
    :: (ABT Term abt)
    => Text.Text
    -> Sing a
    -> abt '[] ('HMeasure (HPair a b))
    -> [abt '[] (a ':-> 'HMeasure b)]
disintegrateWithVar hint typ m =
    let x = Variable hint (nextFree m `max` nextBind m) typ
    in map (lam_ x) . flip runDis [Some2 m, Some2 (var x)] $ do
        ab    <- perform m
        (a,b) <- emitUnpair ab
        constrainValue (var x) a
        return b


-- | A variant of 'disintegrateWithVar' which automatically computes
-- the type via 'typeOf'.
disintegrate
    :: (ABT Term abt)
    => abt '[] ('HMeasure (HPair a b))
    -> [abt '[] (a ':-> 'HMeasure b)]
disintegrate m =
    disintegrateWithVar
        Text.empty
        (fst . sUnPair . sUnMeasure $ typeOf m)
        m


-- | Return the density function for a given measure. The first two
-- arguments give the hint and type of the lambda-bound variable
-- in the result. If you want to automatically fill those in, then
-- see 'density'.
--
-- TODO: is the resulting function guaranteed to be measurable? If
-- so, update this documentation to reflect that fact; if not, then
-- we should make it into a Haskell function instead.
densityWithVar
    :: (ABT Term abt)
    => Text.Text
    -> Sing a
    -> abt '[] ('HMeasure a)
    -> [abt '[] (a ':-> 'HProb)]
densityWithVar hint typ m =
    let x = Variable hint (nextFree m `max` nextBind m) typ
    in (lam_ x . E.total) <$> observe m (var x)


-- | A variant of 'densityWithVar' which automatically computes the
-- type via 'typeOf'.
density
    :: (ABT Term abt)
    => abt '[] ('HMeasure a)
    -> [abt '[] (a ':-> 'HProb)]
density m =
    densityWithVar
        Text.empty
        (sUnMeasure $ typeOf m)
        m


-- | Constrain a measure such that it must return the observed
-- value. In other words, the resulting measure returns the observed
-- value with weight according to its density in the original
-- measure, and gives all other values weight zero.
observe
    :: (ABT Term abt)
    => abt '[] ('HMeasure a)
    -> abt '[] a
    -> [abt '[] ('HMeasure a)]
observe m x =
    runDis (constrainOutcome x m >> return x) [Some2 m, Some2 x]


-- | Arbitrarily choose one of the possible alternatives. In the
-- future, this function should be replaced by a better one that
-- takes some sort of strategy for deciding which alternative to
-- choose.
determine :: (ABT Term abt) => [abt '[] a] -> Maybe (abt '[] a)
determine []    = Nothing
determine (m:_) = Just m


----------------------------------------------------------------
----------------------------------------------------------------
firstM :: Functor f => (a -> f b) -> (a,c) -> f (b,c)
firstM f (x,y) = (\z -> (z, y)) <$> f x


-- N.B., forward disintegration is not identical to partial evaluation,
-- as noted at the top of the file. For correctness we need to
-- ensure the result is emissible (i.e., has no heap-bound variables).
-- More specifically, we need to ensure emissibility in the places
-- where we call 'emitMBind'
evaluate_ :: (ABT Term abt) => TermEvaluator abt (Dis abt)
evaluate_ = evaluate perform


evaluateDatum :: (ABT Term abt) => DatumEvaluator (abt '[]) (Dis abt)
evaluateDatum e = viewWhnfDatum <$> evaluate_ e


-- | Simulate performing 'HMeasure' actions by simply emiting code
-- for those actions, returning the bound variable.
--
-- This is the function called @(|>>)@ in the disintegration paper.
perform :: forall abt. (ABT Term abt) => MeasureEvaluator abt (Dis abt)
perform = \e0 ->
    {-
    trace ("\nperform: " ++ show (pretty e0)) $
    -}
    caseVarSyn e0 performVar performTerm
    where
    performTerm :: forall a. Term abt ('HMeasure a) -> Dis abt (Whnf abt a)
    performTerm (Dirac :$ e1 :* End)       = evaluate_ e1
    performTerm (MeasureOp_ o :$ es)       = performMeasureOp o es
    performTerm (MBind :$ e1 :* e2 :* End) =
        caseBind e2 $ \x e2' ->
            push (SBind x $ Thunk e1) e2' perform
    performTerm (Superpose_ pes) = do
        -- TODO: we should combine the multiple traversals of @pes@/@pes'@
        pes' <- T.traverse (firstM (fmap fromWhnf . atomize)) pes
        emitFork_ (P.superpose . getCompose) (perform <$> Compose pes')

    -- TODO: we could optimize this by calling some @evaluateTerm@
    -- directly, rather than calling 'syn' to rebuild @e0@ from
    -- @t0@ and then calling 'evaluate_' (which will just use
    -- 'caseVarSyn' to get the @t0@ back out from the @e0@).
    performTerm t0 = performWhnf =<< evaluate_ (syn t0)


    performVar :: forall a. Variable ('HMeasure a) -> Dis abt (Whnf abt a)
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
    -- as the input, we'd need to pass it to 'perform' somehow so that
    -- it can emit the annotation when it emits 'MBind' etc. (That
    -- prolly means we shouldn't handle 'WAnn' here, but rather should
    -- handle it in the definition of 'perform' itself...)
    performWhnf
        :: forall a. Whnf abt ('HMeasure a) -> Dis abt (Whnf abt a)
    performWhnf (Head_ (WAnn typ v)) =
        ann (sUnMeasure typ) <$> performWhnf (Head_ v)
    performWhnf (Head_   v) = perform $ fromHead v
    performWhnf (Neutral e) = (Neutral . var) <$> emitMBind e


    -- TODO: right now we do the simplest thing. However, for better
    -- coverage and cleaner produced code we'll need to handle each
    -- of the ops separately. (For example, see how 'Uniform' is
    -- handled in the old code; how it has two options for what to
    -- do.)
    performMeasureOp
        :: forall typs args a
        .  (typs ~ UnLCs args, args ~ LCs typs)
        => MeasureOp typs a
        -> SArgs abt args
        -> Dis abt (Whnf abt a)
    performMeasureOp o es = do
        es' <- traverse21 atomizeCore es
        x   <- emitMBind $ syn (MeasureOp_ o :$ es')
        return (Neutral $ var x)


-- | The goal of this function is to ensure the correctness criterion
-- that given any term to be emitted, the resulting term is
-- semantically equivalent but contains no heap-bound variables.
-- That correctness criterion is necessary to ensure hygiene\/scoping.
--
-- This particular implementation calls 'evaluate' recursively,
-- giving us something similar to full-beta reduction. However,
-- that is considered an implementation detail rather than part of
-- the specification of what the function should do. Also, it's a
-- gross hack and prolly a big part of why we keep running into
-- infinite looping issues.
--
-- This name is taken from the old finally tagless code, where
-- \"atomic\" terms are (among other things) emissible; i.e., contain
-- no heap-bound variables.
--
-- BUG: this function infinitely loops in certain circumstances
-- (namely when dealing with neutral terms)
atomize :: (ABT Term abt) => TermEvaluator abt (Dis abt)
atomize e =
    {-
    trace ("\natomize: " ++ show (pretty e)) $
    -}
    traverse21 atomizeCore =<< evaluate_ e


-- | A variant of 'atomize' which is polymorphic in the locally
-- bound variables @xs@ (whereas 'atomize' requires @xs ~ '[]@).
-- We factored this out because we often want this more polymorphic
-- variant when using our indexed @TraversableMN@ classes.
atomizeCore :: (ABT Term abt) => abt xs a -> Dis abt (abt xs a)
atomizeCore e = do
    -- HACK: this check for 'disjointVarSet' is sufficient to catch
    -- the particular infinite loops we were encountering, but it
    -- will not catch all of them. If the call to 'evaluate_' in
    -- 'atomize' returns a neutral term which contains heap-bound
    -- variables, then we'll still loop forever since we don't
    -- traverse\/fmap over the top-level term constructor of neutral
    -- terms.
    xs <- getHeapVars
    if disjointVarSet xs (freeVars e)
        then return e
        else
            let (ys, e') = caseBinds e
            in  (binds_ ys . fromWhnf) <$> atomize e'
    where
    -- TODO: does @IM.null . IM.intersection@ fuse correctly?
    disjointVarSet xs ys =
        IM.null (IM.intersection (unVarSet xs) (unVarSet ys))


statementVars :: Statement abt p -> VarSet ('KProxy :: KProxy Hakaru)
statementVars (SBind x _)     = singletonVarSet x
statementVars (SLet  x _)     = singletonVarSet x
statementVars (SIndex x _ _)  = singletonVarSet x
statementVars (SWeight _)     = emptyVarSet
statementVars (SGuard xs _ _) = toVarSet1 xs

-- HACK: if we really want to go through with this approach, then
-- we should memoize the set of heap-bound variables in the
-- 'ListContext' itself rather than recomputing it every time!
getHeapVars :: Dis abt (VarSet ('KProxy :: KProxy Hakaru))
getHeapVars =
    Dis $ \c h -> c (foldMap statementVars (statements h)) h

----------------------------------------------------------------
----------------------------------------------------------------
-- | Given an emissible term @v0@ (the first argument) and another
-- term @e0@ (the second argument), compute the constraints such
-- that @e0@ must evaluate to @v0@. This is the function called
-- @(<|)@ in the disintegration paper, though notably we swap the
-- argument order so that the \"value\" is the first argument.
--
-- N.B., this function assumes (and does not verify) that the first
-- argument is emissible. So callers (including recursive calls)
-- must guarantee this invariant, by calling 'atomize' as necessary.
--
-- TODO: capture the emissibility requirement on the first argument
-- in the types, to help avoid accidentally passing the arguments
-- in the wrong order!
constrainValue :: (ABT Term abt) => abt '[] a -> abt '[] a -> Dis abt ()
constrainValue v0 e0 =
    {-
    trace (
        let s = "constrainValue"
        in "\n" ++ s ++ ": "
            ++ show (pretty v0)
            ++ "\n" ++ replicate (length s) ' ' ++ ": "
            ++ show (pretty e0)) $
    -}
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


        -- N.B., the semantically correct definition is:
        --
        -- > Literal_ v
        -- >     | "dirac v has a density wrt the ambient measure" -> ...
        -- >     | otherwise -> bot
        --
        -- For the case where the ambient measure is Lebesgue, dirac
        -- doesn't have a density, so we return 'bot'. However, we
        -- will need to generalize this when we start handling other
        -- ambient measures.
        Literal_ v               -> bot -- unsolvable. (kinda; see note)
        Datum_   d               -> bot -- unsolvable. (kinda; see note)

        Dirac :$ _ :* End        -> bot -- giving up.
        MBind :$ _ :* _ :* End   -> bot -- giving up.
        MeasureOp_ o :$ es       -> constrainValueMeasureOp v0 o es
        Superpose_ pes           -> bot -- giving up.
        Let_ :$ e1 :* e2 :* End ->
            caseBind e2 $ \x e2' ->
                push (SLet x $ Thunk e1) e2' (constrainValue v0)

        Ann_      typ :$ e1 :* End -> constrainValue  v0 e1
        CoerceTo_   c :$ e1 :* End ->
            -- TODO: we need to insert some kind of guard that says
            -- @v0@ is in the range of @coerceTo c@, or equivalently
            -- that @unsafeFrom c v0@ will always succeed. We need
            -- to emit this guard (for correctness of the generated
            -- program) because if @v0@ isn't in the range of the
            -- coercion, then there's no possible way the program
            -- @e1@ could in fact be observed at @v0@. The only
            -- question is how to perform that check; for the
            -- 'Signed' coercions it's easy enough, but for the
            -- 'Continuous' coercions it's not really clear.
            constrainValue (P.unsafeFrom_ c v0) e1
        UnsafeFrom_ c :$ e1 :* End ->
            -- TODO: to avoid returning garbage, we'd need to place
            -- some constraint on @e1@ so that if the original
            -- program would've crashed due to a bad unsafe-coercion,
            -- then we won't return a disintegrated program (since
            -- it too should always crash). Avoiding this check is
            -- sound (i.e., if the input program is well-formed
            -- then the output program is a well-formed disintegration),
            -- it just overgeneralizes.
            constrainValue  (P.coerceTo_ c v0) e1
        NaryOp_     o    es        -> constrainNaryOp v0 o es
        PrimOp_     o :$ es        -> constrainPrimOp v0 o es
        Expect  :$ e1 :* e2 :* End -> error "TODO: constrainValue{Expect}"

        Case_ e bs ->
            -- First we try going forward on the scrutinee, to make
            -- pretty resulting programs; but if that doesn't work
            -- out, we fall back to just constraining the branches.
            do  match <- matchBranches evaluateDatum e bs
                case match of
                    Nothing ->
                        -- If desired, we could return the Hakaru program
                        -- that always crashes, instead of throwing a
                        -- Haskell error.
                        error "constrainValue{Case_}: nothing matched!"
                    Just (GotStuck, _) ->
                        constrainBranches v0 e bs
                    Just (Matched ss Nil1, body) ->
                        pushes (toStatements ss) body (constrainValue v0)
            <|> constrainBranches v0 e bs

        _ :$ _ -> error "constrainValue: the impossible happened"


-- | The default way of doing 'constrainValue' on a 'Case_' expression:
-- by constraining each branch. To do this we rely on the fact that
-- we're in a 'HMeasure' context (i.e., the continuation produces
-- programs of 'HMeasure' type). For each branch we first assert the
-- branch's pattern holds (via 'SGuard') and then call 'constrainValue'
-- on the body of the branch; and the final program is the superposition
-- of all these branches.
--
-- TODO: how can we avoid duplicating the scrutinee expression?
-- Would pushing a 'SLet' statement before the superpose be sufficient
-- to achieve maximal sharing?
constrainBranches
    :: (ABT Term abt)
    => abt '[] a
    -> abt '[] b
    -> [Branch b abt a]
    -> Dis abt ()
constrainBranches v0 e = choose . map constrainBranch
    where
    constrainBranch (Branch pat body) =
        let (vars,body') = caseBinds body
        in push (SGuard vars pat (Thunk e)) body' (constrainValue v0)


----------------------------------------------------------------
-- | N.B., as with 'constrainValue', we assume that the first
-- argument is emissible. So it is the caller's responsibility to
-- ensure this (by calling 'atomize' as appropriate).
--
-- TODO: capture the emissibility requirement on the first argument
-- in the types.
constrainVariable
    :: (ABT Term abt) => abt '[] a -> Variable a -> Dis abt ()
constrainVariable v0 x =
    -- If we get 'Nothing', then it turns out @x@ is a free variable.
    -- If @x@ is a free variable, then it's a neutral term; and we
    -- return 'bot' for neutral terms
    (maybe bot return =<<) . select x $ \s ->
        case s of
        SBind y e -> do
            Refl <- varEq x y
            Just $ do
                constrainOutcome v0 (fromLazy e)
                unsafePush (SLet x $ Whnf_ (Neutral v0))
        SLet y e -> do
            Refl <- varEq x y
            Just $ do
                constrainValue v0 (fromLazy e)
                unsafePush (SLet x $ Whnf_ (Neutral v0))
        SWeight _ -> Nothing
        SGuard ys pat scrutinee ->
            error "TODO: constrainVariable{SGuard}"
        SIndex y e1 e2 -> do
            Refl <- varEq x y
            Just $ error "TODO: constrainVariable{SIndex}"


----------------------------------------------------------------
-- | N.B., as with 'constrainValue', we assume that the first
-- argument is emissible. So it is the caller's responsibility to
-- ensure this (by calling 'atomize' as appropriate).
--
-- TODO: capture the emissibility requirement on the first argument
-- in the types.
constrainValueMeasureOp
    :: forall abt typs args a
    .  (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => abt '[] ('HMeasure a)
    -> MeasureOp typs a
    -> SArgs abt args
    -> Dis abt ()
constrainValueMeasureOp v0 = go
    where
    -- TODO: for Lebesgue and Counting we use @bot@ because that's
    -- what the old finally-tagless code seems to have been doing.
    -- But is that right, or should they really be @return ()@?
    go :: MeasureOp typs a -> SArgs abt args -> Dis abt ()
    go Lebesgue    = \End               -> bot -- TODO: see note above
    go Counting    = \End               -> bot -- TODO: see note above
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
--
-- TODO: find some way to capture in the type that the first argument
-- must be emissible.
constrainNaryOp
    :: (ABT Term abt)
    => abt '[] a
    -> NaryOp a
    -> Seq (abt '[] a)
    -> Dis abt ()
constrainNaryOp v0 o =
    case o of
    Sum theSemi ->
        lubSeq $ \es1 e es2 -> do
            u <- atomize $ syn (NaryOp_ (Sum theSemi) (es1 S.>< es2))
            v <- evaluate_ $ P.unsafeMinus_ theSemi v0 (fromWhnf u)
            constrainValue (fromWhnf v) e
    Prod theSemi ->
        lubSeq $ \es1 e es2 -> do
            u <- atomize $ syn (NaryOp_ (Prod theSemi) (es1 S.>< es2))
            let u' = fromWhnf u -- TODO: emitLet?
            emitWeight $ P.recip (toProb_abs theSemi u')
            v <- evaluate_ $ P.unsafeDiv_ theSemi v0 u'
            constrainValue (fromWhnf v) e
    _ -> error $ "TODO: constrainNaryOp{" ++ show o ++ "}"


-- TODO: if this function (or the component @toProb@ and @semiringAbs@
-- parts) turn out to be useful elsewhere, then we should move it
-- to the Prelude.
toProb_abs :: (ABT Term abt) => HSemiring a -> abt '[] a -> abt '[] 'HProb
toProb_abs HSemiring_Nat  = P.nat2prob
toProb_abs HSemiring_Int  = P.nat2prob . P.abs_
toProb_abs HSemiring_Prob = id
toProb_abs HSemiring_Real = P.abs_


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
--
-- TODO: find some way to capture in the type that the first argument
-- must be emissible.
constrainPrimOp
    :: forall abt typs args a
    .  (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => abt '[] a
    -> PrimOp typs a
    -> SArgs abt args
    -> Dis abt ()
constrainPrimOp v0 = go
    where
    error_TODO op = error $ "TODO: constrainPrimOp{" ++ op ++"}"

    go :: PrimOp typs a -> SArgs abt args -> Dis abt ()
    go Not  = \(e1 :* End)       -> error_TODO "Not"
    go Impl = \(e1 :* e2 :* End) -> error_TODO "Impl"
    go Diff = \(e1 :* e2 :* End) -> error_TODO "Diff"
    go Nand = \(e1 :* e2 :* End) -> error_TODO "Nand"
    go Nor  = \(e1 :* e2 :* End) -> error_TODO "Nor"

    go Pi = \End -> bot -- because @dirac pi@ has no density wrt lebesgue

    go Sin = \(e1 :* End) -> do
        x0 <- emitLet' v0
        n  <- var <$> emitMBind P.counting
        let tau_n = P.real_ 2 P.* P.fromInt n P.* P.pi -- TODO: emitLet?
        emitGuard (P.negate P.one P.< x0 P.&& x0 P.< P.one)
        v  <- var <$> emitSuperpose
            [ P.dirac (tau_n P.+ P.asin x0)
            , P.dirac (tau_n P.+ P.pi P.- P.asin x0)
            ]
        emitWeight
            . P.recip
            . P.sqrt
            . P.unsafeProb
            $ (P.one P.- x0 P.^ P.nat_ 2)
        constrainValue v e1

    go Cos = \(e1 :* End) -> do
        x0 <- emitLet' v0
        n  <- var <$> emitMBind P.counting
        let tau_n = P.real_ 2 P.* P.fromInt n P.* P.pi
        emitGuard (P.negate P.one P.< x0 P.&& x0 P.< P.one)
        r  <- emitLet' (tau_n P.+ P.acos x0)
        v  <- var <$> emitSuperpose [P.dirac r, P.dirac (r P.+ P.pi)]
        emitWeight
            . P.recip
            . P.sqrt
            . P.unsafeProb
            $ (P.one P.- x0 P.^ P.nat_ 2)
        constrainValue v e1

    go Tan = \(e1 :* End) -> do
        x0 <- emitLet' v0
        n  <- var <$> emitMBind P.counting
        r  <- emitLet' (P.fromInt n P.* P.pi P.+ P.atan x0)
        emitWeight $ P.recip (P.one P.+ P.square x0)
        constrainValue r e1

    go Asin = \(e1 :* End) -> do
        x0 <- emitLet' v0
        emitWeight $ P.unsafeProb (P.cos x0)
        -- TODO: bounds check for -pi/2 <= v0 < pi/2
        constrainValue (P.sin x0) e1

    go Acos = \(e1 :* End) -> do
        x0 <- emitLet' v0
        emitWeight $ P.unsafeProb (P.sin x0)
        constrainValue (P.cos x0) e1

    go Atan = \(e1 :* End) -> do
        x0 <- emitLet' v0
        emitWeight $ P.recip (P.unsafeProb (P.cos x0 P.^ P.nat_ 2))
        constrainValue (P.tan x0) e1

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
            emitGuard  $ P.zero P.< u
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
            emitGuard $ P.zero P.< u
            w <- atomize $ abs (ex / (v2 * v0))
            -- or this from @pow_@:
            let w = abs (fromProb ex / (v2 * fromProb u))
            -- end.
            emitWeight $ unsafeProb w
            constrainValue ex e1
        -}
    go Exp = \(e1 :* End) -> do
        x0 <- emitLet' v0
        -- TODO: do we still want\/need the @emitGuard (0 < x0)@ which is now equivalent to @emitGuard (0 /= x0)@ thanks to the types?
        emitWeight (P.recip x0)
        constrainValue (P.log x0) e1

    go Log = \(e1 :* End) -> do
        exp_x0 <- emitLet' (P.exp v0)
        emitWeight exp_x0
        constrainValue exp_x0 e1

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
        let negate_v0 = syn (PrimOp_ (Negate theRing) :$ v0 :* End)
                -- case v0 of
                -- Neutral e ->
                --     Neutral $ syn (PrimOp_ (Negate theRing) :$ e :* End)
                -- Head_ v ->
                --     case theRing of
                --     HRing_Int  -> Head_ . reflect . negate $ reify v
                --     HRing_Real -> Head_ . reflect . negate $ reify v
        in constrainValue negate_v0 e1

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

        x0 <- emitLet' (P.coerceTo_ signed v0)
        v  <- var <$> emitMBind
            (P.if_ (lt zero x0)
                (P.superpose
                    [ (P.one, P.dirac x0)
                    , (P.one, P.dirac (neg x0))
                    ])
                (P.if_ (eq zero x0)
                    (P.dirac zero)
                    P.reject))
        constrainValue v e1

    go (Signum theRing) = \(e1 :* End) ->
        case theRing of
        HRing_Real -> bot
        HRing_Int  -> do
            x <- var <$> emitMBind P.counting
            emitGuard $ P.signum x P.== v0
            constrainValue x e1

    go (Recip theFractional) = \(e1 :* End) -> do
        x0 <- emitLet' v0
        emitWeight
            . P.recip
            . P.unsafeProbFraction_ theFractional
            -- TODO: define a dictionary-passing variant of 'P.square' instead, to include the coercion in there explicitly...
            $ square (hSemiring_HFractional theFractional) x0
        constrainValue (P.primOp1_ (Recip theFractional) x0) e1

    go (NatRoot theRadical) = \(e1 :* e2 :* End) ->
        case theRadical of
        HRadical_Prob -> do
            x0 <- emitLet' v0
            u2 <- fromWhnf <$> atomize e2
            emitWeight (P.nat2prob u2 P.* x0)
            constrainValue (x0 P.^ u2) e1

    go (Erf theContinuous) = \(e1 :* End) ->
        error "TODO: constrainPrimOp: need InvErf to disintegrate Erf"


-- HACK: can't use @(P.^)@ because Haskell can't figure out our polymorphism
square :: (ABT Term abt) => HSemiring a -> abt '[] a -> abt '[] a
square theSemiring e =
    syn (PrimOp_ (NatPow theSemiring) :$ e :* P.nat_ 2 :* End)


----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: do we really want the first argument to be a term at all,
-- or do we want something more general like patters for capturing
-- measurable events?
--
-- | This is a helper function for 'constrainValue' to handle 'SBind'
-- statements (just as the 'perform' argument to 'evaluate' is a
-- helper for handling 'SBind' statements).
--
-- N.B., We assume that the first argument, @v0@, is already
-- atomized. So, this must be ensured before recursing, but we can
-- assume it's already been done by the IH. Technically, we con't
-- care whether the first argument is in normal form or not, just
-- so long as it doesn't contain any heap-bound variables.
--
-- This is the function called @(<<|)@ in the paper, though notably
-- we swap the argument order.
--
-- TODO: find some way to capture in the type that the first argument
-- must be emissible, to help avoid accidentally passing the arguments
-- in the wrong order!
--
-- TODO: under what circumstances is @constrainOutcome x m@ different
-- from @constrainValue x =<< perform m@? If they're always the
-- same, then we should just use that as the definition in order
-- to avoid repeating ourselves
constrainOutcome
    :: forall abt a
    .  (ABT Term abt)
    => abt '[] a
    -> abt '[] ('HMeasure a)
    -> Dis abt ()
constrainOutcome v0 e0 =
    {-
    trace (
        let s = "constrainOutcome"
        in "\n" ++ s ++ ": "
            ++ show (pretty v0)
            ++ "\n" ++ replicate (length s) ' ' ++ ": "
            ++ show (pretty e0)) $ -} do
    w0 <- evaluate_ e0
    case w0 of
        Neutral _ -> bot
        Head_   v -> go v
    where
    impossible = error "constrainOutcome: the impossible happened"

    go :: Head abt ('HMeasure a) -> Dis abt ()
    go (WLiteral _)          = impossible
    -- go (WDatum _)         = impossible
    -- go (WEmpty _)         = impossible
    -- go (WArray _ _)       = impossible
    -- go (WLam _)           = impossible
    -- go (WIntegrate _ _ _) = impossible
    -- go (WSummate   _ _ _) = impossible
    go (WAnn        _ e1)    = go e1 -- TODO: reinsert the annotation?
    go (WCoerceTo   _ _)     = impossible
    go (WUnsafeFrom _ _)     = impossible
    go (WMeasureOp o es)     = constrainOutcomeMeasureOp v0 o es
    go (WDirac e1)           = constrainValue v0 e1
    go (WMBind e1 e2)        =
        caseBind e2 $ \x e2' ->
            push (SBind x $ Thunk e1) e2' (constrainOutcome v0)
    go (WSuperpose pes) =
        case pes of
        [(p,e)] -> do
            p' <- fromWhnf <$> atomize p
            emitWeight p'
            constrainOutcome v0 e
        _ -> do
            -- TODO: we should combine the multiple traversals of @pes@/@pes'@
            pes' <- T.traverse (firstM (fmap fromWhnf . atomize)) pes
            emitFork_ (P.superpose . getCompose)
                (constrainOutcome v0 <$> Compose pes')


-- TODO: should this really be different from 'constrainValueMeasureOp'?
--
-- TODO: find some way to capture in the type that the first argument
-- must be emissible.
constrainOutcomeMeasureOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => abt '[] a
    -> MeasureOp typs a
    -> SArgs abt args
    -> Dis abt ()
constrainOutcomeMeasureOp v0 = go
    where
    -- Per the paper
    go Lebesgue = \End -> return ()

    -- TODO: I think, based on Hakaru v0.2.0
    go Counting = \End -> return ()

    go Categorical = \(e1 :* End) ->
        error "TODO: constrainOutcomeMeasureOp{Categorical}"

    -- Per the paper
    go Uniform = \(lo :* hi :* End) -> do
        v0' <- emitLet' v0
        lo' <- (emitLet' . fromWhnf) =<< atomize lo
        hi' <- (emitLet' . fromWhnf) =<< atomize hi
        emitGuard (lo' P.<= v0' P.&& v0' P.<= hi')
        emitWeight  (P.recip (P.unsafeProb (hi' P.- lo')))

    -- TODO: Add fallback handling of Normal that does not atomize mu,sd.
    -- This fallback is as if Normal were defined in terms of Lebesgue
    -- and a density Weight.  This fallback is present in Hakaru v0.2.0
    -- in order to disintegrate a program such as
    --  x <~ normal(0,1)
    --  y <~ normal(x,1)
    --  return ((x+(y+y),x)::pair(real,real))
    go Normal = \(mu :* sd :* End) -> do
        -- N.B., if\/when extending this to higher dimensions, the real equation is @recip (sqrt (2*pi*sd^2) ^ n) * exp (negate (norm_n (v0 - mu) ^ 2) / (2*sd^2))@ for @Real^n@.
        mu' <- fromWhnf <$> atomize mu
        sd' <- (emitLet' . fromWhnf) =<< atomize sd
        emitWeight
            (P.exp (P.negate ((v0 P.- mu') P.^ P.nat_ 2)
                    P./ P.fromProb (P.prob_ 2 P.* sd' P.^ P.nat_ 2))
                P./ sd'
                P./ P.sqrt (P.prob_ 2 P.* P.pi))

    go Poisson = \(e1 :* End) ->
        error "TODO: constrainOutcomeMeasureOp{Poisson}"
    go Gamma = \(e1 :* e2 :* End) ->
        error "TODO: constrainOutcomeMeasureOp{Gamma}"
    go Beta = \(e1 :* e2 :* End) ->
        error "TODO: constrainOutcomeMeasureOp{Beta}"
    go (DirichletProcess _) = \(e1 :* e2 :* End) ->
        error "TODO: constrainOutcomeMeasureOp{DirichletProcess}"
    go (Plate _) = \(e1 :* End) ->
        error "TODO: constrainOutcomeMeasureOp{Plate}"
    go (Chain _ _) = \(e1 :* e2 :* End) ->
        error "TODO: constrainOutcomeMeasureOp{Chain}"

----------------------------------------------------------------
----------------------------------------------------------- fin.
