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
--                                                    2016.05.24
-- |
-- Module      :  Language.Hakaru.Evaluation.DisintegrationMonad
-- Copyright   :  Copyright (c) 2016 the Hakaru team
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
      getStatements
    , ListContext(..), Ans, Dis(..), runDis
    -- ** TODO: IntMap-based version
    
    -- * Operators on the disintegration monad
    -- ** The \"zero\" and \"one\"
    , bot
    --, reject
    -- ** Emitting code
    , emit
    , emitMBind
    , emitLet
    , emitLet'
    , emitUnpair
    -- TODO: emitUneither
    -- emitCaseWith
    , emit_
    , emitMBind_
    , emitGuard
    , emitWeight
    , emitFork_
    , emitSuperpose
    , choose
    -- * Overrides for original in Evaluation.Types
    , pushPlate
    -- * For Arrays/Plate
    , getIndices
    , extendIndices
    , statementInds
    -- * Locs
    , Loc(..)
    , getLocs
    , putLocs
    , insertLoc
    , adjustLoc
    ) where

import           Prelude              hiding (id, (.))
import           Control.Category     (Category(..))
#if __GLASGOW_HASKELL__ < 710
import           Data.Monoid          (Monoid(..))
import           Data.Functor         ((<$>))
import           Control.Applicative  (Applicative(..))
#endif
import           Data.Maybe
import qualified Data.Foldable        as F
import qualified Data.Traversable     as T
import           Data.List.NonEmpty   (NonEmpty(..))
import qualified Data.List.NonEmpty   as NE
import           Control.Applicative  (Alternative(..))
import           Control.Monad        (MonadPlus(..))
import           Data.Text            (Text)
import qualified Data.Text            as Text

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing    (Sing(..), sUnMeasure, sUnPair)
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.DatumABT
import Language.Hakaru.Syntax.TypeOf
import Language.Hakaru.Syntax.ABT
import qualified Language.Hakaru.Syntax.Prelude as P
import Language.Hakaru.Evaluation.Types
import Language.Hakaru.Evaluation.PEvalMonad (ListContext(..))
import Language.Hakaru.Evaluation.Lazy (reifyPair)

#ifdef __TRACE_DISINTEGRATE__
import Debug.Trace (trace)
#endif

getStatements :: Dis abt [Statement abt 'Impure]
getStatements = Dis $ \c h -> c (statements h) h

----------------------------------------------------------------
----------------------------------------------------------------
-- | Plug a term into a context. That is, the 'statements' of the
-- context specifies a program with a hole in it; so we plug the
-- given term into that hole, returning the complete program.
residualizeListContext
    :: forall abt a
    .  (ABT Term abt)
    => ListContext abt 'Impure
    -> abt '[] ('HMeasure a)
    -> abt '[] ('HMeasure a)
residualizeListContext =
    -- N.B., we use a left fold because the head of the list of
    -- statements is the one closest to the hole.
    \ss e0 -> foldl step e0 (statements ss)
    where
    step
        :: abt '[] ('HMeasure a)
        -> Statement abt 'Impure
        -> abt '[] ('HMeasure a)
    step e s =
        case s of
        SBind x body _ ->
            -- TODO: if @body@ is dirac, then treat as 'SLet'
            syn (MBind :$ fromLazy body :* bind x e :* End)
        SLet x body _
            | not (x `memberVarSet` freeVars e) -> e
            -- TODO: if used exactly once in @e@, then inline.
            | otherwise ->
                case getLazyVariable body of
                Just y  -> subst x (var y) e
                Nothing ->
                    case getLazyLiteral body of
                    Just v  -> subst x (syn $ Literal_ v) e
                    Nothing ->
                        syn (Let_ :$ fromLazy body :* bind x e :* End)
        SGuard xs pat scrutinee _ ->
            syn $ Case_ (fromLazy scrutinee)
                [ Branch pat   (binds_ xs e)
                , Branch PWild (P.reject $ typeOf e)
                ]
        SWeight body _ -> syn $ Superpose_ ((fromLazy body, e) :| [])

----------------------------------------------------------------
-- A location is a variable *use* instantiated at some list of indices.
data Loc :: (Hakaru -> *) -> Hakaru -> * where
     Loc
         :: Variable a
         -> [Index ast]
         -> Loc ast a
     MultiLoc
         :: Variable a
         -> [Index ast]
         -> Loc ast ('HArray a)


-- In the paper we say that result must be a 'Whnf'; however, in
-- the paper it's also always @HMeasure a@ and everything of that
-- type is a WHNF (via 'WMeasure') so that's a trivial statement
-- to make. If we turn it back into some sort of normal form, then
-- it must be one preserved by 'residualizeContext'.
--
-- Also, we add the list in order to support "lub" without it living in the AST.
-- TODO: really we should use LogicT...
type Ans abt a
  =  ListContext abt 'Impure
  -> [Index (abt '[])]
  -> Assocs (Loc (abt '[]))
  -> [abt '[] ('HMeasure a)]


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
newtype Dis abt x =
    Dis { unDis :: forall a. (x -> Ans abt a) -> Ans abt a }
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
runDis (Dis m) es =
    m c0 (ListContext i0 []) [] emptyAssocs
    where
    -- TODO: we only use dirac because 'residualizeListContext' requires it to already be a measure; unfortunately this can result in an extraneous @(>>= \x -> dirac x)@ redex at the end of the program. In principle, we should be able to eliminate that redex by changing the type of 'residualizeListContext'...
    c0 e ss _ _ = [residualizeListContext ss (syn(Dirac :$ e :* End))]

    i0 = maxNextFree es

extendIndices
    :: (ABT Term abt)
    => Index (abt '[])
    -> [Index (abt '[])]
    -> [Index (abt '[])]
-- TODO: check all Indices are unique
extendIndices = (:)

-- give better name
statementInds :: Statement abt p -> [Index (abt '[])]
statementInds (SBind   _ _   i) = i
statementInds (SLet    _ _   i) = i
statementInds (SWeight _     i) = i
statementInds (SGuard  _ _ _ i) = i
statementInds (SStuff0 _     i) = i
statementInds (SStuff1 _ _   i) = i

getLocs :: (ABT Term abt)
        => Dis abt (Assocs (Loc (abt '[])))
getLocs = Dis $ \c h i l -> c l h i l

putLocs :: (ABT Term abt)
        => Assocs (Loc (abt '[]))
        -> Dis abt ()
putLocs l = Dis $ \c h i _ -> c () h i l

insertLoc :: (ABT Term abt)
          => Variable a
          -> Loc (abt '[]) a
          -> Dis abt ()
insertLoc v loc = 
  Dis $ \c h i l -> c () h i $
    insertAssoc (Assoc v loc) l

adjustLoc :: (ABT Term abt)
          => Variable (a :: Hakaru)
          -> (Assoc (Loc (abt '[])) -> Assoc (Loc (abt '[])))
          -> Dis abt ()
adjustLoc x f = do
    locs <- getLocs
    putLocs $ adjustAssoc x f locs

mkLoc
    :: (ABT Term abt)
    => Text
    -> Variable (a :: Hakaru)
    -> [Index (abt '[])]
    -> Dis abt (Variable a)
mkLoc hint s inds = do
  x <- freshVar hint (varType s)
  insertLoc x (Loc s inds)
  return x

mkLocs
    :: (ABT Term abt)
    => List1 Variable (xs :: [Hakaru])
    -> [Index (abt '[])]
    -> Dis abt (List1 Variable xs)
mkLocs Nil1         _    = return Nil1
mkLocs (Cons1 x xs) inds = Cons1
                           <$> mkLoc Text.empty x inds
                           <*> mkLocs xs inds

mkMultiLoc
    :: (ABT Term abt)
    => Text
    -> Variable a
    -> [Index (abt '[])]
    -> Dis abt (Variable ('HArray a))
mkMultiLoc hint s inds = do
  locs <- getLocs
  x' <- freshVar hint (SArray $ varType s)
  insertLoc x' (MultiLoc s inds)
  return x'

instance Functor (Dis abt) where
    fmap f (Dis m)  = Dis $ \c -> m (c . f)

instance Applicative (Dis abt) where
    pure x            = Dis $ \c -> c x
    Dis mf <*> Dis mx = Dis $ \c -> mf $ \f -> mx $ \x -> c (f x)

instance Monad (Dis abt) where
    return      = pure
    Dis m >>= k = Dis $ \c -> m $ \x -> unDis (k x) c

instance Alternative (Dis abt) where
    empty           = Dis $ \_ _ _ _ -> []
    Dis m <|> Dis n = Dis $ \c h i l -> m c h i l ++ n c h i l

instance MonadPlus (Dis abt) where
    mzero = empty -- aka "bot"
    mplus = (<|>) -- aka "lub"

instance (ABT Term abt) => EvaluationMonad abt (Dis abt) 'Impure where
    freshNat =
        Dis $ \c (ListContext i ss) ->
            c i (ListContext (i+1) ss)

    freshenStatement s =
        case s of
          SWeight _ _    -> return (s, mempty)
          SBind x body i -> do
               s  <- freshenVar x
               x' <- mkLoc (varHint x) s i
               return (SBind x' body i, singletonAssocs x x')
          SLet  x body i -> do
               s  <- freshenVar x
               x' <- mkLoc (varHint x) s i
               return (SLet x' body i, singletonAssocs x x')
          SGuard xs pat scrutinee i -> do
               ss  <- freshenVars xs
               xs' <- mkLocs ss i
               return (SGuard xs' pat scrutinee i, toAssocs1 xs xs')

    getIndices =  Dis $ \c h i l -> c i h i l

    unsafePush s =
        Dis $ \c (ListContext i ss) ->
            c () (ListContext i (s:ss))

    -- N.B., the use of 'reverse' is necessary so that the order
    -- of pushing matches that of 'pushes'
    unsafePushes ss =
        Dis $ \c (ListContext i ss') ->
            c () (ListContext i (reverse ss ++ ss'))

    select x p = loop []
        {-  -- The following causes snippet causes programs
            -- which bot to instead infinite loop

        do locs <- getLocs
           let mx = lookupAssoc x locs
           case mx of
             Just (Loc is) -> loop [] 
             Nothing       -> return Nothing
        -}
        where
        -- TODO: use a DList to avoid reversing inside 'unsafePushes'
        loop ss = do
            ms <- unsafePop
            case ms of
                Nothing      -> do
                    unsafePushes ss
                    return Nothing
                Just s ->
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
unsafePop :: Dis abt (Maybe (Statement abt 'Impure))
unsafePop =
    Dis $ \c h@(ListContext i ss) ind loc ->
        case ss of
        []    -> c Nothing  h ind loc
        s:ss' -> c (Just s) (ListContext i ss') ind loc

pushPlate
    :: (ABT Term abt)
    => abt '[] 'HNat
    -> abt '[ 'HNat ] ('HMeasure a)
    -> [Index (abt '[])]
    -> Dis abt (Variable ('HArray a))
pushPlate n e inds =
  caseBind e $ \x body -> do
    i  <- freshInd n
    p  <- freshVar Text.empty (sUnMeasure $ typeOf body)
    unsafePush (SBind p (Thunk $ rename x (indVar i) body)
                (extendIndices i inds))
    mkMultiLoc Text.empty p inds

----------------------------------------------------------------
----------------------------------------------------------------

-- | It is impossible to satisfy the constraints, or at least we
-- give up on trying to do so. This function is identical to 'empty'
-- and 'mzero' for 'Dis'; we just give it its own name since this is
-- the name used in our papers.
--
-- TODO: add some sort of trace information so we can get a better
-- idea what caused a disintegration to fail.
bot :: (ABT Term abt) => Dis abt a
bot = Dis $ \_ _ _ _ -> []


-- | The empty measure is a solution to the constraints.
-- reject :: (ABT Term abt) => Dis abt a
-- reject = Dis $ \_ _ -> [syn (Superpose_ [])]


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
    Dis $ \c h i l -> (f . bind x) <$> c x h i l


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
emitUnpair (Head_   w) = return $ reifyPair w
emitUnpair (Neutral e) = do
    let (a,b) = sUnPair (typeOf e)
    x <- freshVar Text.empty a
    y <- freshVar Text.empty b
    emitUnpair_ x y e

emitUnpair_
    :: forall abt a b
    .  (ABT Term abt)
    => Variable a
    -> Variable b
    -> abt '[] (HPair a b)
    -> Dis abt (abt '[] a, abt '[] b)
emitUnpair_ x y = loop
    where
    done :: abt '[] (HPair a b) -> Dis abt (abt '[] a, abt '[] b)
    done e =
#ifdef __TRACE_DISINTEGRATE__
        trace "-- emitUnpair: done (term is not Datum_ nor Case_)" $
#endif
        Dis $ \c h i l ->
            ( syn
            . Case_ e
            . (:[])
            . Branch (pPair PVar PVar)
            . bind x
            . bind y
            ) <$> c (var x, var y) h i l

    loop :: abt '[] (HPair a b) -> Dis abt (abt '[] a, abt '[] b)
    loop e0 =
        caseVarSyn e0 (done . var) $ \t ->
            case t of
            Datum_ d   -> do
#ifdef __TRACE_DISINTEGRATE__
                trace "-- emitUnpair: found Datum_" $ return ()
#endif
                return $ reifyPair (WDatum d)
            Case_ e bs -> do
#ifdef __TRACE_DISINTEGRATE__
                trace "-- emitUnpair: going under Case_" $ return ()
#endif
                -- TODO: we want this to duplicate the current
                -- continuation for (the evaluation of @loop@ in)
                -- all branches. So far our traces all end up
                -- returning @bot@ on the first branch, and hence
                -- @bot@ for the whole case-expression, so we can't
                -- quite tell whether it does what is intended.
                --
                -- N.B., the only 'Dis'-effects in 'applyBranch'
                -- are to freshen variables; thus this use of
                -- 'traverse' is perfectly sound.
                emitCaseWith loop e bs
            _ -> done e0


-- TODO: emitUneither


-- This function was called @insert_@ in the old finally-tagless code.
-- | Emit some code that doesn't bind any variables. This function
-- provides an optimisation over using 'emit' and then discarding
-- the generated variable.
emit_
    :: (ABT Term abt)
    => (forall r. abt '[] ('HMeasure r) -> abt '[] ('HMeasure r))
    -> Dis abt ()
emit_ f = Dis $ \c h i l -> f <$> c () h i l


-- | Emit an 'MBind' that discards its result (i.e., \"@m >>@\").
-- We restrict the type of the argument to be 'HUnit' so as to avoid
-- accidentally dropping things.
emitMBind_ :: (ABT Term abt) => abt '[] ('HMeasure HUnit) -> Dis abt ()
emitMBind_ m = emit_ (m P.>>)


-- TODO: if the argument is a value, then we can evaluate the 'P.if_' immediately rather than emitting it.
-- | Emit an assertion that the condition is true.
emitGuard :: (ABT Term abt) => abt '[] HBool -> Dis abt ()
emitGuard b = emit_ (P.withGuard b) -- == emit_ $ \m -> P.if_ b m P.reject

-- TODO: if the argument is the literal 1, then we can avoid emitting anything.
emitWeight :: (ABT Term abt) => abt '[] 'HProb -> Dis abt ()
emitWeight w = emit_ (P.withWeight w)


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
emitFork_ f ms = Dis $ \c h i l -> f <$> T.traverse (\m -> unDis m c h i l) ms


-- | Emit a 'Superpose_' of the alternatives, each with unit weight.
emitSuperpose
    :: (ABT Term abt)
    => [abt '[] ('HMeasure a)]
    -> Dis abt (Variable a)
emitSuperpose []  = error "TODO: emitSuperpose[]"
emitSuperpose [e] = emitMBind e
emitSuperpose es  =
    emitMBind . P.superpose . NE.map ((,) P.one) $ NE.fromList es


-- | Emit a 'Superpose_' of the alternatives, each with unit weight.
choose :: (ABT Term abt) => [Dis abt a] -> Dis abt a
choose []  = error "TODO: choose[]"
choose [m] = m
choose ms  = emitFork_ (P.superpose . NE.map ((,) P.one) . NE.fromList) ms


-- | Given some function we can call on the bodies of the branches,
-- freshen all the pattern-bound variables and then run the function
-- on all the branches in parallel (i.e., with the same continuation
-- and heap) and then emit a case-analysis expression with the
-- results of the continuations as the bodies of the branches. This
-- function is useful for when we really do want to emit a 'Case_'
-- expression, rather than doing the superpose of guard patterns
-- thing that 'constrainValue' does.
--
-- N.B., this function assumes (and does not verify) that the second
-- argument is emissible. So callers must guarantee this invariant,
-- by calling 'atomize' as necessary.
--
-- TODO: capture the emissibility requirement on the second argument
-- in the types.
emitCaseWith
    :: (ABT Term abt)
    => (abt '[] b -> Dis abt r)
    -> abt '[] a
    -> [Branch a abt b]
    -> Dis abt r
emitCaseWith f e bs = do
    gms <- T.for bs $ \(Branch pat body) ->
        let (vars, body') = caseBinds body
        in  (\vars' ->
                let rho = toAssocs1 vars (fmap11 var vars')
                in  GBranch pat vars' (f $ substs rho body')
            ) <$> freshenVars vars
    Dis $ \c h i l ->
        (syn . Case_ e) <$> T.for gms (\gm ->
            fromGBranch <$> T.for gm (\m ->
                unDis m c h i l))
{-# INLINE emitCaseWith #-}


----------------------------------------------------------------
----------------------------------------------------------- fin.
