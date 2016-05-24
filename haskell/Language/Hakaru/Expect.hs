{-# LANGUAGE CPP
           , GADTs
           , EmptyCase
           , KindSignatures
           , DataKinds
           , TypeOperators
           , NoImplicitPrelude
           , ScopedTypeVariables
           , FlexibleContexts
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.04.28
-- |
-- Module      :  Language.Hakaru.Expect
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
--
----------------------------------------------------------------
module Language.Hakaru.Expect
    ( normalize
    , total
    , expect
    ) where

import           Prelude               (($), (.), error, return, reverse, mapM)
import qualified Data.Text             as Text
import           Data.Functor          ((<$>))
import qualified Data.Foldable         as F
import qualified Data.Traversable      as T
import qualified Data.List.NonEmpty    as NE
import           Control.Monad

import Language.Hakaru.Syntax.IClasses (Some2(..), List1(..), Functor11(..))
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST               hiding (Expect)
import Language.Hakaru.Syntax.Datum
import qualified Language.Hakaru.Syntax.AST     as AST
import Language.Hakaru.Syntax.TypeOf            (typeOf)
import qualified Language.Hakaru.Syntax.Prelude as P
import Language.Hakaru.Evaluation.Types
import Language.Hakaru.Evaluation.ExpectMonad

#ifdef __TRACE_DISINTEGRATE__
import Prelude                          (show, (++))
import qualified Text.PrettyPrint       as PP
import Language.Hakaru.Pretty.Haskell   (pretty)
import Language.Hakaru.Evaluation.Types (ppStatement)
import Debug.Trace                      (trace)
#endif

----------------------------------------------------------------

-- | Convert an arbitrary measure into a probability measure; i.e.,
-- reweight things so that the total weight\/mass is 1.
normalize
    :: (ABT Term abt) => abt '[] ('HMeasure a) -> abt '[] ('HMeasure a)
normalize m = P.withWeight (P.recip $ total m) m


-- | Compute the total weight\/mass of a measure.
total :: (ABT Term abt) => abt '[] ('HMeasure a) -> abt '[] 'HProb
total m =
    expect m . binder Text.empty (sUnMeasure $ typeOf m) $ \_ -> P.one

-- TODO: is it actually a _measurable_ function from measurable-functions
-- to probs? If so, shouldn't we also capture that in the types?
--
-- | Convert a measure into its integrator. N.B., the second argument
-- is (a representation of) a measurable function from @a@ to
-- 'HProb@. We represent it as a binding form rather than as @abt
-- '[] (a ':-> 'HProb)@ in order to avoid introducing administrative
-- redexes. We could, instead, have used a Haskell function @abt
-- '[] a -> abt '[] 'HProb@ to eliminate the administrative redexes,
-- but that would introduce other implementation difficulties we'd
-- rather avoid.
expect
    :: (ABT Term abt)
    => abt '[] ('HMeasure a)
    -> abt '[a] 'HProb
    -> abt '[] 'HProb
expect e f = runExpect (expectTerm e) f [Some2 e, Some2 f]


residualizeExpect
    :: (ABT Term abt)
    => abt '[] ('HMeasure a)
    -> Expect abt (abt '[] a)
residualizeExpect e = do
    -- BUG: is this what we really mean? or do we actually mean the old 'emit' version?
    x <- freshVar Text.empty (sUnMeasure $ typeOf e)
    unsafePush (SStuff1 x (\c ->
        syn (AST.Expect :$ e :* bind x c :* End)) Nil1)
    return $ var x
{-
residualizeExpect e = do
    var <$> emit Text.empty (sUnMeasure $ typeOf e)
        (\c -> syn (AST.Expect :$ e :* c :* End))
-}

-- This version checks whether the first argument is a variable or not, avoiding the extraneous let binding as appropriate. We also avoid using 'binder', which is good because it constructs the term more directly, but is bad because we make no guarantees about hygiene! We expect callers to handle that.
-- TODO: move this elsewhere, so that 'runExpect' can use it.
-- TODO: make even smarter so that we drop the let binding in case @f@ doesn't actually use it?
let_ :: (ABT Term abt) => abt '[] a -> abt '[a] b -> abt '[] b
let_ e f =
    caseVarSyn e
        (\x -> caseBind f $ \y f' -> subst y (var x) f')
        (\_ -> syn (Let_ :$ e :* f :* End))


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

{-
toGBranch
    :: (ABT Term abt)
    => Branch a abt b
    -> GBranch a (abt '[] b)
toGBranch (Branch pat body) =
    uncurry (GBranch pat) (caseBinds body)
-}

instance Functor (GBranch a) where
    fmap f (GBranch pat vars x) = GBranch pat vars (f x)

instance F.Foldable (GBranch a) where
    foldMap f (GBranch _ _ x) = f x

instance T.Traversable (GBranch a) where
    traverse f (GBranch pat vars x) = GBranch pat vars <$> f x

    
expectCase
    :: (ABT Term abt)
    => abt '[] a
    -> [Branch a abt ('HMeasure b)]
    -> Expect abt (abt '[] b)
expectCase scrutinee bs = do
    -- Get the current context and then clear it.
    ctx <- Expect $ \c h -> c h (h {statements = []})
    -- Emit the old "current" context.
    Expect $ \c h -> residualizeExpectListContext (c () h) ctx
    -- @emitCaseWith@
    gms <- T.for bs $ \(Branch pat body) ->
        let (vars, body') = caseBinds body
        in  (\vars' ->
                let rho = toAssocs1 vars (fmap11 var vars')
                in  GBranch pat vars' (expectTerm $ substs rho body')
            ) <$> freshenVars vars
    Expect $ \c h ->
        syn $ Case_ scrutinee
            [ fromGBranch $ fmap (\m -> unExpect m c h) gm
            | gm <- gms
            ]

----------------------------------------------------------------
-- BUG: really rather than using 'pureEvaluate' itself, we should
-- have our own similar version which pushes the @expect _ c@ under
-- the branches; in lieu of allowing 'defaultCaseEvaluator' to
-- return a 'Neutral' term. How can we get this to work right? Seems
-- like a common problem to have since the backwards disintegrator(s)
-- have to do it too.


-- N.B., in the ICFP 2015 pearl paper, we took the expectation of
-- bound variables prior to taking the expectation of their scope.
-- E.g., @expect(let_ v e1 e2) xs c = expect e1 xs $ \x -> expect
-- e2 (insertAssoc v x xs) c@. Whereas here, I'm being lazier and
-- performing the expectation on variable lookup. This delayed
-- evaluation preserves the expectation semantics (ICFP 2015, §5.6.0)
-- whenever (1) the variable is never used (by wasted computation),
-- or (2) used exactly once (by Tonelli's theorem); so we only need
-- to worry if (3) the variable is used more than once, in which
-- case we'll have to worry about whether the various integrals
-- commute/exchange with one another. More generally, cf. Bhat et
-- al.'s \"active variables\"

-- TODO: do we want to move this to the public API of
-- "Language.Hakaru.Evaluation.DisintegrationMonad"?
#ifdef __TRACE_DISINTEGRATE__
getStatements :: Expect abt [Statement abt 'ExpectP]
getStatements = Expect $ \c h -> c (statements h) h
#endif


expectTerm
    :: (ABT Term abt)
    => abt '[] ('HMeasure a)
    -> Expect abt (abt '[] a)
expectTerm e = do
#ifdef __TRACE_DISINTEGRATE__
    ss <- getStatements
    trace ("\n-- expectTerm --\n"
        ++ show (pretty_Statements_withTerm ss e)
        ++ "\n") $ return ()
#endif
    w <- pureEvaluate e
    case w of
        -- TODO: if the neutral term is a 'Case_' then we want to go under it
        Neutral e'              ->
            caseVarSyn e' (residualizeExpect . var) $ \t ->
                case t of
                Case_ e1 bs -> expectCase e1 bs
                _           -> residualizeExpect e'
        Head_ (WLiteral    _)   -> error "expect: the impossible happened"
        Head_ (WCoerceTo   _ _) -> error "expect: the impossible happened"
        Head_ (WUnsafeFrom _ _) -> error "expect: the impossible happened"
        Head_ (WMeasureOp o es) -> expectMeasureOp o es
        Head_ (WDirac e1)       -> return e1
        Head_ (WMBind e1 e2)    -> do
            v1 <- expectTerm e1
            expectTerm (let_ v1 e2)
        Head_ (WPlate _ _)     -> error "TODO: expect{Plate}"
        Head_ (WChain _ _ _)   -> error "TODO: expect{Chain}"
        Head_ (WReject    _)   -> expectSuperpose []
        Head_ (WSuperpose pes) -> expectSuperpose (NE.toList pes)


-- N.B., we guarantee that each @e@ is called with the same heap
-- @h@ and continuation @c@.
expectSuperpose
    :: (ABT Term abt)
    => [(abt '[] 'HProb, abt '[] ('HMeasure a))]
    -> Expect abt (abt '[] a)
expectSuperpose pes = do
#ifdef __TRACE_DISINTEGRATE__
    ss <- getStatements
    trace ("\n-- expectSuperpose --\n"
        ++ show (pretty_Statements_withTerm ss (syn $ Superpose_ pes))
        ++ "\n") $ return ()
#endif
    -- First, emit the current heap (so that each @p@ is emissible)
    emitExpectListContext
    -- Then emit the 'sum', and call the same continuation on each @e@
    Expect $ \c h ->
        P.sum [ p P.* unExpect (expectTerm e) c h | (p,e) <- pes]
    -- TODO: if @pes@ is null, then automatically simplify to just 0
    -- TODO: in the Lazy.tex paper, we guard against that interpretation being negative...

emitExpectListContext :: forall abt. (ABT Term abt) => Expect abt ()
emitExpectListContext = do
    ss <- Expect $ \c h -> c (statements h) (h {statements = []})
    F.traverse_ step (reverse ss) -- TODO: use composition tricks to avoid reversing @ss@
    where
    step :: Statement abt 'ExpectP -> Expect abt ()
    step s =
#ifdef __TRACE_DISINTEGRATE__
        trace ("\n-- emitExpectListContext: " ++ show (ppStatement 0 s)) $
#endif
        case s of
        SLet x body _ ->
            -- TODO: be smart about dropping unused let-bindings and inlining trivial let-bindings
            Expect $ \c h ->
                syn (Let_ :$ fromLazy body :* bind x (c () h) :* End)
        SStuff0   f _ -> Expect $ \c h -> f (c () h)
        SStuff1 _ f _ -> Expect $ \c h -> f (c () h)


pushIntegrate
    :: (ABT Term abt)
    => abt '[] 'HReal
    -> abt '[] 'HReal
    -> Expect abt (Variable 'HReal)
pushIntegrate lo hi = do
    x <- freshVar Text.empty SReal
    unsafePush (SStuff1 x (\c ->
        syn (Integrate :$ lo :* hi :* bind x c :* End)) Nil1)
    return x
{-
-- BUG: we assume the arguments are emissible!
emitIntegrate lo hi =
    emit Text.empty SReal (\c ->
        syn (Integrate :$ lo :* hi :* c :* End))
-}

pushSummate
    :: (ABT Term abt)
    => abt '[] 'HReal
    -> abt '[] 'HReal
    -> Expect abt (Variable 'HInt)
pushSummate lo hi = do
    x <- freshVar Text.empty SInt
    unsafePush (SStuff1 x (\c ->
        syn (Summate :$ lo :* hi :* bind x c :* End)) Nil1)
    return x
{-
-- BUG: we assume the arguments are emissible!
emitSummate lo hi =
    emit Text.empty SInt (\c ->
        syn (Summate :$ lo :* hi :* c :* End))
-}

-- TODO: can we / would it help to, reuse 'let_'?
-- BUG: we assume the argument is emissible!
pushLet :: (ABT Term abt) => abt '[] a -> Expect abt (Variable a)
pushLet e =
    caseVarSyn e return $ \_ -> do
        x <- freshVar Text.empty (typeOf e)
        unsafePush (SStuff1 x (\c ->
            syn (Let_ :$ e :* bind x c :* End)) Nil1)
        return x
{-
emitLet e =
    caseVarSyn e return $ \_ ->
        emit Text.empty (typeOf e) $ \f ->
            syn (Let_ :$ e :* f :* End)
-}


-- TODO: introduce HProb variants of integrate\/summate so we can avoid the need for 'unsafeProb' here
expectMeasureOp
    :: forall abt typs args a
    .  (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => MeasureOp typs a
    -> SArgs abt args
    -> Expect abt (abt '[] a)
expectMeasureOp Lebesgue = \End ->
    var <$> pushIntegrate P.negativeInfinity P.infinity
expectMeasureOp Counting = \End ->
    var <$> pushSummate P.negativeInfinity P.infinity
expectMeasureOp Categorical = \(ps :* End) -> do
    ps' <- var <$> pushLet ps
    tot <- var <$> pushLet (P.summateV ps')
    unsafePush (SStuff0 (\c -> P.if_ (P.zero P.< tot) c P.zero) Nil1)
    i <- freshVar Text.empty SNat
    Expect $ \c h ->
        P.summateV
            (syn (Array_ (P.size ps') (bind i ((ps' P.! var i) P.* c (var i) h))))
            P./ tot
    {-
    let_ ps $ \ps' ->
    let_ (summateV ps') $ \tot ->
    if_ (zero < tot)
        (summateV (mapWithIndex (\i p -> p * inst c i) ps') / tot)
        zero
    -}
expectMeasureOp Uniform = \(lo :* hi :* End) -> do
    -- BUG: @(let_ zero $ \y -> uniform y one)@ doesn't work as desired; *drops* the @SLet y zero@ binding entirely!!
    lo' <- var <$> pushLet lo
    hi' <- var <$> pushLet hi
    x   <- var <$> pushIntegrate lo' hi'
    unsafePush (SStuff0 (\c -> P.densityUniform lo' hi' x P.* c) Nil1)
    return x
    {-
    let_ lo $ \lo' ->
    let_ hi $ \hi' ->
    integrate lo' hi' $ \x ->
        densityUniform lo' hi' x * inst c x
    -}
expectMeasureOp Normal = \(mu :* sd :* End) -> do
    -- HACK: for some reason w need to break apart the 'emit' and the 'emit_' or else we get a "<<loop>>" exception. Not entirely sure why, but it prolly indicates a bug somewhere.
    x <- var <$> pushIntegrate P.negativeInfinity P.infinity
    unsafePush (SStuff0 (\c -> P.densityNormal mu sd x P.* c) Nil1)
    return x
    {-
    \c ->
        P.integrate P.negativeInfinity P.infinity $ \x ->
            P.densityNormal mu sd x P.* let_ x c)
    -}
expectMeasureOp Poisson = \(l :* End) -> do
    l' <- var <$> pushLet l
    unsafePush (SStuff0 (\c -> P.if_ (P.zero P.< l') c P.zero) Nil1)
    x  <- var <$> pushSummate P.zero P.infinity
    x_ <- var <$> pushLet (P.unsafeFrom_ signed x) -- TODO: Or is this small enough that we'd be fine using Haskell's "let" and so duplicating the coercion of a variable however often?
    unsafePush (SStuff0 (\c -> P.densityPoisson l' x_ P.* c) Nil1)
    return x_
    {-
    let_ l $ \l' ->
    if_ (zero < l')
        (summate zero infinity $ \x ->
            let x_ = unsafeFrom_ signed x in
            densityPoisson l' x_ * inst c x_)
        zero
    -}
expectMeasureOp Gamma = \(shape :* scale :* End) -> do
    x  <- var <$> pushIntegrate P.zero P.infinity
    x_ <- var <$> pushLet (P.unsafeProb x) -- TODO: Or is this small enough that we'd be fine using Haskell's "let" and so duplicating the coercion of a variable however often?
    unsafePush (SStuff0 (\c -> P.densityGamma shape scale x_ P.* c) Nil1)
    return x_
    {-
    integrate zero infinity $ \x ->
        let x_ = unsafeProb x in
        densityGamma shape scale x_ * inst c x_
    -}
expectMeasureOp Beta = \(a :* b :* End) -> do
    x  <- var <$> pushIntegrate P.zero P.one
    x_ <- var <$> pushLet (P.unsafeProb x) -- TODO: Or is this small enough that we'd be fine using Haskell's "let" and so duplicating the coercion of a variable however often?
    unsafePush (SStuff0 (\c -> P.densityBeta a b x_ P.* c) Nil1)
    return x_
    {-
    integrate zero one $ \x ->
        let x_ = unsafeProb x in
        densityBeta a b x_ * inst c x_
    -}

----------------------------------------------------------------
----------------------------------------------------------- fin.
