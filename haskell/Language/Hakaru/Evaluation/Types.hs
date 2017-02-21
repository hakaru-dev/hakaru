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
--                                                    2016.04.28
-- |
-- Module      :  Language.Hakaru.Evaluation.Types
-- Copyright   :  Copyright (c) 2016 the Hakaru team
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
    , getLazyVariable, isLazyVariable
    , getLazyLiteral,  isLazyLiteral

    -- * The monad for partial evaluation
    , Purity(..), Statement(..), statementVars, isBoundBy
    , Index, indVar, indSize
#ifdef __TRACE_DISINTEGRATE__
    , ppList
    , ppInds
    , ppStatement
    , pretty_Statements
    , pretty_Statements_withTerm
    , prettyAssocs
#endif
    , EvaluationMonad(..)
    , freshVar
    , freshenVar
    , Hint(..), freshVars
    , freshenVars
    , freshInd
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
import           Data.Traversable
#endif
import           Control.Arrow        ((***))
import qualified Data.Foldable        as F
import           Data.List.NonEmpty   (NonEmpty(..))
import qualified Data.Text            as T
import           Data.Text            (Text)
import           Data.Proxy           (KProxy(..))

import Language.Hakaru.Syntax.IClasses
import Data.Number.Nat
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing    (Sing(..))
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.AST.Eq (alphaEq)
-- import Language.Hakaru.Syntax.TypeOf
import Language.Hakaru.Syntax.ABT
import qualified Language.Hakaru.Syntax.Prelude as P

#ifdef __TRACE_DISINTEGRATE__
import qualified Text.PrettyPrint     as PP
import Language.Hakaru.Pretty.Haskell
#endif

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
data Head :: ([Hakaru] -> Hakaru -> *) -> Hakaru -> * where
    -- Simple heads (aka, the usual stuff)
    WLiteral :: !(Literal a) -> Head abt a
    -- BUG: even though the 'Datum' type has a single constructor, we get a warning about not being able to UNPACK it in 'WDatum'... wtf?
    WDatum :: !(Datum (abt '[]) (HData' t)) -> Head abt (HData' t)
    WEmpty :: !(Sing ('HArray a)) -> Head abt ('HArray a)
    WArray :: !(abt '[] 'HNat) -> !(abt '[ 'HNat] a) -> Head abt ('HArray a)
    WArrayLiteral
           :: [abt '[] a] -> Head abt ('HArray a)
    WLam   :: !(abt '[ a ] b) -> Head abt (a ':-> b)

    -- Measure heads (N.B., not simply @abt '[] ('HMeasure _)@)
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
    WPlate
        :: !(abt '[] 'HNat)
        -> !(abt '[ 'HNat ] ('HMeasure a))
        -> Head abt ('HMeasure ('HArray a))
    WChain
        :: !(abt '[] 'HNat)
        -> !(abt '[] s)
        -> !(abt '[ s ] ('HMeasure (HPair a s)))
        -> Head abt ('HMeasure (HPair ('HArray a) s))
    WSuperpose
        :: !(NonEmpty (abt '[] 'HProb, abt '[] ('HMeasure a)))
        -> Head abt ('HMeasure a)
    WReject
        :: !(Sing ('HMeasure a)) -> Head abt ('HMeasure a)

    -- Type coercion stuff. These are transparent re head-ness; that is, they behave more like HNF than WHNF.
    -- TODO: we prolly don't actually want\/need the coercion variants... we'd lose some proven-guarantees about cancellation, but everything should work just fine. The one issue that remains is if we have coercion of 'WIntegrate' or 'WSummate', since without the 'WCoerceTo'\/'WUnsafeFrom' constructors we'd be forced to call the coercion of an integration \"neutral\"--- even though it's not actually a neutral term!
    WCoerceTo   :: !(Coercion a b) -> !(Head abt a) -> Head abt b
    WUnsafeFrom :: !(Coercion a b) -> !(Head abt b) -> Head abt a

    -- Other funky stuff
    WIntegrate
        :: !(abt '[] 'HReal)
        -> !(abt '[] 'HReal)
        -> !(abt '[ 'HReal ] 'HProb)
        -> Head abt 'HProb
    -- WSummate
    --     :: !(abt '[] 'HReal)
    --     -> !(abt '[] 'HReal)
    --     -> !(abt '[ 'HInt ] 'HProb)
    --     -> Head abt 'HProb

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
fromHead (WArrayLiteral  es)    = syn (ArrayLiteral_ es)
fromHead (WLam        e1)       = syn (Lam_ :$ e1 :* End)
fromHead (WMeasureOp  o  es)    = syn (MeasureOp_ o :$ es)
fromHead (WDirac      e1)       = syn (Dirac :$ e1 :* End)
fromHead (WMBind      e1 e2)    = syn (MBind :$ e1 :* e2 :* End)
fromHead (WPlate      e1 e2)    = syn (Plate :$ e1 :* e2 :* End)
fromHead (WChain      e1 e2 e3) = syn (Chain :$ e1 :* e2 :* e3 :* End)
fromHead (WSuperpose  pes)      = syn (Superpose_ pes)
fromHead (WReject     typ)      = syn (Reject_ typ)
fromHead (WCoerceTo   c e1)     = syn (CoerceTo_   c :$ fromHead e1 :* End)
fromHead (WUnsafeFrom c e1)     = syn (UnsafeFrom_ c :$ fromHead e1 :* End)
fromHead (WIntegrate  e1 e2 e3) = syn (Integrate :$ e1 :* e2 :* e3 :* End)
--fromHead (WSummate    e1 e2 e3) = syn (Summate   :$ e1 :* e2 :* e3 :* End)


-- | Identify terms which are already heads.
toHead :: (ABT Term abt) => abt '[] a -> Maybe (Head abt a)
toHead e =
    caseVarSyn e (const Nothing) $ \t ->
        case t of
        Literal_     v                      -> Just $ WLiteral   v
        Datum_       d                      -> Just $ WDatum     d
        Empty_       typ                    -> Just $ WEmpty     typ
        Array_       e1     e2              -> Just $ WArray     e1 e2
        ArrayLiteral_       es              -> Just $ WArrayLiteral es
        Lam_      :$ e1  :* End             -> Just $ WLam       e1
        MeasureOp_   o   :$ es              -> Just $ WMeasureOp o  es
        Dirac     :$ e1  :* End             -> Just $ WDirac     e1
        MBind     :$ e1  :* e2 :* End       -> Just $ WMBind     e1 e2
        Plate     :$ e1  :* e2 :* End       -> Just $ WPlate     e1 e2
        Chain     :$ e1  :* e2 :* e3 :* End -> Just $ WChain     e1 e2 e3 
        Superpose_   pes                    -> Just $ WSuperpose pes
        CoerceTo_    c   :$ e1 :* End       -> WCoerceTo   c <$> toHead e1
        UnsafeFrom_  c   :$ e1 :* End       -> WUnsafeFrom c <$> toHead e1
        Integrate :$ e1  :* e2 :* e3 :* End -> Just $ WIntegrate e1 e2 e3
        --Summate   :$ e1  :* e2 :* e3 :* End -> Just $ WSummate   e1 e2 e3
        _ -> Nothing

instance Functor21 Head where
    fmap21 _ (WLiteral    v)        = WLiteral v
    fmap21 f (WDatum      d)        = WDatum (fmap11 f d)
    fmap21 _ (WEmpty      typ)      = WEmpty typ
    fmap21 f (WArray      e1 e2)    = WArray (f e1) (f e2)
    fmap21 f (WArrayLiteral  es)    = WArrayLiteral (fmap f es)
    fmap21 f (WLam        e1)       = WLam (f e1)
    fmap21 f (WMeasureOp  o  es)    = WMeasureOp o (fmap21 f es)
    fmap21 f (WDirac      e1)       = WDirac (f e1)
    fmap21 f (WMBind      e1 e2)    = WMBind (f e1) (f e2)
    fmap21 f (WPlate      e1 e2)    = WPlate (f e1) (f e2)
    fmap21 f (WChain      e1 e2 e3) = WChain (f e1) (f e2) (f e3)
    fmap21 f (WSuperpose  pes)      = WSuperpose (fmap (f *** f) pes)
    fmap21 _ (WReject     typ)      = WReject typ
    fmap21 f (WCoerceTo   c e1)     = WCoerceTo   c (fmap21 f e1)
    fmap21 f (WUnsafeFrom c e1)     = WUnsafeFrom c (fmap21 f e1)
    fmap21 f (WIntegrate  e1 e2 e3) = WIntegrate (f e1) (f e2) (f e3)
    --fmap21 f (WSummate    e1 e2 e3) = WSummate   (f e1) (f e2) (f e3)

instance Foldable21 Head where
    foldMap21 _ (WLiteral    _)        = mempty
    foldMap21 f (WDatum      d)        = foldMap11 f d
    foldMap21 _ (WEmpty      _)        = mempty
    foldMap21 f (WArray      e1 e2)    = f e1 `mappend` f e2
    foldMap21 f (WArrayLiteral  es)    = F.foldMap f es
    foldMap21 f (WLam        e1)       = f e1
    foldMap21 f (WMeasureOp  _  es)    = foldMap21 f es
    foldMap21 f (WDirac      e1)       = f e1
    foldMap21 f (WMBind      e1 e2)    = f e1 `mappend` f e2
    foldMap21 f (WPlate      e1 e2)    = f e1 `mappend` f e2
    foldMap21 f (WChain      e1 e2 e3) = f e1 `mappend` f e2 `mappend` f e3
    foldMap21 f (WSuperpose  pes)      = foldMapPairs f pes
    foldMap21 _ (WReject     _)        = mempty
    foldMap21 f (WCoerceTo   _ e1)     = foldMap21 f e1
    foldMap21 f (WUnsafeFrom _ e1)     = foldMap21 f e1
    foldMap21 f (WIntegrate  e1 e2 e3) = f e1 `mappend` f e2 `mappend` f e3
    --foldMap21 f (WSummate    e1 e2 e3) = f e1 `mappend` f e2 `mappend` f e3

instance Traversable21 Head where
    traverse21 _ (WLiteral    v)        = pure $ WLiteral v
    traverse21 f (WDatum      d)        = WDatum <$> traverse11 f d
    traverse21 _ (WEmpty      typ)      = pure $ WEmpty typ
    traverse21 f (WArray      e1 e2)    = WArray <$> f e1 <*> f e2
    traverse21 f (WArrayLiteral  es)    = WArrayLiteral <$> traverse f es
    traverse21 f (WLam        e1)       = WLam <$> f e1
    traverse21 f (WMeasureOp  o  es)    = WMeasureOp o <$> traverse21 f es
    traverse21 f (WDirac      e1)       = WDirac <$> f e1
    traverse21 f (WMBind      e1 e2)    = WMBind <$> f e1 <*> f e2
    traverse21 f (WPlate      e1 e2)    = WPlate <$> f e1 <*> f e2
    traverse21 f (WChain      e1 e2 e3) = WChain <$> f e1 <*> f e2 <*> f e3
    traverse21 f (WSuperpose  pes)      = WSuperpose <$> traversePairs f pes
    traverse21 _ (WReject     typ)      = pure $ WReject typ
    traverse21 f (WCoerceTo   c e1)     = WCoerceTo   c <$> traverse21 f e1
    traverse21 f (WUnsafeFrom c e1)     = WUnsafeFrom c <$> traverse21 f e1
    traverse21 f (WIntegrate  e1 e2 e3) = WIntegrate <$> f e1 <*> f e2 <*> f e3
    --traverse21 f (WSummate    e1 e2 e3) = WSummate   <$> f e1 <*> f e2 <*> f e3


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
    --
    -- TODO: is there some /clean/ way to ensure that the neutral term is exactly a chain of blocked redexes? That is, we want to be able to pull out neutral 'Case_' terms; so we want to make sure they're not wrapped in let-bindings, coercions, etc.

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
viewHeadDatum (WDatum d) = d
viewHeadDatum _          = error "viewHeadDatum: the impossible happened"


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
                    -- BUG: literals should never be neutral in the first place; but even if we got one, we shouldn't call it neutral after coercing it.
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
                    -- BUG: literals should never be neutral in the first place; but even if we got one, we shouldn't call it neutral after coercing it.
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


-- | Is the lazy value a variable?
getLazyVariable :: (ABT Term abt) => Lazy abt a -> Maybe (Variable a)
getLazyVariable e =
    case e of
    Whnf_ (Head_   _)  -> Nothing
    Whnf_ (Neutral e') -> caseVarSyn e' Just (const Nothing)
    Thunk e'           -> caseVarSyn e' Just (const Nothing)

-- | Boolean-blind variant of 'getLazyVariable'
isLazyVariable :: (ABT Term abt) => Lazy abt a -> Bool
isLazyVariable = maybe False (const True) . getLazyVariable


-- | Is the lazy value a literal?
getLazyLiteral :: (ABT Term abt) => Lazy abt a -> Maybe (Literal a)
getLazyLiteral e =
    case e of
    Whnf_ (Head_ (WLiteral v)) -> Just v
    Whnf_ _                    -> Nothing -- by construction
    Thunk e' ->
        caseVarSyn e' (const Nothing) $ \t ->
            case t of
            Literal_ v -> Just v
            _          -> Nothing

-- | Boolean-blind variant of 'getLazyLiteral'
isLazyLiteral :: (ABT Term abt) => Lazy abt a -> Bool
isLazyLiteral = maybe False (const True) . getLazyLiteral

----------------------------------------------------------------

-- | A kind for indexing 'Statement' to know whether the statement
-- is pure (and thus can be evaluated in any ambient monad) vs
-- impure (i.e., must be evaluated in the 'HMeasure' monad).
--
-- TODO: better names!
data Purity = Pure | Impure | ExpectP
    deriving (Eq, Read, Show)

data Index ast = Ind (Variable 'HNat) (ast 'HNat)

instance (ABT Term abt) => Eq (Index (abt '[])) where
    Ind i1 s1 == Ind i2 s2 = i1 == i2 && (alphaEq s1 s2)

instance (ABT Term abt) => Ord (Index (abt '[])) where
    compare (Ind i _) (Ind j _) = compare i j -- TODO check this

indVar :: Index ast -> Variable 'HNat
indVar (Ind v _ ) = v

indSize :: Index ast -> ast 'HNat
indSize (Ind _ a) = a

-- | A single statement in some ambient monad (specified by the @p@
-- type index). In particular, note that the the first argument to
-- 'MBind' (or 'Let_') together with the variable bound in the
-- second argument forms the \"statement\" (leaving out the body
-- of the second argument, which may be part of a following statement).
-- In addition to these binding constructs, we also include a few
-- non-binding statements like 'SWeight'.
--
-- The semantics of this type are as follows. Let @ss :: [Statement
-- abt p]@ be a sequence of statements. We have @Γ@: the collection
-- of all free variables that occur in the term expressions in @ss@,
-- viewed as a measureable space (namely the product of the measureable
-- spaces for each variable). And we have @Δ@: the collection of
-- all variables bound by the statements in @ss@, also viewed as a
-- measurable space. The semantic interpretation of @ss@ is a
-- measurable function of type @Γ ':-> M Δ@ where @M@ is either
-- @HMeasure@ (if @p ~ 'Impure@) or @Identity@ (if @p ~ 'Pure@).
data Statement :: ([Hakaru] -> Hakaru -> *) -> Purity -> * where
    -- BUG: haddock doesn't like annotations on GADT constructors. So we can't make the constructor descriptions below available to Haddock.
    -- <https://github.com/hakaru-dev/hakaru/issues/6>
    
    -- A variable bound by 'MBind' to a measure expression.
    SBind
        :: forall abt (a :: Hakaru)
        .  {-# UNPACK #-} !(Variable a)
        -> !(Lazy abt ('HMeasure a))
        -> [Index (abt '[])]
        -> Statement abt 'Impure

    -- A variable bound by 'Let_' to an expression.
    SLet
        :: forall abt p (a :: Hakaru)
        .  {-# UNPACK #-} !(Variable a)
        -> !(Lazy abt a)
        -> [Index (abt '[])]
        -> Statement abt p


    -- A weight; i.e., the first component of each argument to
    -- 'Superpose_'. This is a statement just so that we can avoid
    -- needing to atomize the weight itself.
    SWeight
        :: forall abt
        .  !(Lazy abt 'HProb)
        -> [Index (abt '[])]
        -> Statement abt 'Impure

    -- A monadic guard statement. If the scrutinee matches the
    -- pattern, then we bind the variables as usual; otherwise, we
    -- return the empty measure. N.B., this statement type is only
    -- for capturing constraints that some pattern matches /in a/
    -- /monadic context/. In pure contexts we should be able to
    -- handle case analysis without putting anything onto the heap.
    SGuard
        :: forall abt (xs :: [Hakaru]) (a :: Hakaru)
        .  !(List1 Variable xs)
        -> !(Pattern xs a)
        -> !(Lazy abt a)
        -> [Index (abt '[])]
        -> Statement abt 'Impure

    -- Some arbitrary pure code. This is a statement just so that we can avoid needing to atomize the stuff in the pure code.
    --
    -- TODO: real names for these.
    -- TODO: generalize to use a 'VarSet' so we can collapse these
    -- TODO: defunctionalize? These break pretty printing...
    SStuff0
        :: forall abt
        .  (abt '[] 'HProb -> abt '[] 'HProb)
        -> [Index (abt '[])]
        -> Statement abt 'ExpectP
    SStuff1
        :: forall abt (a :: Hakaru)
        . {-# UNPACK #-} !(Variable a)
        -> (abt '[] 'HProb -> abt '[] 'HProb)
        -> [Index (abt '[])]
        -> Statement abt 'ExpectP


statementVars :: Statement abt p -> VarSet ('KProxy :: KProxy Hakaru)
statementVars (SBind x _ _)     = singletonVarSet x
statementVars (SLet  x _ _)     = singletonVarSet x
statementVars (SWeight _ _)     = emptyVarSet
statementVars (SGuard xs _ _ _) = toVarSet1 xs
statementVars (SStuff0   _ _)   = emptyVarSet
statementVars (SStuff1 x _ _)   = singletonVarSet x    

-- | Is the variable bound by the statement?
--
-- We return @Maybe ()@ rather than @Bool@ because in our primary
-- use case we're already in the @Maybe@ monad and so it's easier
-- to just stick with that. If we find other situations where we'd
-- really rather have the @Bool@, then we can easily change things
-- and use some @boolToMaybe@ function to do the coercion wherever
-- needed.
isBoundBy :: Variable (a :: Hakaru) -> Statement abt p -> Maybe ()
x `isBoundBy` SBind  y  _ _   = const () <$> varEq x y
x `isBoundBy` SLet   y  _ _   = const () <$> varEq x y
_ `isBoundBy` SWeight   _ _   = Nothing
x `isBoundBy` SGuard ys _ _ _ =
    if memberVarSet x (toVarSet1 ys) -- TODO: just check membership directly, rather than going through VarSet
    then Just ()
    else Nothing
_ `isBoundBy` SStuff0   _ _   = Nothing
x `isBoundBy` SStuff1 y _ _   = const () <$> varEq x y


-- TODO: remove this CPP guard, provided we don't end up with a cyclic dependency...
#ifdef __TRACE_DISINTEGRATE__
instance (ABT Term abt) => Pretty (Whnf abt) where
    prettyPrec_ p (Head_   w) = ppApply1 p "Head_" (fromHead w) -- HACK
    prettyPrec_ p (Neutral e) = ppApply1 p "Neutral" e

instance (ABT Term abt) => Pretty (Lazy abt) where
    prettyPrec_ p (Whnf_ w) = ppFun p "Whnf_" [PP.sep (prettyPrec_ 11 w)]
    prettyPrec_ p (Thunk e) = ppApply1 p "Thunk" e

ppApply1 :: (ABT Term abt) => Int -> String -> abt '[] a -> [PP.Doc]
ppApply1 p f e1 =
    let d = PP.text f PP.<+> PP.nest (1 + length f) (prettyPrec 11 e1)
    in [if p > 9 then PP.parens (PP.nest 1 d) else d]

ppFun :: Int -> String -> [PP.Doc] -> [PP.Doc]
ppFun _ f [] = [PP.text f]
ppFun p f ds =
    parens (p > 9) [PP.text f PP.<+> PP.nest (1 + length f) (PP.sep ds)]

parens :: Bool -> [PP.Doc] -> [PP.Doc]
parens True  ds = [PP.parens (PP.nest 1 (PP.sep ds))]
parens False ds = ds

ppList :: [PP.Doc] -> PP.Doc
ppList = PP.sep . (:[]) . PP.brackets . PP.nest 1 . PP.fsep . PP.punctuate PP.comma

ppInds :: (ABT Term abt) => [Index (abt '[])] -> PP.Doc
ppInds = ppList . map (ppVariable . indVar)

ppStatement :: (ABT Term abt) => Int -> Statement abt p -> PP.Doc
ppStatement p s =
    case s of
    SBind x e inds ->
        PP.sep $ ppFun p "SBind"
            [ ppVariable x
            , PP.sep $ prettyPrec_ 11 e
            , ppInds inds
            ]
    SLet x e inds ->
        PP.sep $ ppFun p "SLet"
            [ ppVariable x
            , PP.sep $ prettyPrec_ 11 e
            , ppInds inds
            ]
    SWeight e inds ->
        PP.sep $ ppFun p "SWeight"
            [ PP.sep $ prettyPrec_ 11 e
            , ppInds inds
            ]
    SGuard xs pat e inds ->
        PP.sep $ ppFun p "SGuard"
            [ PP.sep $ ppVariables xs
            , PP.sep $ prettyPrec_ 11 pat
            , PP.sep $ prettyPrec_ 11 e
            , ppInds inds
            ]
    SStuff0   _ _ ->
        PP.sep $ ppFun p "SStuff0"
            [ PP.text "TODO: ppStatement{SStuff0}"
            ]
    SStuff1 _ _ _ ->
        PP.sep $ ppFun p "SStuff1"
            [ PP.text "TODO: ppStatement{SStuff1}"
            ]

pretty_Statements :: (ABT Term abt) => [Statement abt p] -> PP.Doc
pretty_Statements []     = PP.text "[]"
pretty_Statements (s:ss) =
    foldl
        (\d s' -> d PP.$+$ PP.comma PP.<+> ppStatement 0 s')
        (PP.text "[" PP.<+> ppStatement 0 s)
        ss
    PP.$+$ PP.text "]"

pretty_Statements_withTerm
    :: (ABT Term abt) => [Statement abt p] -> abt '[] a -> PP.Doc
pretty_Statements_withTerm ss e =
    pretty_Statements ss PP.$+$ pretty e

prettyAssocs
    :: (ABT Term abt)
    => Assocs (abt '[])
    -> PP.Doc
prettyAssocs a = PP.vcat $ map go (fromAssocs a)
  where go (Assoc x e) = ppVariable x PP.<+>
                         PP.text "->" PP.<+>
                         pretty e
                                
#endif

----------------------------------------------------------------
-- | This class captures the monadic operations needed by the
-- 'evaluate' function in "Language.Hakaru.Lazy".
class (Functor m, Applicative m, Monad m, ABT Term abt)
    => EvaluationMonad abt m p | m -> abt p
    where
    -- TODO: should we have a *method* for arbitrarily incrementing the stored 'nextFreshNat'; or should we only rely on it being initialized correctly? Beware correctness issues about updating the lower bound after having called 'freshNat'...

    -- | Return a fresh natural number. That is, a number which is
    -- not the 'varID' of any free variable in the expressions of
    -- interest, and isn't a number we've returned previously.
    freshNat :: m Nat


    -- | Internal function for renaming the variables bound by a
    -- statement. We return the renamed statement along with a substitution
    -- for mapping the old variable names to their new variable names.
    freshenStatement
        :: Statement abt p
        -> m (Statement abt p, Assocs (Variable :: Hakaru -> *))
    freshenStatement s =
        case s of
          SWeight _ _    -> return (s, mempty)
          SBind x body i -> do
               x' <- freshenVar x
               return (SBind x' body i, singletonAssocs x x')
          SLet  x body i -> do
               x' <- freshenVar x
               return (SLet x' body i, singletonAssocs x x')
          SGuard xs pat scrutinee i -> do
               xs' <- freshenVars xs
               return (SGuard xs' pat scrutinee i, toAssocs1 xs xs')
          SStuff0   _ _ -> return (s, mempty)
          SStuff1 x f i -> do
               x' <- freshenVar x
               return (SStuff1 x' f i, singletonAssocs x x')


    -- | Returns the current Indices. Currently, this is only
    -- applicable to the Disintegration Monad, but could be
    -- relevant as other partial evaluators begin to handle
    -- Plate and Array
    getIndices :: m [Index (abt '[])]
    getIndices =  return []

    -- | Add a statement to the top of the context. This is unsafe
    -- because it may allow confusion between variables with the
    -- same name but different scopes (thus, may allow variable
    -- capture). Prefer using 'push_', 'push', or 'pushes'.
    unsafePush :: Statement abt p -> m ()

    -- | Call 'unsafePush' repeatedly. Is part of the class since
    -- we may be able to do this more efficiently than actually
    -- calling 'unsafePush' repeatedly.
    --
    -- N.B., this should push things in the same order as 'pushes'
    -- does.
    unsafePushes :: [Statement abt p] -> m ()
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
    -- bind /all/ the variables bound by @s@!
    --
    -- TODO: pass the continuation more detail, so it can avoid
    -- needing to be in the 'Maybe' monad due to the redundant call
    -- to 'varEq' in the continuation. In particular, we want to
    -- do this so that we can avoid the return type @m (Maybe (Maybe r))@
    -- while still correctly handling statements like 'SStuff1'
    -- which (a) do bind variables and thus should shadow bindings
    -- further up the 'ListContext', but which (b) offer up no
    -- expression the variable is bound to, and thus cannot be
    -- altered by forcing etc. To do all this, we need to pass the
    -- 'TypeEq' proof from (the 'varEq' call in) the 'isBoundBy'
    -- call in the instance; but that means we also need some way
    -- of tying it together with the existential variable in the
    -- 'Statement'. Perhaps we should have an alternative statement
    -- type which exposes the existential?
    select
        :: Variable (a :: Hakaru)
        -> (Statement abt p -> Maybe (m r))
        -> m (Maybe r)



-- TODO: define a new NameSupply monad in "Language.Hakaru.Syntax.Variable" for encapsulating these four fresh(en) functions?


-- | Given some hint and type, generate a variable with a fresh
-- 'varID'.
freshVar
    :: (EvaluationMonad abt m p)
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
    :: (EvaluationMonad abt m p)
    => List1 Hint xs
    -> m (List1 Variable xs)
freshVars Nil1         = return Nil1
freshVars (Cons1 x xs) = Cons1 <$> freshVar' x <*> freshVars xs
    where
    freshVar' (Hint hint typ) = freshVar hint typ


-- | Given a variable, return a new variable with the same hint and
-- type but with a fresh 'varID'.
freshenVar
    :: (EvaluationMonad abt m p)
    => Variable (a :: Hakaru)
    -> m (Variable a)
freshenVar x = (\i -> x{varID=i}) <$> freshNat


-- | Call 'freshenVar' repeatedly.
-- TODO: make this more efficient than actually calling 'freshenVar'
-- repeatedly.
freshenVars
    :: (EvaluationMonad abt m p)
    => List1 Variable (xs :: [Hakaru])
    -> m (List1 Variable xs)
freshenVars Nil1         = return Nil1
freshenVars (Cons1 x xs) = Cons1 <$> freshenVar x <*> freshenVars xs
{-
-- TODO: get this faster version to typecheck! And once we do, move it to IClasses.hs or wherever 'List1'\/'DList1' end up
freshenVars = go dnil1
    where
    go  :: (EvaluationMonad abt m p)
        => DList1 Variable (ys :: [Hakaru])
        -> List1  Variable (zs :: [Hakaru])
        -> m (List1 Variable (ys ++ zs))
    go k Nil1         = return (unDList1 k Nil1) -- for typechecking, don't use 'toList1' here.
    go k (Cons1 x xs) = do
        x' <- freshenVar x
        go (k `dsnoc1` x') xs -- BUG: type error....
-}

-- | Given a size, generate a fresh Index
freshInd :: (EvaluationMonad abt m p)
         => abt '[] 'HNat
         -> m (Index (abt '[]))
freshInd s = do
  x <- freshVar T.empty SNat
  return $ Ind x s


-- | Add a statement to the top of the context, renaming any variables
-- the statement binds and returning the substitution mapping the
-- old variables to the new ones. This is safer than 'unsafePush'
-- because it avoids variable confusion; but it is still somewhat
-- unsafe since you may forget to apply the substitution to \"the
-- rest of the term\". You almost certainly should use 'push' or
-- 'pushes' instead.
push_
    :: (ABT Term abt, EvaluationMonad abt m p)
    => Statement abt p
    -> m (Assocs (Variable :: Hakaru -> *))
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
    :: (ABT Term abt, EvaluationMonad abt m p)
    => Statement abt p   -- ^ the statement to push
    -> abt xs a          -- ^ the \"rest\" of the term
    -> (abt xs a -> m r) -- ^ what to do with the renamed \"rest\"
    -> m r               -- ^ the final result
push s e k = do
    rho <- push_ s
    k (renames rho e)


-- | Call 'push' repeatedly. (N.B., is more efficient than actually
-- calling 'push' repeatedly.) The head is pushed first and thus
-- is the furthest away in the final context, whereas the tail is
-- pushed last and is the closest in the final context.
pushes
    :: (ABT Term abt, EvaluationMonad abt m p)
    => [Statement abt p] -- ^ the statements to push
    -> abt xs a          -- ^ the \"rest\" of the term
    -> (abt xs a -> m r) -- ^ what to do with the renamed \"rest\"
    -> m r               -- ^ the final result
pushes ss e k = do
    -- TODO: is 'foldlM' the right one? or do we want 'foldrM'?
    rho <- F.foldlM (\rho s -> mappend rho <$> push_ s) mempty ss
    k (renames rho e)

----------------------------------------------------------------
----------------------------------------------------------- fin.
