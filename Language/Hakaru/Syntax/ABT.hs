{-# LANGUAGE RankNTypes
           , ScopedTypeVariables
           , GADTs
           , TypeFamilies
           , DataKinds
           , PolyKinds
           , DeriveDataTypeable
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.06.24
-- |
-- Module      :  Language.Hakaru.Syntax.ABT
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- The interface for abstract binding trees. Given the generating
-- functor 'AST': the non-recursive 'View' type extends 'AST' by
-- adding variables and binding; and each 'ABT' type  (1) provides
-- some additional annotations at each recursion site, and then (2)
-- ties the knot to produce the recursive trees.
----------------------------------------------------------------
module Language.Hakaru.Syntax.ABT
    (
    -- TODO: move this stuff elsewhere
    -- * Indexed variants of standard classes
      IFunctor(..)
    , IMonoid(..)
    , IFoldable(..)
    
    -- * The abstract binding tree interface
    , Variable(..)
    -- See note about exposing 'View', 'viewABT', and 'unviewABT'
    , View(..), unviewABT
    , ABT(..), caseABT, caseOpenABT, caseVarSynABT
    , subst
    , ABTException(..)
    -- ** Some ABT instances
    , TrivialABT()
    , FreeVarsABT()
    ) where

import           Data.Typeable     (Typeable)
import           Data.Set          (Set)
import qualified Data.Set          as Set
import           Data.Monoid
import           Data.Foldable
import           Control.Arrow     (second, (***))
import           Control.Exception (Exception, throw)

import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.TypeEq (Sing, SingI, toSing, TypeEq(Refl), jmEq)
import Language.Hakaru.Syntax.AST

----------------------------------------------------------------
-- TODO: will we want to make this polykinded instead of restricting to the @Hakaru*@ kind?
-- | A functor on the category of @k@-indexed types.
class IFunctor (f :: (k -> *) -> k -> *) where
    hmap :: (forall b. g b -> g' b) -> f g a -> f g' a 


-- | A monoid lifted to be (trivially) @k@-indexed.
newtype IMonoid (m :: *) (a :: k) =
    IMonoid { unIMonoid :: m }
instance Monoid m => Monoid (IMonoid m a) where
    mempty = IMonoid mempty
    mappend (IMonoid m) (IMonoid n) = IMonoid (mappend m n)
    mconcat ms = IMonoid (mconcat $ map unIMonoid ms)


-- | A foldable functor on the category of @k@-indexed types.
class IFunctor f => IFoldable (f :: (k -> *) -> k -> *) where
    hfold :: (Monoid m) => f (IMonoid m) a -> m
    hfold = hfoldMap unIMonoid

    hfoldMap :: (Monoid m) => (forall b. g b -> m) -> f g a -> m
    hfoldMap f = hfold . hmap (IMonoid . f)


-- TODO: move this instance to "Language.Hakaru.Syntax.AST"
instance IFunctor AST where
    hmap f (Lam_ p  e)           = Lam_ p (f e)
    hmap f (App_ e1 e2)          = App_ (f e1) (f e2)
    hmap f (Let_ e1 e2)          = Let_ (f e1) (f e2)
    hmap f (Fix_ e)              = Fix_ (f e)
    hmap _ (PrimOp_ o)           = PrimOp_ o
    hmap f (NaryOp_ o es)        = NaryOp_ o (fmap f es)
    hmap f (Integrate_ e1 e2 e3) = Integrate_ (f e1) (f e2) (f e3)
    hmap f (Summate_   e1 e2 e3) = Summate_   (f e1) (f e2) (f e3)
    hmap _ (Value_ v)            = Value_ v
    hmap f (CoerceTo_   c e)     = CoerceTo_   c (f e)
    hmap f (UnsafeFrom_ c e)     = UnsafeFrom_ c (f e)
    hmap f (List_  es)           = List_  (map f es)
    hmap f (Maybe_ me)           = Maybe_ (fmap f me)
    hmap f (Case_  e pes)        = Case_ (f e) (map (second f) pes)
    hmap f (Array_ e1 e2)        = Array_ (f e1) (f e2)
    hmap f (Bind_  e1 e2)        = Bind_  (f e1) (f e2)
    hmap f (Superpose_ pes)      = Superpose_ (map (f *** f) pes)
    hmap f (Dp_    e1 e2)        = Dp_    (f e1) (f e2)
    hmap f (Plate_ e)            = Plate_ (f e)
    hmap f (Chain_ e)            = Chain_ (f e)
    hmap f (Lub_ e1 e2)          = Lub_   (f e1) (f e2)
    hmap _ Bot_                  = Bot_


-- TODO: move this instance to "Language.Hakaru.Syntax.AST"
instance IFoldable AST where
    hfoldMap f (Lam_ _  e)           = f e
    hfoldMap f (App_ e1 e2)          = f e1 `mappend` f e2
    hfoldMap f (Let_ e1 e2)          = f e1 `mappend` f e2
    hfoldMap f (Fix_ e)              = f e
    hfoldMap _ (PrimOp_ _)           = mempty
    hfoldMap f (NaryOp_ _ es)        = foldMap f es
    hfoldMap f (Integrate_ e1 e2 e3) = f e1 `mappend` f e2 `mappend` f e3
    hfoldMap f (Summate_   e1 e2 e3) = f e1 `mappend` f e2 `mappend` f e3
    hfoldMap _ (Value_ _)            = mempty
    hfoldMap f (CoerceTo_   _ e)     = f e
    hfoldMap f (UnsafeFrom_ _ e)     = f e
    hfoldMap f (List_  es)           = foldMap f es
    hfoldMap f (Maybe_ me)           = foldMap f me
    hfoldMap f (Case_  e pes)        = f e  `mappend` foldMap (f . snd) pes
    hfoldMap f (Array_ e1 e2)        = f e1 `mappend` f e2
    hfoldMap f (Bind_  e1 e2)        = f e1 `mappend` f e2
    hfoldMap f (Superpose_ pes)      = foldMap (\(e1,e2) -> f e1 `mappend` f e2) pes
    hfoldMap f (Dp_    e1 e2)        = f e1 `mappend` f e2
    hfoldMap f (Plate_ e)            = f e
    hfoldMap f (Chain_ e)            = f e
    hfoldMap f (Lub_ e1 e2)          = f e1 `mappend` f e2
    hfoldMap _ Bot_                  = mempty

----------------------------------------------------------------
-- TODO: actually define 'Variable' as something legit
-- TODO: maybe have @Variable a@ instead, with @SomeVariable@ to package up the existential?
newtype Variable = Variable String
    deriving (Eq, Ord, Read, Show)


-- TODO: go back to the name \"Abs\"(traction), and figure out some other name for the \"Abs\"(olute value) PrimOp to avoid conflict. Or maybe call it \"Bind\"(er) and then come up with some other name for the HMeasure monadic bind operator?
-- <http://semantic-domain.blogspot.co.uk/2015/03/abstract-binding-trees.html>
-- <http://semantic-domain.blogspot.co.uk/2015/03/abstract-binding-trees-addendum.html>
-- <https://gist.github.com/neel-krishnaswami/834b892327271e348f79>
-- TODO: abstract over 'AST' like neelk does for @signature@?
-- TODO: remove the proxy type for 'Var', and infer it instead?
--
-- | The raw view of abstract binding trees, to separate out variables
-- and binders from (1) the rest of syntax (cf., 'AST'), and (2)
-- whatever annotations (cf., the 'ABT' instances).
--
-- HACK: We only want to expose the patterns generated by this type,
-- not the constructors themselves. That way, callers must use the
-- smart constructors of the ABT class.
--
-- BUG: if we don't expose this type, then clients can't define
-- their own ABT instances (without reinventing their own copy of
-- this type)...
data View :: (Hakaru * -> *) -> Hakaru * -> * where
    -- TODO: what are the overhead costs of storying a Sing? Would it be cheaper to store the SingI dictionary (and a Proxy, as necessary)?
    Var  :: !Variable -> !(Sing a) -> View abt a
    Open :: !Variable -> abt a -> View abt a
    Syn  :: !(AST abt a) -> View abt a


instance IFunctor View where
    hmap _ (Var  x p) = Var  x p
    hmap f (Open x e) = Open x (f e)
    hmap f (Syn  t)   = Syn (hmap f t)


-- TODO: neelk includes 'subst' in the signature. Any reason we should?
class ABT (abt :: Hakaru * -> *) where
    var      :: Variable -> Sing a -> abt a
    open     :: Variable -> abt  a -> abt a
    syn      :: AST abt a          -> abt a
    -- See note about exposing 'View', 'viewABT', and 'unviewABT'
    viewABT  :: abt a -> View abt a
    
    freeVars :: abt a -> Set Variable
    -- TODO: add a function for checking alpha-equivalence? Other stuff?
    -- TODO: does it make sense ot have the functions for generating fresh variable names here? or does that belong in a separate class?


-- | A variant of 'viewABT' for not accessing the 'View' type
-- directly. Unlike 'caseOpenABT' and 'caseVarSynABT', this function
-- safely covers all three constructors.
caseABT
    :: (ABT abt)
    => abt a
    -> (Variable -> Sing a -> r)
    -> (Variable -> abt  a -> r)
    -> (AST abt a          -> r)
    -> r
caseABT e v o s =
    case viewABT e of
    Var  x p  -> v x p
    Open x e' -> o x e'
    Syn  t    -> s t


-- See note about exposing 'View', 'viewABT', and 'unviewABT'
unviewABT :: (ABT abt) => View abt a -> abt a
unviewABT (Var  x p) = var  x p
unviewABT (Open x e) = open x e
unviewABT (Syn  t)   = syn  t


data ABTException
    = ExpectedOpenException
    | ExpectedVarSynException
    | SubstitutionTypeError
    deriving (Show, Typeable)

instance Exception ABTException

-- We could render this function safe by further indexing @abt@
-- with a tag to say whether it's Open or Var/Syn. But that may be
-- overkill, especially once we start handling more complicated
-- binders. This only throws an error if the ABT the parser generates
-- is malformed, we can trust/check the parser rather than complicating
-- the types further.
--
-- | Assume the ABT is 'Open' and then project out the components.
-- If the ABT is not 'Open', then this function will throw an
-- 'ExpectedOpenException' error.
caseOpenABT
    :: (ABT abt)
    => abt a
    -> (Variable -> abt  a -> r)
    -> r
caseOpenABT e v =
    case viewABT e of
    Open x e' -> v x e'
    _         -> throw ExpectedOpenException -- TODO: add info about the call-site

-- | Assume the ABT is not 'Open' and then project out the components.
-- If the ABT is in fact 'Open', then this function will throw an
-- 'ExpectedVarSynException' error.
caseVarSynABT
    :: (ABT abt)
    => abt a
    -> (Variable -> Sing a -> r)
    -> (AST abt a          -> r)
    -> r
caseVarSynABT e v s =
    case viewABT e of
    Var  x p -> v x p
    Open _ _ -> throw ExpectedVarSynException -- TODO: add call-site info
    Syn  t   -> s t


----------------------------------------------------------------
-- A trivial ABT with no annotations
newtype TrivialABT (a :: Hakaru *) = TrivialABT (View TrivialABT a)

instance ABT TrivialABT where
    var  x p = TrivialABT (Var  x p)
    open x e = TrivialABT (Open x e)
    syn  t   = TrivialABT (Syn  t)

    viewABT  (TrivialABT v) = v
    
    -- This is very expensive! use 'FreeVarsABT' to fix that
    freeVars (TrivialABT v) =
        case v of
        Var  x _ -> Set.singleton x
        Open x e -> Set.delete x (freeVars e)
        Syn  t   -> hfoldMap freeVars t


----------------------------------------------------------------
-- TODO: replace @Set Variable@ with @Map Variable (Hakaru Star)@; though that belongs more in the type-checking than in this FreeVarsABT itself...
-- TODO: generalize this pattern for any monoidal annotation?
-- | An ABT which keeps track of free variables.
data FreeVarsABT (a :: Hakaru *)
    = FreeVarsABT !(Set Variable) !(View FreeVarsABT a)
    -- N.B., Set is a monoid with {Set.empty; Set.union; Set.unions}

instance ABT FreeVarsABT where
    var  x p = FreeVarsABT (Set.singleton x)           (Var  x p)
    open x e = FreeVarsABT (Set.delete x $ freeVars e) (Open x e)
    syn  t   = FreeVarsABT (hfoldMap freeVars t)       (Syn  t)

    viewABT  (FreeVarsABT _  v) = v

    freeVars (FreeVarsABT xs _) = xs


----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: something smarter
freshen :: Variable -> Set Variable -> Variable
freshen x@(Variable x0) xs
    | x `Set.member` xs = freshen (Variable $ x0 ++"'") xs
    | otherwise         = x

-- | Rename a free variable. Does nothing if the variable is bound.
rename :: forall abt a. (ABT abt) => Variable -> Variable -> abt a -> abt a
rename x y = go
    where
    go :: forall b. abt b -> abt b
    go e =
        case viewABT e of
        Var z p
            | x == z    -> var y p
            | otherwise -> e
        Open z e'
            | x == z    -> e
            | otherwise -> open z (go e')
        Syn t           -> syn (hmap go t)


-- N.B., this /is/ guaranteed to preserve type safety— provided it doesn't throw an exception.
subst
    :: forall abt a b
    .  (SingI a, ABT abt)
    => Variable
    -> abt a
    -> abt b
    -> abt b
subst x e = go
    where
    go :: forall c. abt c -> abt c
    go body =
        case viewABT body of
        Var z p
            | x == z      ->
                case jmEq p (toSing e) of
                Just Refl -> e
                Nothing   -> throw SubstitutionTypeError
            | otherwise   -> body
        Open z body'
            | x == z      -> body
            | otherwise   ->
                let z' = freshen z (freeVars e `mappend` freeVars body)
                in  open z' (go (rename z z' body'))
        Syn body'         -> syn (hmap go body')

----------------------------------------------------------------
----------------------------------------------------------- fin.
