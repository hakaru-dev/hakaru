{-# LANGUAGE CPP
           , ScopedTypeVariables
           , GADTs
           , DeriveDataTypeable
           , DataKinds
           , PolyKinds
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.06.30
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
-- ties the knot to produce the recursive trees. For an introduction
-- to this technique\/approach, see:
--
--    * <http://semantic-domain.blogspot.co.uk/2015/03/abstract-binding-trees.html>
--
--    * <http://semantic-domain.blogspot.co.uk/2015/03/abstract-binding-trees-addendum.html>
--
-- TODO: simultaneous multiple substitution
----------------------------------------------------------------
module Language.Hakaru.Syntax.ABT
    (
    -- * Our basic notion of variables\/names.
      Variable(..), varName, varID
    -- * The abstract binding tree interface
    , ABTException(..)
    -- See note about exposing 'View', 'viewABT', and 'unviewABT'
    , View(..), unviewABT
    , ABT(..), caseVarSynABT
    , subst
    -- ** Constructing first-order trees with a HOAS-like API
    -- cf., <http://comonad.com/reader/2014/fast-circular-substitution/>
    , Bindable(..), binder
    -- ** Some ABT instances
    , TrivialABT()
    , FreeVarsABT()
    ) where

import           Data.Typeable     (Typeable)
import           Data.Set          (Set)
import qualified Data.Set          as Set
import           Data.Function     (on)
import qualified Data.Foldable     as F
#if __GLASGOW_HASKELL__ < 710
import           Data.Monoid
#endif
import           Control.Exception (Exception, throw)

import Language.Hakaru.Syntax.Nat
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.TypeEq
import Language.Hakaru.Syntax.AST

----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: actually define 'Variable' as something legit
-- TODO: use Text instead of String.
-- TODO: should we make this type abstract?
--
-- TODO: maybe have @Variable a@ instead, with @SomeVariable@ to
-- package up the existential?
--
-- TODO: we may want to parameterize ABTs over their implementation
-- of Variable, so that we can use strict\/unpacked Nats everywhere
-- once we're done building the tree with 'binder'... Or, since we
-- unpack Variable in View, maybe it'd be better to parameterize
-- the ABT by its concrete view? If we did that, then we could
-- define a specialized Open for FreeVarsABT, in order to keep track
-- of whether the bound variable occurs or not (for defining
-- 'caseOpenABT' precisely).
--
-- | A variable is a pair of some hint for the name ('varName') and
-- some unique identifier ('varID'). N.B., the unique identifier
-- is lazy so that we can tie-the-knot in 'binder'.
data Variable = Variable !String Nat
    deriving (Read, Show)

-- | Project out the string the user suggested as a name for the
-- variable. N.B., this name does not uniquely identify the variable;
-- it is only a hint for how to show the variable when we need to
-- print things out.
varName :: Variable -> String
varName (Variable name _) = name

-- | Project out the unique identifier for the variable.
varID :: Variable -> Nat
varID (Variable _ i) = i

instance Eq Variable where
    (==) = (==) `on` varID

instance Ord Variable where
    compare = compare `on` varID

-- | Generate a new variable with the same hint as the old one.
-- N.B., the new variable is not guaranteed to be fresh! To do that,
-- we'd need some sort of name supply (and thus would need to be
-- monadic), or some sort of knowledge about the context in which
-- the variable will be used (e.g., as in 'binder')
prime :: Variable -> Variable
prime (Variable n i) = Variable n (i + 1)

----------------------------------------------------------------
-- TODO: go back to the name \"Abs\"(traction), and figure out some
-- other name for the \"Abs\"(olute value) PrimOp to avoid conflict.
-- Or maybe call it \"Bind\"(er) and then come up with some other
-- name for the HMeasure monadic bind operator?
--
-- TODO: should we abstract over 'AST' like neelk does for @signature@?
--
-- TODO: remove the singleton type for 'Var', and infer it instead?
--
-- TODO: distinguish between free and bound variables, a~la Locally
-- Nameless? also cf., <http://hackage.haskell.org/package/abt>
--
-- TODO: (?) index by the /local/ environment (or size thereof).
-- That is, Syn and Var would be @Z@, whereas Open would take @n@
-- to @S n@ (or @[]@ and taking @xs@ to some @x:xs@, respectively).
-- This way, the 'AST' could actually specify when it expects an
-- Open term. Doing this would give us improved type-safety of the
-- syntax tree, and should still free us from worrying about the
-- issues that tracking a /global/ environment would cause (like
-- worrying about weakening, etc),
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
data View :: (Hakaru -> *) -> Hakaru -> * where

    Syn  :: !(AST abt a) -> View abt a

    -- TODO: what are the overhead costs of storing a Sing? Would
    -- it be cheaper to store the SingI dictionary (and a Proxy,
    -- as necessary)?
    Var  :: {-# UNPACK #-} !Variable -> !(Sing a) -> View abt a

    -- N.B., this constructor is recursive, thus minimizing the
    -- memory overhead of whatever annotations our ABT stores (we
    -- only annotate once, at the top of a chaing of 'Open's, rather
    -- than before each one). However, in the 'ABT' class, we provide
    -- an API as if things went straight back to @abt@. Doing so
    -- requires that 'caseOpenABT' is part of the class so that we
    -- can push whatever annotations down over one single level of
    -- 'Open', rather than pushing over all of them at once and
    -- then needing to reconstruct all but the first one.
    Open :: {-# UNPACK #-} !Variable -> !(View abt a) -> View abt a


instance Functor1 View where
    fmap1 f (Syn  t)   = Syn (fmap1 f t)
    fmap1 _ (Var  x p) = Var  x p
    fmap1 f (Open x e) = Open x (fmap1 f e)


instance Show1 abt => Show1 (View abt) where
    showsPrec1 p (Syn t) =
        showParen (p > 9)
            ( showString "Syn "
            . showsPrec1 11 t
            )
    showsPrec1 p (Var x s) =
        showParen (p > 9)
            ( showString "Var "
            . showsPrec  11 x
            . showString " "
            . showsPrec 11 s
            )
    showsPrec1 p (Open x v) =
        showParen (p > 9)
            ( showString "Open "
            . showsPrec  11 x
            . showString " "
            . showsPrec1 11 v
            )

instance Show1 abt => Show (View abt a) where
    showsPrec = showsPrec1
    show      = show1


-- TODO: neelk includes 'subst' in the signature. Any reason we should?
class ABT (abt :: Hakaru -> *) where
    syn  :: AST abt a          -> abt a
    var  :: Variable -> Sing a -> abt a
    open :: Variable -> abt  a -> abt a

    -- TODO: better name. "unopen"? "caseOpen"? "fromOpen"?
    -- | Assume the ABT is 'Open' and then project out the components.
    -- If the ABT is not 'Open', then this function will throw an
    -- 'ExpectedOpenException' error.
    caseOpenABT :: abt a -> (Variable -> abt a -> r) -> r

    -- See note about exposing 'View', 'viewABT', and 'unviewABT'.
    -- We could replace 'viewABT' with a case-elimination version...
    viewABT  :: abt a -> View abt a

    freeVars :: abt a -> Set Variable
    -- TODO: add a function for checking alpha-equivalence? Other stuff?
    -- TODO: does it make sense to have the functions for generating fresh variable names here? or does that belong in a separate class?


-- See note about exposing 'View', 'viewABT', and 'unviewABT'
unviewABT :: (ABT abt) => View abt a -> abt a
unviewABT (Syn  t)   = syn  t
unviewABT (Var  x p) = var  x p
unviewABT (Open x v) = open x (unviewABT v)


data ABTException
    = ExpectedOpenException
    | ExpectedVarSynException
    | SubstitutionTypeError
    deriving (Show, Typeable)

instance Exception ABTException


-- | Assume the ABT is not 'Open' and then project out the components.
-- If the ABT is in fact 'Open', then this function will throw an
-- 'ExpectedVarSynException' error.
caseVarSynABT
    :: (ABT abt)
    => abt a
    -> (Variable -> Sing a -> r)
    -> (AST abt a          -> r)
    -> r
caseVarSynABT e var_ syn_ =
    case viewABT e of
    Syn  t   -> syn_ t
    Var  x p -> var_ x p
    Open _ _ -> throw ExpectedVarSynException -- TODO: add call-site info


----------------------------------------------------------------
-- | A trivial ABT with no annotations. The 'freeVars' method is
-- very expensive for this ABT, because we have to traverse the
-- term every time we want to get it. Use 'FreeVarsABT' to fix this.
newtype TrivialABT (a :: Hakaru) =
    TrivialABT (View TrivialABT a)

instance ABT TrivialABT where
    syn  t                = TrivialABT (Syn  t)
    var  x p              = TrivialABT (Var  x p)
    open x (TrivialABT v) = TrivialABT (Open x v)

    caseOpenABT (TrivialABT v) k =
        case v of
        Open x v' -> k x (TrivialABT v')
        _         -> throw ExpectedOpenException -- TODO: add info about the call-site

    viewABT (TrivialABT v) = v

    freeVars = go . viewABT
        where
        go (Syn  t)   = foldMap1 freeVars t
        go (Var  x _) = Set.singleton x
        go (Open x v) = Set.delete x (go v)


instance Show1 TrivialABT where
    {-
    -- Print the concrete data constructors:
    showsPrec1 p (TrivialABT v) =
        showParen (p > 9)
            ( showString "TrivialABT "
            . showsPrec1 11 v
            )
    -}
    -- Do something a bit prettier. (Because we print the smart
    -- constructors, this output can also be cut-and-pasted to work
    -- for any ABT instance.)
    showsPrec1 p (TrivialABT (Syn t)) =
        showParen (p > 9)
            ( showString "syn "
            . showsPrec1 11 t
            )
    showsPrec1 p (TrivialABT (Var x s)) =
        showParen (p > 9)
            ( showString "var "
            . showsPrec  11 x
            . showString " "
            . showsPrec 11 s
            )
    showsPrec1 p (TrivialABT (Open x v)) =
        showParen (p > 9)
            ( showString "open "
            . showsPrec  11 x
            . showString " "
            . showsPrec1 11 (TrivialABT v) -- HACK: use caseOpenABT
            )

instance Show (TrivialABT a) where
    showsPrec = showsPrec1
    show      = show1

----------------------------------------------------------------
-- TODO: replace @Set Variable@ with @Map Variable (Hakaru Star)@;
-- though that belongs more in the type-checking than in this
-- FreeVarsABT itself...
--
-- TODO: generalize this pattern for any monoidal annotation?
-- TODO: does keeping the set lazy allow us to use 'binder'? At what performance cost?
--
-- | An ABT which keeps track of free variables. The 'freeVars'
-- method is /O(1)/ for this ABT. N.B., the memoized set of free
-- variables is lazy so that we can tie-the-knot in 'binder'
-- without interfering with our memos.
data FreeVarsABT (a :: Hakaru)
    = FreeVarsABT (Set Variable) !(View FreeVarsABT a)
    -- N.B., Set is a monoid with {Set.empty; Set.union; Set.unions}
    -- For a lot of code, the other component ordering would be
    -- nicer; but this ordering gives a more intelligible Show instance.

instance ABT FreeVarsABT where
    syn  t                    = FreeVarsABT (foldMap1 freeVars t) (Syn  t)
    var  x p                  = FreeVarsABT (Set.singleton x)     (Var  x p)
    open x (FreeVarsABT xs v) = FreeVarsABT (Set.delete x xs)     (Open x v)

    caseOpenABT (FreeVarsABT xs v) k =
        case v of
        Open x v' -> k x (FreeVarsABT (Set.insert x xs) v') -- HACK: the variable @x@ doesn't necessarily occur in @v'@! But the only way to be strictly correct is to go back to the non-recursive View, and pay the cost of keeping all thise duplicate Sets around... I suppose we could add a chain of Bools to FreeVarsABT, keeping track for each variable bound by Open whether it actually occured or not...
        _         -> throw ExpectedOpenException -- TODO: add info about the call-site

    viewABT  (FreeVarsABT _  v) = v

    freeVars (FreeVarsABT xs _) = xs


instance Show1 FreeVarsABT where
    showsPrec1 p (FreeVarsABT xs v) =
        showParen (p > 9)
            ( showString "FreeVarsABT "
            . showsPrec  11 xs
            . showString " "
            . showsPrec1 11 v
            )

instance Show (FreeVarsABT a) where
    showsPrec = showsPrec1
    show      = show1


----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: something smarter
freshen :: Variable -> Set Variable -> Variable
freshen x xs
    | x `Set.member` xs = freshen (prime x) xs
    | otherwise         = x


-- | Rename a free variable. Does nothing if the variable is bound.
rename :: forall abt a. (ABT abt) => Variable -> Variable -> abt a -> abt a
rename x y = start
    where
    start :: forall b. abt b -> abt b
    start e = loop e (viewABT e)

    -- TODO: is it actually worth passing around the @e@? Benchmark.
    loop :: forall b. abt b -> View abt b -> abt b
    loop _ (Syn t)  = syn (fmap1 start t)
    loop e (Var z p)
        | x == z    = var y p
        | otherwise = e
    loop e (Open z v)
        | x == z    = e
        | otherwise = open z (loop (caseOpenABT e $ const id) v)


-- | Perform capture-avoiding substitution. This function will
-- either preserve type-safety or else throw an 'SubstitutionTypeError'.
-- N.B., to ensure timely throwing of exceptions, the 'AST' and
-- 'ABT' should have strict 'fmap1' definitions.
subst
    :: forall abt a b
    .  (SingI a, ABT abt)
    => Variable
    -> abt a
    -> abt b
    -> abt b
subst x e = start
    where
    toSing :: (SingI c) => proxy c -> Sing c
    toSing _ = sing
    
    start :: forall c. abt c -> abt c
    start f = loop f (viewABT f)

    -- TODO: is it actually worth passing around the @f@? Benchmark.
    loop :: forall c. abt c -> View abt c -> abt c
    loop _ (Syn t)    = syn (fmap1 start t)
    loop f (Var z p)
        | x == z      =
            case jmEq p (toSing e) of
            Just Refl -> e
            Nothing   -> throw SubstitutionTypeError
        | otherwise   = f
    loop f (Open z _)
        | x == z      = f
        | otherwise   =
            -- TODO: even if we don't come up with a smarter way
            -- of freshening variables, it'd be better to just pass
            -- both sets to 'freshen' directly and then check them
            -- each; rather than paying for taking their union every
            -- time we go under a binder like this.
            let z' = freshen z (freeVars e `mappend` freeVars f) in
            -- HACK: the 'rename' function requires an ABT not a
            -- View, so we have to use 'caseOpenABT' to give its
            -- input and then 'viewABT' to discard the topmost
            -- annotation. We really should find a way to eliminate
            -- that overhead.
            caseOpenABT f $ \_ f' ->
                open z' (loop f' . viewABT $ rename z z' f')


----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: Memoizing the highest bound seen so far (from the bottom-up)
-- breaks our ability to tie-the-knot in 'binder'. However, when
-- it comes to program transformations, it might make sense to
-- memoize the largest binder the transformation passes under (cf.,
-- the discussion in the paper about program transformations). Of
-- course, we could also use some Locally Nameless style approach
-- to deal with that issue...

class Bindable (ast :: Hakaru -> *) where
    -- | Return the largest 'varID' of variable /binding sites/.
    -- N.B., this should return 0 for the bound variables themselves.
    -- For performance, don't traverse into the body under those
    -- binders. (If all terms are constructed via 'binder', then
    -- soundness is guaranteed without needing to traverse under
    -- binders.)
    bound :: ast a -> Nat


-- For multibinders (i.e., nested uses of Open) we recurse through
-- the whole binder, just to be sure. However, we should be able
-- to just look at the first binder, since multibinders will need
-- to be constructed from multiple calls to 'binder'.
-- TODO: check correctness of just returning the topmost binder.
boundView :: Bindable abt => View abt a -> Nat
boundView = go 0
    where
    go 0 (Syn  t)   = bound t
    go n (Syn  _)   = n -- Don't go under binders
    go n (Var  _ _) = n
    go n (Open x v) = go (n `max` varID x) v

instance Bindable TrivialABT where
    bound = boundView . viewABT

instance Bindable FreeVarsABT where
    bound = boundView . viewABT


-- HACK: can't use 'foldMap(1)' unless we newtype wrap up the Nats to say which monoid we mean.
-- N.B., the Prelude's 'maximum' throws an error on empty lists!
maximumBound :: (Bindable ast) => [ast a] -> Nat
maximumBound = F.foldl' (\n e -> n `max` bound e) 0

maximumBound2 :: (Bindable ast) => [(ast a, ast b)] -> Nat
maximumBound2 = F.foldl' (\n (e1,e2) -> n `max` bound e1 `max` bound e2) 0

maximumBoundBranch :: (Bindable ast) => [Branch a ast b] -> Nat
maximumBoundBranch = F.foldl' (\n b -> n `max` bound (branchBody b)) 0

-- N.B., we needn't traverse into any type annotations, since we
-- don't have dependent types, hence no term variables can appear
-- in the types.
instance Bindable abt => Bindable (AST abt) where
    bound (Lam_        _  e)     = bound e
    bound (App_        e1 e2)    = bound e1 `max` bound e2
    bound (Let_        e1 e2)    = bound e1 `max` bound e2
    bound (Fix_        e)        = bound e
    bound (Ann_        _  e)     = bound e
    bound (PrimOp_     _)        = 0
    bound (NaryOp_     _  es)    = maximumBound (F.toList es)
    bound (Value_ _)             = 0
    bound (CoerceTo_   _  e)     = bound e
    bound (UnsafeFrom_ _  e)     = bound e
    bound (Array_      e1 e2)    = bound e1 `max` bound e2
    bound (Datum_      d)        = bound d
    bound (Case_       e  bs)    = bound e  `max` maximumBoundBranch bs
    bound (Measure_    _)        = 0
    bound (Bind_       e1 e2)    = bound e1 `max` bound e2
    bound (Superpose_  pes)      = maximumBound2 pes
    bound (Lub_        e1 e2)    = bound e1 `max` bound e2
    bound Bot_                   = 0

instance Bindable abt => Bindable (Datum abt) where
    bound (Roll       d)        = bound d
    bound Nil                   = 0
    bound (Cons       d1 d2)    = bound d1 `max` bound d2
    bound (Zero       d)        = bound d
    bound (Succ       d)        = bound d
    bound (Konst      e)        = bound e
    bound (Ident      e)        = bound e


-- | A combinator for defining a HOAS-like API for our syntax.
-- Because our 'AST' is first-order, we cannot actually have any
-- exotic terms in our language. In principle, this function could
-- be used to do exotic things when constructing those non-exotic
-- terms; however, trying to do anything other than change the
-- variable's name hint will cause things to explode (since it'll
-- interfere with our tying-the-knot).
binder
    :: (ABT abt, Bindable abt)
    => (Variable -> abt b -> r) -- ^ The binder's data constructor
    -> String                   -- ^ The variable's name hint
    -> Sing a                   -- ^ The variable's type
    -> (abt a -> abt b)         -- ^ Buid the binder's body from a variable
    -> r
binder cons name typ hoas = cons x body
    where
    body = hoas (var x typ)
    x    = Variable name (bound body + 1)

----------------------------------------------------------------
----------------------------------------------------------- fin.
