{-# LANGUAGE CPP
           , RankNTypes
           , ScopedTypeVariables
           , GADTs
           , StandaloneDeriving
           , DeriveDataTypeable
           , DataKinds
           , PolyKinds
           , TypeOperators
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.27
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
-- adding variables and binding; and each 'ABT' type (1) provides
-- some additional annotations at each recursion site, and then (2)
-- ties the knot to produce the recursive trees. For an introduction
-- to this technique\/approach, see:
--
--    * <http://semantic-domain.blogspot.co.uk/2015/03/abstract-binding-trees.html>
--    * <http://semantic-domain.blogspot.co.uk/2015/03/abstract-binding-trees-addendum.html>
--    * <http://winterkoninkje.dreamwidth.org/103978.html>
--
-- TODO: simultaneous multiple substitution
-- TODO: move all the variable stuff out to a separate module that this one depends on.
----------------------------------------------------------------
module Language.Hakaru.Syntax.ABT
    (
    -- * Our basic notion of variables.
      Variable(..)
    , varEq
    , VarEqTypeError(..)
    , SomeVariable(..)
    -- ** Some helper types for \"heaps\", \"environments\", etc
    , Assoc(..)
    , Assocs(..)
    , emptyAssocs
    , insertAssoc
    , lookupAssoc
    , resolveVar

    -- * The abstract binding tree interface
    -- See note about exposing 'View', 'viewABT', and 'unviewABT'
    , View(..)
    , unviewABT
    , ABT(..)
    , caseVarSyn
    , binds
    -- ** Capture avoiding substitution for any 'ABT'
    , subst
    , substs
    -- ** Constructing first-order trees with a HOAS-like API
    -- cf., <http://comonad.com/reader/2014/fast-circular-substitution/>
    , binder
    {-
    -- *** Highly experimental
    , Hint(..)
    , multibinder
    -}
    -- ** Some ABT instances
    , TrivialABT()
    , MemoizedABT()
    ) where

import           Data.Typeable     (Typeable)
import           Data.Text         (Text)
import           Data.Set          (Set)
import qualified Data.Set          as Set
import           Data.IntMap       (IntMap)
import qualified Data.IntMap       as IM
import qualified Data.Foldable     as F
import           Data.Function     (on)
#if __GLASGOW_HASKELL__ < 710
import           Data.Monoid       (Monoid(..))
#endif
import           Control.Exception (Exception, throw)

import Language.Hakaru.Syntax.Nat
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.AST

----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: (definitely) parameterise the 'ABT' class over it's choice
-- of syntax (currently assumed to always be 'AST'). This way we
-- can reuse the ABT stuff for the untyped AST that symbol resolution
-- generates

-- TODO: (probably) parameterize the 'ABT' class over it's
-- implementation of 'Variable', so that after we're done constructing
-- terms with 'binder' we can make the varID strict\/unboxed.

-- TODO: (maybe) parameterize the 'ABT' class over it's implementation
-- of 'View' so that we can unpack the implementation of 'Variable'
-- into the 'Var' constructor. That is, the current version does
-- this unpacking, but if we parameterize the variable implementation
-- then we'd lose it; so this would allow us to regain it. Also,
-- if we do this, then 'MemoizedABT' could define it's own specialized
-- 'Bind' in order to keep track of whether bound variables occur
-- or not (for defining 'caseBind' precisely).

----------------------------------------------------------------
-- TODO: should we make this type abstract?


-- TODO: alas we need to keep the Sing in order to make 'subst'
-- typesafe... Is there any way to work around that? Maybe only
-- define substitution for well-typed ABTs (i.e., what we produce
-- via typechecking a plain ABT)? If we can manage to get rid of
-- the Sing, then 'binder' and 'multibinder' would become much
-- simpler. Alas, it looks like we also need it for 'inferType' to
-- be well-typed... How can we avoid that?
--
-- TODO: what are the overhead costs of storing a Sing? Would
-- it be cheaper to store the SingI dictionary (and a Proxy,
-- as necessary)?


-- | A variable is a triple of a unique identifier ('varID'), a
-- hint for how to display things to humans ('varHint'), and a type
-- ('varType'). Notably, the hint is only used for display purposes,
-- and the type is only used for typing purposes; thus, the 'Eq'
-- and 'Ord' instances only look at the unique identifier, completely
-- ignoring the other two components. However, the 'varEq' function
-- does take the type into consideration (but still ignores the
-- hint).
--
-- N.B., the unique identifier is lazy so that we can tie-the-knot
-- in 'binder'.
data Variable (a :: Hakaru) = Variable
    { varHint :: {-# UNPACK #-} !Text
    , varID   :: Nat -- N.B., lazy!
    , varType :: !(Sing a)
    }

-- TODO: instance Read (Variable a)

instance Show1 Variable where
    showsPrec1 p (Variable hint i typ) =
        showParen (p > 9)
            ( showString "Variable "
            . showsPrec  11 hint
            . showString " "
            . showsPrec  11 i
            . showString " "
            . showsPrec  11 typ
            )

instance Show (Variable a) where
    showsPrec = showsPrec1
    show      = show1


-- BUG: this may not be consistent with the interpretation chosen by 'varEq'
instance Eq (Variable a) where
    (==) = (==) `on` varID

-- BUG: this must be consistent with the 'Eq' instance, but should
-- also be consistent with the 'varEq' interpretation. In particular,
-- it's not clear how to make any Ord instance consistent with
-- interpretation #1 (unless we have some sort of `jmCompare` on
-- types!)
instance Ord (Variable a) where
    compare = compare `on` varID


-- TODO: so long as we don't go with interpretation #1 (because
-- that'd cause consistency issues with the 'Ord' instance) we could
-- simply use this to give a 'JmEq1' instance. Would help to minimize
-- the number of distinct concepts floating around...
--
-- | Compare to variables at possibly-different types. If the
-- variables are \"equal\", then they must in fact have the same
-- type. N.B., it is not entirely specified what this function
-- /means/ when two variables have the same 'varID' but different
-- 'varType'. However, so long as we use this function everywhere,
-- at least we'll be consistent.
--
-- Possible interpretations:
--
-- * We could /assume/ that when the 'varType's do not match the
-- variables are not equal. Upside: we can statically guarantee
-- that every variable is \"well-typed\" (by fiat). Downside: every
-- type has its own variable namespace, which is very confusing.
-- Also, the @Ord SomeVariable@ instance will be really difficult
-- to get right.
--
-- * We could /require/ that whenever two 'varID's match, their
-- 'varType's must also match. Upside: a single variable namespace.
-- Downside: if the types do not in fact match (e.g., the preprocessing
-- step for ensuring variable uniqueness is buggy), then we must
-- throw (or return) an 'VarEqTypeError' exception.
--
-- * We could /assert/ that whenever two 'varID's match, their
-- 'varType's must also match. Upsides: we get a single variable
-- namespace, and we get /O(1)/ equality checking. Downsides: if
-- the types do not in fact match, we'll probably segfault.
--
-- Whichever interpretation we choose, we must make sure that typing
-- contexts ('Cxt') and binding environments ('Env') behave
-- consistently.
varEq :: Variable a -> Variable b -> Maybe (TypeEq a b)
{-
-- Interpretation #1:
varEq x y =
    case jmEq1 (varType x) (varType y) of
    Just Refl | x == y -> Just Refl
    _                  -> Nothing
-}
-- Interpretation #2:
varEq x y
    | varID x == varID y =
        case jmEq1 (varType x) (varType y) of
        Just Refl -> Just Refl
        Nothing   -> throw (VarEqTypeError x y)
    | otherwise = Nothing
{-
-- Interpretation #3:
varEq x y
    | varID x == varID y = Just (unsafeCoerce Refl)
    | otherwise          = Nothing
-}


-- BUG: haddock doesn't like annotations on GADT constructors. So
-- here we'll avoid using the GADT syntax, even though it'd make
-- the data type declaration prettier\/cleaner.
-- <https://github.com/hakaru-dev/hakaru/issues/6>
data VarEqTypeError
    = forall a b. VarEqTypeError
        {-# UNPACK #-} !(Variable a)
        {-# UNPACK #-} !(Variable b)
    deriving (Typeable)

deriving instance Show VarEqTypeError
instance Exception VarEqTypeError

----------------------------------------------------------------
-- TODO: switch to using 'Some' itself

-- BUG: haddock doesn't like annotations on GADT constructors. So
-- here we'll avoid using the GADT syntax, even though it'd make
-- the data type declaration prettier\/cleaner.
-- <https://github.com/hakaru-dev/hakaru/issues/6>
--
-- | Hide an existentially quantified parameter to 'Variable'.
data SomeVariable
    = forall a. SomeVariable
        {-# UNPACK #-} !(Variable a)

instance Eq SomeVariable where
    SomeVariable x == SomeVariable y =
        case varEq x y of
        Just Refl -> True
        Nothing   -> False

-- N.B., This implementation assumes that 'varEq' uses either the second or third interpretation! If it uses the first interpretation then this is wrong!
instance Ord SomeVariable where
    SomeVariable x `compare` SomeVariable y =
        varID x `compare` varID y

-- TODO: instance Read SomeVariable
deriving instance Show SomeVariable


----------------------------------------------------------------
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
data View :: ([Hakaru] -> Hakaru -> *) -> [Hakaru] -> Hakaru -> * where
    -- BUG: haddock doesn't like annotations on GADT constructors
    -- <https://github.com/hakaru-dev/hakaru/issues/6>

    Syn  :: !(AST abt a) -> View abt '[] a

    Var  :: {-# UNPACK #-} !(Variable a) -> View abt '[] a

    -- N.B., this constructor is recursive, thus minimizing the
    -- memory overhead of whatever annotations our ABT stores (we
    -- only annotate once, at the top of a chaing of 'Bind's, rather
    -- than before each one). However, in the 'ABT' class, we provide
    -- an API as if things went straight back to @abt@. Doing so
    -- requires that 'caseBind' is part of the class so that we
    -- can push whatever annotations down over one single level of
    -- 'Bind', rather than pushing over all of them at once and
    -- then needing to reconstruct all but the first one.
    Bind
        :: {-# UNPACK #-} !(Variable a)
        -> !(View abt xs b)
        -> View abt (a ': xs) b


instance Functor22 View where
    fmap22 f (Syn  t)   = Syn (fmap21 f t)
    fmap22 _ (Var  x)   = Var  x
    fmap22 f (Bind x e) = Bind x (fmap22 f e)


instance Show2 abt => Show2 (View abt) where
    showsPrec2 p (Syn t) =
        showParen (p > 9)
            ( showString "Syn "
            . showsPrec1 11 t
            )
    showsPrec2 p (Var x) =
        showParen (p > 9)
            ( showString "Var "
            . showsPrec1 11 x
            )
    showsPrec2 p (Bind x v) =
        showParen (p > 9)
            ( showString "Bind "
            . showsPrec1 11 x
            . showString " "
            . showsPrec2 11 v
            )

instance Show2 abt => Show1 (View abt xs) where
    showsPrec1 = showsPrec2
    show1      = show2
    
instance Show2 abt => Show (View abt xs a) where
    showsPrec = showsPrec1
    show      = show1


-- TODO: neelk includes 'subst' as a method. Any reason we should?
-- TODO: jon includes instantiation as a method. Any reason we should?
class ABT (abt :: [Hakaru] -> Hakaru -> *) where
    -- Smart constructors for building a 'View' and then injecting it into the @abt@.
    syn  :: AST abt  a -> abt '[] a
    var  :: Variable a -> abt '[] a
    bind :: Variable a -> abt xs b -> abt (a ': xs) b

    -- TODO: better name. "unbind"? "fromBind"?
    --
    -- When the left side is defined, we have the following laws:
    -- > caseBind e bind == e
    -- > caseBind (bind x e) k == k x (unviewABT $ viewABT e)
    -- However, we do not necessarily have the following:
    -- > caseBind (bind x e) k == k x e
    -- because the definition of 'caseBind' for 'MemoizedABT'
    -- is not exact.
    --
    -- | Since the first argument to @abt@ is not @'[]@, we know
    -- it must be 'Bind'. So we do case analysis on that constructor,
    -- pushing the annotation down one binder (but not over the
    -- whole recursive 'View' layer).
    caseBind :: abt (x ': xs) a -> (Variable x -> abt xs a -> r) -> r

    -- See note about exposing 'View', 'viewABT', and 'unviewABT'.
    -- We could replace 'viewABT' with a case-elimination version...
    viewABT  :: abt xs a -> View abt xs a

    -- TODO: use our own VarSet type (e.g., @IntMap Variable@) instead of @Set Variable@?
    freeVars :: abt xs a -> Set SomeVariable

    -- | Return the largest 'varID' of /free/ variables. The default
    -- implementation is to take the maximum of 'freeVars'. This
    -- is part of the class in case you want to memoize it.
    --
    -- This function is used in order to generate guaranteed-fresh
    -- variables without the need for a name supply. In particular,
    -- it's used to ensure that the generated variable don't capture
    -- any free variables in the term.
    maxFree :: abt xs a -> Nat
    maxFree = maxVarID . freeVars

    -- | Return the largest 'varID' of variable /binding sites/
    -- (i.e., of variables bound by the 'Bind' constructor). N.B.,
    -- this should return 0 for /uses/ of the bound variables
    -- themselves. This is part of the class in case you want to
    -- memoize it.
    --
    -- This function is used in order to generate guaranteed-fresh
    -- variables without the need for a name supply. In particular,
    -- it's used to ensure that the generated variable won't be
    -- captured or shadowed by bindings already in the term.
    maxBind :: abt xs a -> Nat


    -- TODO: add a function for checking alpha-equivalence? Refreshing all variable IDs to be in some canonical form? Other stuff?


maxVarID :: Set SomeVariable -> Nat
maxVarID xs
    | Set.null xs = 0
    | otherwise   =
        case Set.findMax xs of
        SomeVariable x -> varID x


-- See note about exposing 'View', 'viewABT', and 'unviewABT'
unviewABT :: (ABT abt) => View abt xs a -> abt xs a
unviewABT (Syn  t)   = syn  t
unviewABT (Var  x)   = var  x
unviewABT (Bind x v) = bind x (unviewABT v)


-- | Since the first argument to @abt@ is @'[]@, we know it must
-- be either 'Syn' of 'Var'. So we do case analysis with those two
-- constructors.
caseVarSyn
    :: (ABT abt)
    => abt '[] a
    -> (Variable a -> r)
    -> (AST abt  a -> r)
    -> r
caseVarSyn e var_ syn_ =
    case viewABT e of
    Syn t -> syn_ t
    Var x -> var_ x


-- | Call 'bind' repeatedly.
binds :: (ABT abt) => List1 Variable xs -> abt ys b -> abt (xs ++ ys) b
binds Nil1         e = e
binds (Cons1 x xs) e = bind x (binds xs e)


----------------------------------------------------------------
----------------------------------------------------------------
-- | A trivial ABT with no annotations.
--
-- The 'Show' instance does not expose the raw underlying data
-- types, but rather prints the smart constructors 'var', 'syn',
-- and 'bind'. This makes things prettier, but also means that if
-- you paste the string into a Haskell file you can use it for any
-- 'ABT' instance.
--
-- The 'freeVars', 'maxFree', and 'maxBind' methods are all very
-- expensive for this ABT, because we have to traverse the term
-- every time we want to call them. The 'MemoizedABT' implementation
-- fixes this.
--
-- N.B., The 'maxBind' method is not as expensive as it could be.
-- As a performance hack, we do not traverse under binders. If every
-- binding form is generated by using 'binder', then this is in
-- fact sound because all nested binders will bind smaller variables.
-- However, If you generate any binding forms manually, then you
-- can break things so that 'maxBind' returns an incorrect answer.
newtype TrivialABT (xs :: [Hakaru]) (a :: Hakaru) =
    TrivialABT (View TrivialABT xs a)

instance ABT TrivialABT where
    syn  t                = TrivialABT (Syn  t)
    var  x                = TrivialABT (Var  x)
    bind x (TrivialABT v) = TrivialABT (Bind x v)

    caseBind (TrivialABT v) k =
        case v of
        Bind x v' -> k x (TrivialABT v')

    viewABT (TrivialABT v) = v

    freeVars = go . viewABT
        where
        go :: View TrivialABT xs a -> Set SomeVariable
        go (Syn  t)   = foldMap21 freeVars t
        go (Var  x)   = Set.singleton (SomeVariable x)
        go (Bind x v) = Set.delete (SomeVariable x) (go v)

    maxBind = go 0 . viewABT
        where
        -- For multibinders (i.e., nested uses of Bind) we recurse
        -- through the whole binder, just to be sure. However, we should
        -- be able to just look at the first binder, since whenever we
        -- figure out how to do multibinders we can prolly arrange for
        -- the first one to be the largest.
        go :: (ABT abt) => Nat -> View abt xs a -> Nat
        go 0 (Syn  t)   = unMaxNat $ foldMap21 (MaxNat . maxBind) t
        go n (Syn  _)   = n -- Don't go under binders
        go n (Var  _)   = n -- Don't look at variable *uses*
        go n (Bind x v) = go (n `max` varID x) v
        

instance Show2 TrivialABT where
    {-
    -- Print the concrete data constructors:
    showsPrec2 p (TrivialABT v) =
        showParen (p > 9)
            ( showString "TrivialABT "
            . showsPrec1 11 v
            )
    -}
    -- Do something a bit prettier. (Because we print the smart
    -- constructors, this output can also be cut-and-pasted to work
    -- for any ABT instance.)
    showsPrec2 p (TrivialABT (Syn t)) =
        showParen (p > 9)
            ( showString "syn "
            . showsPrec1 11 t
            )
    showsPrec2 p (TrivialABT (Var x)) =
        showParen (p > 9)
            ( showString "var "
            . showsPrec1 11 x
            )
    showsPrec2 p (TrivialABT (Bind x v)) =
        showParen (p > 9)
            ( showString "bind "
            . showsPrec1 11 x
            . showString " "
            . showsPrec1 11 (TrivialABT v) -- HACK: use caseBind
            )

instance Show1 (TrivialABT xs) where
    showsPrec1 = showsPrec2
    show1      = show2

instance Show (TrivialABT xs a) where
    showsPrec = showsPrec1
    show      = show1

----------------------------------------------------------------
-- TODO: replace @Set Variable@ with @Map Variable Hakaru@ or @Map
-- Variable (Some (Sing :: Hakaru -> *))@ though that belongs more
-- in a different ABT instance produced by type-checking, rather
-- than belonging here...
--
-- TODO: replace @Set Variable@ with @Map Variable Nat@ where the
-- Nat is the number of times the variable occurs. That way, we can
-- tell when a bound variable is unused or only used only once (and
-- hence performing beta\/let reduction would be a guaranteed win),
-- and if it's used more than once then we can use the number of
-- occurances in our heuristic for deciding whether reduction would
-- be a win or not.
--
-- TODO: generalize this pattern for any monoidal annotation?
-- TODO: what is the performance cost of letting 'memoizedFreeVars' be lazy? Is it okay to lose the ability to use 'binder' in order to shore that up?


-- WARNING: in older versions of the library, there was an issue
-- about the memoization of 'maxBind' breaking our ability to
-- tie-the-knot in 'binder'. Everything seems to work now, but it's
-- not entirely clear to me what changed...

-- | An ABT which memoizes 'freeVars', 'maxBind', and 'maxFree',
-- thereby making them take only /O(1)/ time.
--
-- N.B., the memoized set of free variables is lazy so that we can
-- tie-the-knot in 'binder' without interfering with our memos. The
-- memoized 'maxFree' must be lazy for the same reason.
data MemoizedABT (xs :: [Hakaru]) (a :: Hakaru) = MemoizedABT
    { memoizedFreeVars :: Set SomeVariable -- N.B., lazy!
    , memoizedMaxFree  :: Nat -- N.B., lazy!
    , memoizedMaxBind  :: {-# UNPACK #-} !Nat
    , memoizedView     :: !(View MemoizedABT xs a)
    }
    -- N.B., Set is a monoid with {Set.empty; Set.union; Set.unions}
    -- For a lot of code, the other component ordering would be
    -- nicer; but this ordering gives a more intelligible Show instance.


instance ABT MemoizedABT where
    syn t =
        MemoizedABT
            (foldMap21 freeVars t)
            (unMaxNat $ foldMap21 (MaxNat . maxFree) t)
            (unMaxNat $ foldMap21 (MaxNat . maxBind) t)
            (Syn t)

    var x =
        MemoizedABT
            (Set.singleton $ SomeVariable x)
            (varID x)
            0
            (Var x)

    bind x (MemoizedABT xs _ mb v) =
        let xs' = Set.delete (SomeVariable x) xs
        in MemoizedABT
            xs'
            (maxVarID xs')
            (varID x `max` mb)
            (Bind x v)

    -- N.B., when we go under the binder, the variable @x@ may not
    -- actually be used, but we add it to the set of freeVars
    -- anyways. The reasoning is thus: this function is mainly used
    -- in defining 'subst', and for that purpose it's important to
    -- track all the variables which /could be/ free, so that we
    -- can freshen appropriately. It may be safe to not include @x@
    -- when @x@ is not actually used in @v'@, but it's best not to
    -- risk it. Moreover, once we add support for open terms (i.e.,
    -- truly-free variables) then we'll need to account for the
    -- fact that the variable @x@ may come to be used in the grounding
    -- of the open term, even though it's not used in the part of
    -- the term we already know. Similarly, the true 'maxBind' may
    -- be lower now that we're going under this binding; but keeping
    -- it the same is an always valid approximation.
    --
    -- TODO: we could actually compute things exactly, similar to how we do it in 'syn'; but unclear if that's really worth it...
    caseBind (MemoizedABT xs mf mb v) k =
        case v of
        Bind x v' ->
            k x $ MemoizedABT
                (Set.insert (SomeVariable x) xs)
                (varID x `max` mf)
                mb
                v'

    viewABT  = memoizedView
    freeVars = memoizedFreeVars
    maxFree  = memoizedMaxFree
    maxBind  = memoizedMaxBind


instance Show2 MemoizedABT where
    showsPrec2 p (MemoizedABT xs mf mb v) =
        showParen (p > 9)
            ( showString "MemoizedABT "
            . showsPrec  11 xs
            . showString " "
            . showsPrec  11 mf
            . showString " "
            . showsPrec  11 mb
            . showString " "
            . showsPrec1 11 v
            )

instance Show1 (MemoizedABT xs) where
    showsPrec1 = showsPrec2
    show1      = show2

instance Show (MemoizedABT xs a) where
    showsPrec = showsPrec1
    show      = show1

----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: should we export 'freshen' and 'rename'?

-- TODO: do something smarter
-- | If the variable is in the set, then construct a new one which
-- isn't (but keeping the same hint and type as the old variable).
-- If it isn't in the set, then just return it.
freshen :: Variable a -> Set SomeVariable -> Variable a
freshen x xs
    | SomeVariable x `Set.member` xs =
        let i = 1 + maxVarID xs in i `seq` x{varID = i}
    | otherwise = x


-- | Rename a free variable. Does nothing if the variable is bound.
rename
    :: forall abt a xs b
    .  (ABT abt)
    => Variable a
    -> Variable a
    -> abt xs b
    -> abt xs b
rename x y = start
    where
    start :: forall xs' b'. abt xs' b' -> abt xs' b'
    start e = loop e (viewABT e)

    -- TODO: is it actually worth passing around the @e@? Benchmark.
    loop :: forall xs' b'. abt xs' b' -> View abt xs' b' -> abt xs' b'
    loop _ (Syn t) = syn $! fmap21 start t
    loop e (Var z) =
        case varEq x z of
        Just Refl -> var y
        Nothing   -> e
    loop e (Bind z v) =
        case varEq x z of
        Just Refl -> e
        Nothing   -> bind z $ loop (caseBind e $ const id) v


-- TODO: keep track of a variable renaming environment, and do renaming on the fly rather than traversing the ABT repeatedly.
--
-- TODO: make an explicit distinction between substitution in general vs instantiation of the top-level bound variable (i.e., the function of type @abt (x ': xs) a -> abt '[] x -> abt xs a@). cf., <http://hackage.haskell.org/package/abt>
--
-- | Perform capture-avoiding substitution. This function will
-- either preserve type-safety or else throw an 'VarEqTypeError'
-- (depending on which interpretation of 'varEq' is chosen). N.B.,
-- to ensure timely throwing of exceptions, the 'AST' and 'ABT'
-- should have strict 'fmap21' definitions.
subst
    :: forall abt a xs b
    .  (ABT abt)
    => Variable a
    -> abt '[] a
    -> abt xs b
    -> abt xs b
subst x e = start
    where
    start :: forall xs' b'. abt xs' b' -> abt xs' b'
    start f = loop f (viewABT f)

    -- TODO: is it actually worth passing around the @f@? Benchmark.
    loop :: forall xs' b'. abt xs' b' -> View abt xs' b' -> abt xs' b'
    loop _ (Syn t) = syn $! fmap21 start t
    loop f (Var z) =
        case varEq x z of
        Just Refl -> e
        Nothing   -> f
    loop f (Bind z _) =
        case varEq x z of
        Just Refl -> f
        Nothing   ->
            -- TODO: even if we don't come up with a smarter way
            -- of freshening variables, it'd be better to just pass
            -- both sets to 'freshen' directly and then check them
            -- each; rather than paying for taking their union every
            -- time we go under a binder like this.
            let z' = freshen z (freeVars e `mappend` freeVars f) in
            -- HACK: the 'rename' function requires an ABT not a
            -- View, so we have to use 'caseBind' to give its
            -- input and then 'viewABT' to discard the topmost
            -- annotation. We really should find a way to eliminate
            -- that overhead.
            caseBind f $ \_ f' ->
                bind z' . loop f' . viewABT $ rename z z' f'


-- TODO: verify that this works as advertised
-- | The parallel version of 'subst' for performing multiple substitutions at once.
substs
    :: forall abt xs a
    .  (ABT abt)
    => Assocs abt
    -> abt xs a
    -> abt xs a
substs rho0 = start rho0
    where
    fv0 = F.foldMap (\(Assoc _ e) -> freeVars e) (unAssocs rho0)
    
    start :: forall xs' a'. Assocs abt -> abt xs' a' -> abt xs' a'
    start rho e = loop rho e (viewABT e)

    loop :: forall xs' a'. Assocs abt -> abt xs' a' -> View abt xs' a' -> abt xs' a'
    loop rho _ (Syn t) = syn $! fmap21 (start rho) t
    loop rho e (Var x) =
        case IM.lookup (fromNat $ varID x) (unAssocs rho) of
        Nothing           -> e
        Just (Assoc y e') ->
            case varEq x y of
            Just Refl     -> e'
            Nothing       -> e
    loop rho e (Bind x _body) =
        case IM.lookup (fromNat $ varID x) (unAssocs rho) of
        Nothing          -> e
        Just (Assoc y _) ->
            case varEq x y of
            Just Refl ->
                let rho' = IM.delete (fromNat $ varID x) (unAssocs rho) in
                if IM.null rho'
                then e
                else caseBind e $ \_x body' ->
                        bind x . loop (Assocs rho') body' $ viewABT body'
            Nothing   ->
                -- TODO: even if we don't come up with a smarter way
                -- of freshening variables, it'd be better to just pass
                -- both sets to 'freshen' directly and then check them
                -- each; rather than paying for taking their union every
                -- time we go under a binder like this.
                let x' = freshen x (fv0 `mappend` freeVars e) in
                -- HACK: the 'rename' function requires an ABT not a
                -- View, so we have to use 'caseBind' to give its
                -- input and then 'viewABT' to discard the topmost
                -- annotation. We really should find a way to eliminate
                -- that overhead.
                caseBind e $ \_x body' ->
                    bind x' . loop rho body' . viewABT $ rename x x' body'


----------------------------------------------------------------
----------------------------------------------------------------
-- | A combinator for defining a HOAS-like API for our syntax.
-- Because our 'AST' is first-order, we cannot actually have any
-- exotic terms in our language. In principle, this function could
-- be used to do exotic things when constructing those non-exotic
-- terms; however, trying to do anything other than change the
-- variable's name hint will cause things to explode (since it'll
-- interfere with our tying-the-knot).
--
-- N.B., if you manually construct free variables and use them in
-- the body (i.e., via 'var'), they may become captured by the new
-- binding introduced here! This is inevitable since 'maxBind' never
-- looks at variable /use sites/; it only ever looks at /binding
-- sites/. On the other hand, if you manually construct a bound
-- variable (i.e., manually calling 'bind' yourself), then the new
-- binding introduced here will respect the old binding and avoid
-- that variable ID.
binder
    :: (ABT abt)
    => Text                     -- ^ The variable's name hint
    -> Sing a                   -- ^ The variable's type
    -> (abt '[] a -> abt xs b)  -- ^ Build the binder's body from a variable
    -> abt (a ': xs) b
binder hint typ hoas = bind x body
    where
    body = hoas (var x)
    x    = Variable hint (1 + maxBind body) typ
    -- N.B., cannot use 'maxFree' when deciding the 'varID' of @x@

{-
data Hint (a :: Hakaru)
    = Hint !Text !(Sing a)

instance Show1 Hint where
    showsPrec1 p (Hint x s) = showParen_01 p "Hint" x s

instance Show (Hint a) where
    showsPrec = showsPrec1
    show      = show1

data VS (a :: Hakaru)
    = VS {-# UNPACK #-} !Variable !(Sing a)

-- this typechecks, and it works!
-- BUG: but it seems fairly unusable. We must give explicit type signatures to any lambdas passed as the second argument, otherwise it complains about not knowing enough about the types in @xs@... Also, the uncurriedness of it isn't very HOAS-like
multibinder
    :: (ABT abt) => List1 Hint xs -> (List1 abt xs -> abt b) -> abt b
multibinder names hoas = binds vars body
    where
    vars = go 0 names
        where
        -- BUG: this puts the largest binder on the inside
        go :: Nat -> List1 Hint xs -> List1 VS xs
        go _ Nil                         = Nil
        go n (Cons (Hint name typ) rest) =
            Cons (VS (Variable name (maxBind body + n) typ) typ)
                ((go $! n + 1) rest)
    body = hoas (go vars)
        where
        go :: ABT abt => List1 VS xs -> List1 abt xs
        go Nil                    = Nil
        go (Cons (VS x typ) rest) = Cons (var x typ) (go rest)

    binds :: ABT abt => List1 VS xs -> abt a -> abt a
    binds Nil                  = id
    binds (Cons (VS x _) rest) = bind x . binds rest
-}

----------------------------------------------------------------
----------------------------------------------------------------
-- BUG: haddock doesn't like annotations on GADT constructors. So
-- here we'll avoid using the GADT syntax, even though it'd make
-- the data type declaration prettier\/cleaner.
-- <https://github.com/hakaru-dev/hakaru/issues/6>
--
-- | A pair of variable and term, both of the same Hakaru type.
data Assoc (abt :: [Hakaru] -> Hakaru -> *)
    = forall a. Assoc
        {-# UNPACK #-} !(Variable a)
        !(abt '[] a)


-- BUG: since multiple 'varEq'-distinct variables could have the
-- same ID, we should really have the elements be a list of
-- associations (or something more efficient; e.g., if 'Sing' is
-- hashable).
--
-- | A set of variable\/term associations.
--
-- N.B., the current implementation assumes 'varEq' uses either the
-- second or third interpretations; that is, it is impossible to
-- have a single 'varID' be shared by multiple variables (i.e., at
-- different types). If you really want the first interpretation,
-- then the implementation must be updated.
newtype Assocs abt = Assocs { unAssocs :: IntMap (Assoc abt) }

-- | The empty set of associations.
emptyAssocs :: Assocs abt
emptyAssocs = Assocs IM.empty

-- If we actually do have a list (etc) of variables for each ID,
-- and want to add the new binding to whatever old ones, then it
-- looks like there's no way to do that in one pass of both the
-- IntMap and the list.
--
-- | Add an association to the set of associations.
--
-- HACK: if the variable is already associated with some term then
-- we throw an error! In the future it'd be better to take some
-- sort of continuation to decide between (a) replacing the old
-- binding, (b) throwing an exception, or (c) safely wrapping the
-- result up with 'Maybe'
insertAssoc :: Assoc abt -> Assocs abt -> Assocs abt
insertAssoc v@(Assoc x _) (Assocs xs) =
    case IM.insertLookupWithKey (\_ v' _ -> v') (fromNat $ varID x) v xs of
    (Nothing, xs') -> Assocs xs'
    (Just _,  _)   -> error "insertAssoc: variable is already assigned!"


-- | Look up a variable and return the associated term.
--
-- N.B., this function is robust to all interpretations of 'varEq'.
lookupAssoc :: Variable a -> Assocs abt -> Maybe (abt '[] a)
lookupAssoc x (Assocs xs) = do
    Assoc x' e' <- IM.lookup (fromNat $ varID x) xs
    Refl        <- varEq x x'
    return e'
{-
-- for @Assocs abt = IntMap [Assoc abt]@ this should work:
lookupAssoc x (Assocs xss) =
    go x <$> IM.lookup (fromNat $ varID x) xss
    where
    go x []                 = Nothing
    go x (Assoc x' e' : xs) =
        case varEq x x' of
        Just Refl -> Just e'
        Nothing   -> go x xs
-}

-- TODO: Swap the argument order?
-- | If the expression is a variable, then look it up. Recursing
-- until we can finally return some syntax.
resolveVar
    :: (ABT abt)
    => abt '[] a
    -> Assocs abt
    -> Either (Variable a) (AST abt a)
resolveVar e xs =
    flip (caseVarSyn e) Right $ \x ->
        case lookupAssoc x xs of
        Just e' -> resolveVar e' xs
        Nothing -> Left x

----------------------------------------------------------------
----------------------------------------------------------- fin.
