{-# LANGUAGE CPP
           , GADTs
           , DataKinds
           , PolyKinds
           , FlexibleContexts
           , DeriveDataTypeable
           , ExistentialQuantification
           , UndecidableInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.29
-- |
-- Module      :  Language.Hakaru.Syntax.Variable
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- An implementation of variables, for use with "Language.Hakaru.Syntax.ABT".
----------------------------------------------------------------
module Language.Hakaru.Syntax.Variable
    (
    -- * Our basic notion of variables.
      Variable(..)
    , varEq
    , VarEqTypeError(..)
    -- ** Variables with existentially quantified types
    , KindOf
    , SomeVariable(..)
    , nextVarID
    
    -- * Some helper types for \"heaps\", \"environments\", etc
    , Assoc(..)
    , Assocs(..) -- TODO: hide the data constructors
    , emptyAssocs
    , singletonAssocs
    , toAssocs
    , insertAssoc
    , lookupAssoc
    ) where

import           Data.Proxy        (KProxy(..))
import           Data.Typeable     (Typeable)
import           Data.Text         (Text)
import           Data.Set          (Set)
import qualified Data.Set          as Set
import           Data.IntMap       (IntMap)
import qualified Data.IntMap       as IM
import           Data.Function     (on)
import           Control.Exception (Exception, throw)
#if __GLASGOW_HASKELL__ < 710
import           Data.Monoid       (Monoid(..))
#endif

import Language.Hakaru.Syntax.Nat
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.Sing

----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: should we make this type abstract, or type-class it?

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
data Variable (a :: k) = Variable
    { varHint :: {-# UNPACK #-} !Text
    , varID   :: Nat -- N.B., lazy!
    , varType :: !(Sing a)
    }

-- TODO: instance Read (Variable a)

-- HACK: this requires UndecidableInstances
instance Show1 (Sing :: k -> *) => Show1 (Variable :: k -> *) where
    showsPrec1 p (Variable hint i typ) =
        showParen (p > 9)
            ( showString "Variable "
            . showsPrec  11 hint
            . showString " "
            . showsPrec  11 i
            . showString " "
            . showsPrec1 11 typ
            )

instance Show (Sing a) => Show (Variable a) where
    showsPrec p (Variable hint i typ) =
        showParen (p > 9)
            ( showString "Variable "
            . showsPrec  11 hint
            . showString " "
            . showsPrec  11 i
            . showString " "
            . showsPrec  11 typ
            )

-- BUG: these may not be consistent with the interpretation chosen by 'varEq'
instance Eq1 Variable where
    eq1 = (==) `on` varID

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
-- contexts, binding environments, and so on all behave consistently.
varEq
    :: (Show1 (Sing :: k -> *), JmEq1 (Sing :: k -> *))
    => Variable (a :: k)
    -> Variable (b :: k)
    -> Maybe (TypeEq a b)
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


-- TODO: is there any reason we ought to parameterize 'VarEqTypeError'
-- by the kind of the variables it closes over? Packaging up the
-- dictionaries seems fine for the 'Show' and 'Exception' instances,
-- but maybe elsewhere?
--
-- | An exception type for if we need to throw an error when two
-- variables do not have an equal 'varType'. This is mainly used
-- when 'varEq' chooses the second interpretation.
data VarEqTypeError where
    VarEqTypeError
        :: (Show1 (Sing :: k -> *), JmEq1 (Sing :: k -> *))
        => {-# UNPACK #-} !(Variable (a :: k))
        -> {-# UNPACK #-} !(Variable (b :: k))
        -> VarEqTypeError
    deriving (Typeable)

instance Show VarEqTypeError where
    showsPrec p (VarEqTypeError x y) =
        showParen (p > 9)
            ( showString "VarEqTypeError "
            . showsPrec1 11 x
            . showString " "
            . showsPrec1 11 y
            )

instance Exception VarEqTypeError


----------------------------------------------------------------
-- TODO: switch to using 'Some1' itself? Maybe no longer a good idea, due to the need for the kind parameter...

-- | Hide an existentially quantified parameter to 'Variable'.
--
-- Because the 'Variable' type is poly-kinded, we need to be careful
-- not to erase too much type\/kind information. Thus, we parameterize
-- the 'SomeVariable' type by the /kind/ of the type we existentially
-- quantify over. This is necessary for giving 'Eq' and 'Ord'
-- instances since we can only compare variables whose types live
-- in the same kind.
--
-- N.B., the 'Ord' instance assumes that 'varEq' uses either the
-- second or third interpretation. If 'varEq' uses the first
-- interpretation then, the 'Eq' instance (which uses 'varEq') will
-- be inconsistent with the 'Ord' instance!
data SomeVariable kproxy where
    SomeVariable :: {-# UNPACK #-} !(Variable a) -> SomeVariable (KindOf a)


-- | Convenient synonym to refer to the kind of a type variable:
-- @type KindOf (a :: k) = ('KProxy :: KProxy k)@
type KindOf (a :: k) = ('KProxy :: KProxy k)


-- This instance requires the 'JmEq1' and 'Show1' constraints because we use 'varEq'.
instance (JmEq1 (Sing :: k -> *), Show1 (Sing :: k -> *))
    => Eq (SomeVariable (kproxy :: KProxy k))
    where
    SomeVariable x == SomeVariable y =
        case varEq x y of
        Just Refl -> True
        Nothing   -> False


-- This instance requires the 'JmEq1' and 'Show1' constraints because 'Ord' requires the 'Eq' instance, which in turn requires those constraints.
instance (JmEq1 (Sing :: k -> *), Show1 (Sing :: k -> *))
    => Ord (SomeVariable (kproxy :: KProxy k))
    where
    SomeVariable x `compare` SomeVariable y =
        varID x `compare` varID y


-- TODO: instance Read SomeVariable


instance Show1 (Sing :: k -> *)
    => Show (SomeVariable (kproxy :: KProxy k))
    where
    showsPrec p (SomeVariable v) =
        showParen (p > 9)
            ( showString "SomeVariable "
            . showsPrec1 11 v
            )


-- TODO: switch from @Set SomeVariable@ to @VarSet = IntSet SomeVariable@
-- | Return the successor of the largest 'varID' of all the variables
-- in the set. Thus, we return zero for the empty set and non-zero
-- for non-empty sets.
nextVarID :: Set (SomeVariable kproxy) -> Nat
nextVarID xs
    | Set.null xs = 0
    | otherwise   =
        case Set.findMax xs of
        SomeVariable x -> 1 + varID x


----------------------------------------------------------------
-- BUG: haddock doesn't like annotations on GADT constructors. So
-- here we'll avoid using the GADT syntax, even though it'd make
-- the data type declaration prettier\/cleaner.
-- <https://github.com/hakaru-dev/hakaru/issues/6>
--
-- | A pair of variable and term, both of the same Hakaru type.
data Assoc (abt :: [k] -> k -> *)
    = forall (a :: k) . Assoc
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


singletonAssocs :: Variable a -> abt '[] a -> Assocs abt
singletonAssocs x e =
    Assocs $ IM.singleton (fromNat $ varID x) (Assoc x e)


toAssocs :: List1 Variable xs -> List1 (abt '[]) xs -> Assocs abt
toAssocs = \xs es -> Assocs (go xs es)
    where
    go :: List1 Variable xs -> List1 (abt '[]) xs -> IntMap (Assoc abt)
    -- BUG: GHC claims the patterns are non-exhaustive here
    go Nil1         Nil1         = IM.empty
    go (Cons1 x xs) (Cons1 e es) =
        IM.insert (fromNat $ varID x) (Assoc x e) (go xs es)
    go _ _ = error "toAssocs: the impossible happened"


instance Monoid (Assocs abt) where
    mempty = emptyAssocs
    mappend (Assocs xs) (Assocs ys) = Assocs (IM.union xs ys) -- TODO: remove bias; crash if conflicting definitions
    mconcat = Assocs . IM.unions . map unAssocs


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
lookupAssoc
    :: (Show1 (Sing :: k -> *), JmEq1 (Sing :: k -> *))
    => Variable (a :: k)
    -> Assocs abt
    -> Maybe (abt '[] a)
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

----------------------------------------------------------------
----------------------------------------------------------- fin.
