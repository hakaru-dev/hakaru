{-# LANGUAGE CPP
           , GADTs
           , DataKinds
           , PolyKinds
           , FlexibleContexts
           , DeriveDataTypeable
           , ExistentialQuantification
           , UndecidableInstances
           , ScopedTypeVariables
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.04.28
-- |
-- Module      :  Language.Hakaru.Syntax.Variable
-- Copyright   :  Copyright (c) 2016 the Hakaru team
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
    
    -- * Some helper types for \"heaps\", \"environments\", etc
    -- ** Typing environments; aka: sets of (typed) variables
    , VarSet(..)
    , emptyVarSet
    , singletonVarSet
    , fromVarSet
    , toVarSet
    , toVarSet1
    , varSetKeys
    , insertVarSet
    , deleteVarSet
    , memberVarSet
    , unionVarSet
    , intersectVarSet
    , sizeVarSet
    , nextVarID
    -- ** Substitutions; aka: maps from variables to their definitions
    , Assoc(..)
    , Assocs(..) -- TODO: hide the data constructors
    , emptyAssocs
    , singletonAssocs
    , fromAssocs
    , toAssocs
    , toAssocs1
    , insertAssoc
    , insertOrReplaceAssoc
    , insertAssocs
    , lookupAssoc
    , adjustAssoc
    , mapAssocs
    ) where

import           Data.Proxy        (KProxy(..))
import           Data.Typeable     (Typeable)
import           Data.Text         (Text)
import           Data.IntMap       (IntMap)
import qualified Data.IntMap       as IM
import           Data.Function     (on)
import           Control.Exception (Exception, throw)
#if __GLASGOW_HASKELL__ < 710
import           Data.Monoid       (Monoid(..))
#endif

#if !(MIN_VERSION_base(4,11,0))
import Data.Semigroup
#endif

import Data.Number.Nat
import Language.Hakaru.Syntax.IClasses
-- TODO: factor the definition of the 'Sing' type family out from
-- the instances, so that we can make our ABT stuff totally independent
-- of the definition of Hakaru's types.
import Language.Hakaru.Types.Sing

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
data SomeVariable (kproxy :: KProxy k) =
    forall (a :: k) . SomeVariable
        {-# UNPACK #-} !(Variable (a :: k))


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


----------------------------------------------------------------
-- | A set of (typed) variables.
newtype VarSet (kproxy :: KProxy k) =
    VarSet { unVarSet :: IntMap (SomeVariable kproxy) }

instance Show1 (Sing :: k -> *) => Show (VarSet (kproxy :: KProxy k)) where
    showsPrec p (VarSet xs) =
        showParen (p > 9)
            ( showString "VarSet "
            . showsPrec  11 xs
            )

instance (Eq (SomeVariable (kproxy :: KProxy k))) => Eq (VarSet kproxy) where
  VarSet s1 == VarSet s2 = s1 == s2

-- | Return the successor of the largest 'varID' of all the variables
-- in the set. Thus, we return zero for the empty set and non-zero
-- for non-empty sets.
nextVarID :: VarSet kproxy -> Nat
nextVarID (VarSet xs)
    | IM.null xs = 0
    | otherwise  =
        case IM.findMax xs of
        (_, SomeVariable x) -> 1 + varID x


emptyVarSet :: VarSet kproxy
emptyVarSet = VarSet IM.empty

singletonVarSet :: Variable a -> VarSet (KindOf a)
singletonVarSet x =
    VarSet $ IM.singleton (fromNat $ varID x) (SomeVariable x)

fromVarSet :: VarSet kproxy -> [SomeVariable kproxy]
fromVarSet (VarSet xs) = IM.elems xs

-- | Convert a list of variables into a variable set.
--
-- In the event that multiple variables have conflicting 'varID',
-- the latter variable will be kept. This generally won't matter
-- because we're treating the list as a /set/. In the cases where
-- it would matter, chances are you're going to encounter a
-- 'VarEqTypeError' sooner or later anyways.
toVarSet :: [SomeVariable kproxy] -> VarSet kproxy
toVarSet = VarSet . go IM.empty
    where
    go vars _ | vars `seq` False = error "toVarSet: the impossible happened"
    go vars []     = vars
    go vars (x:xs) = go (IM.insert (fromNat $ someVarID x) x vars) xs

    someVarID :: SomeVariable kproxy -> Nat
    someVarID (SomeVariable x) = varID x


-- | Convert a list of variables into a variable set.
--
-- In the event that multiple variables have conflicting 'varID',
-- the latter variable will be kept. This generally won't matter
-- because we're treating the list as a /set/. In the cases where
-- it would matter, chances are you're going to encounter a
-- 'VarEqTypeError' sooner or later anyways.
toVarSet1 :: List1 Variable (xs :: [k]) -> VarSet (kproxy :: KProxy k)
toVarSet1 = toVarSet . someVariables
    where
    -- N.B., this conversion maintains the variable ordering.
    someVariables
        :: List1 Variable (xs :: [k])
        -> [SomeVariable (kproxy :: KProxy k)]
    someVariables Nil1         = []
    someVariables (Cons1 x xs) = SomeVariable x : someVariables xs

instance Semigroup (VarSet kproxy) where
    VarSet xs <> VarSet ys = VarSet (IM.union xs ys) -- TODO: remove bias; crash if conflicting definitions

instance Monoid (VarSet kproxy) where
    mempty  = emptyVarSet
#if !(MIN_VERSION_base(4,11,0))
    mappend = (<>)
#endif
    mconcat = VarSet . IM.unions . map unVarSet

varSetKeys :: VarSet a -> [Int]
varSetKeys (VarSet set) = IM.keys set

insertVarSet :: Variable a -> VarSet (KindOf a) -> VarSet (KindOf a)
insertVarSet x (VarSet xs) =
    case
        IM.insertLookupWithKey
            (\_ v' _ -> v')
            (fromNat $ varID x)
            (SomeVariable x)
            xs
    of
    (Nothing, xs') -> VarSet xs'
    (Just _,  _)   -> error "insertVarSet: variable is already assigned!"


deleteVarSet :: Variable a -> VarSet (KindOf a) -> VarSet (KindOf a)
deleteVarSet x (VarSet xs) =
    --- BUG: use some sort of deleteLookupWithKey to make sure we got the right one...
    VarSet $ IM.delete (fromNat $ varID x) xs


memberVarSet
    :: (Show1 (Sing :: k -> *), JmEq1 (Sing :: k -> *))
    => Variable (a :: k)
    -> VarSet (kproxy :: KProxy k)
    -> Bool
memberVarSet x (VarSet xs) =
    -- HACK: can't use do-notation here for GADT reasons
    case IM.lookup (fromNat $ varID x) xs of
    Nothing                -> False
    Just (SomeVariable x') -> 
        case varEq x x' of
        Nothing -> False
        Just _  -> True

-- NB: The union and intersection operations are left biased.
-- What is the best behaviour when we have two variables with
-- different types in the set?
unionVarSet
    :: forall (kproxy :: KProxy k)
    .  (Show1 (Sing :: k -> *), JmEq1 (Sing :: k -> *))
    => VarSet kproxy
    -> VarSet kproxy
    -> VarSet kproxy
unionVarSet (VarSet s1) (VarSet s2) = VarSet (IM.union s1 s2)

intersectVarSet
    :: forall (kproxy :: KProxy k)
    .  (Show1 (Sing :: k -> *), JmEq1 (Sing :: k -> *))
    => VarSet kproxy
    -> VarSet kproxy
    -> VarSet kproxy
intersectVarSet (VarSet s1) (VarSet s2) = VarSet (IM.intersection s1 s2)

sizeVarSet :: VarSet a -> Int
sizeVarSet (VarSet xs) = IM.size xs

----------------------------------------------------------------
-- BUG: haddock doesn't like annotations on GADT constructors. So
-- here we'll avoid using the GADT syntax, even though it'd make
-- the data type declaration prettier\/cleaner.
-- <https://github.com/hakaru-dev/hakaru/issues/6>
--
-- | A pair of variable and term, both of the same Hakaru type.
data Assoc (ast :: k -> *)
    = forall (a :: k) . Assoc
        {-# UNPACK #-} !(Variable a)
        !(ast a)

instance (Show1 (Sing :: k -> *), Show1 (ast :: k -> *))
    => Show (Assoc ast)
    where
    showsPrec p (Assoc x e) =
        showParen (p > 9)
            ( showString "Assoc "
            . showsPrec1 11 x
            . showString " "
            . showsPrec1 11 e
            )


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
newtype Assocs ast = Assocs { unAssocs :: IntMap (Assoc ast) }

instance (Show1 (Sing :: k -> *), Show1 (ast :: k -> *))
    => Show (Assocs ast)
    where
    showsPrec p rho =
        showParen (p > 9)
            ( showString "toAssocs "
            . showListWith shows (fromAssocs rho)
            )

-- | The empty set of associations.
emptyAssocs :: Assocs abt
emptyAssocs = Assocs IM.empty

-- | A single association.
singletonAssocs :: Variable a -> f a -> Assocs f
singletonAssocs x e =
    Assocs $ IM.singleton (fromNat $ varID x) (Assoc x e)

-- | Convert an association list into a list of associations.
fromAssocs :: Assocs ast -> [Assoc ast]
fromAssocs (Assocs rho) = IM.elems rho

-- | Convert a list of associations into an association list. In
-- the event of conflict, later associations override earlier ones.
toAssocs :: [Assoc ast] -> Assocs ast
toAssocs = Assocs . foldl step IM.empty
    where
    step :: IntMap (Assoc ast) -> Assoc ast -> IntMap (Assoc ast)
    step xes xe@(Assoc x _) = IM.insert (fromNat $ varID x) xe xes


-- TODO: Do we also want a zipped curried variant: @List1 (Pair1 Variable ast) xs@?
-- | Convert an unzipped list of curried associations into an
-- association list. In the event of conflict, later associations
-- override earlier ones.
toAssocs1 :: List1 Variable xs -> List1 ast xs -> Assocs ast
toAssocs1 = \xs es -> Assocs (go IM.empty xs es)
    where
    go  :: IntMap (Assoc ast)
        -> List1 Variable xs
        -> List1 ast xs
        -> IntMap (Assoc ast)
    -- BUG: GHC claims the patterns are non-exhaustive here
    go m Nil1         Nil1         = m
    go m (Cons1 x xs) (Cons1 e es) =
        go (IM.insert (fromNat $ varID x) (Assoc x e) m) xs es

instance Semigroup (Assocs abt) where
    Assocs xs <> Assocs ys = Assocs (IM.union xs ys) -- TODO: remove bias; crash if conflicting definitions

instance Monoid (Assocs abt) where
    mempty  = emptyAssocs
#if !(MIN_VERSION_base(4,11,0))
    mappend = (<>)
#endif
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
insertAssoc :: Assoc ast -> Assocs ast -> Assocs ast
insertAssoc v@(Assoc x _) (Assocs xs) =
    case IM.insertLookupWithKey (\_ v' _ -> v') (fromNat $ varID x) v xs of
    (Nothing, xs') -> Assocs xs'
    (Just _,  _  ) -> error "insertAssoc: variable is already assigned!"

insertOrReplaceAssoc :: Assoc ast -> Assocs ast -> Assocs ast
insertOrReplaceAssoc v@(Assoc x _) (Assocs xs) =
    Assocs $ IM.insert (fromNat $ varID x) v xs

insertAssocs :: Assocs ast -> Assocs ast -> Assocs ast
insertAssocs (Assocs from) to = IM.foldr insertAssoc to from

-- | Adjust an association so existing variable refers to different
-- value. Does nothing if variable not present.
adjustAssoc :: Variable (a :: k)
            -> (Assoc ast -> Assoc ast)
            -> Assocs ast
            -> Assocs ast
adjustAssoc x f (Assocs xs) =
    Assocs $ IM.adjust f (fromNat $ varID x) xs

-- | Look up a variable and return the associated term.
--
-- N.B., this function is robust to all interpretations of 'varEq'.
lookupAssoc
    :: (Show1 (Sing :: k -> *), JmEq1 (Sing :: k -> *))
    => Variable (a :: k)
    -> Assocs ast
    -> Maybe (ast a)
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

mapAssocs :: (Assoc ast1 -> Assoc ast2) -> Assocs ast1 -> Assocs ast2
mapAssocs f (Assocs xs) = Assocs (IM.map f xs)
                

----------------------------------------------------------------
----------------------------------------------------------- fin.
