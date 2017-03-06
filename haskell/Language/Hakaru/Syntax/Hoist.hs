{-# LANGUAGE CPP
           , BangPatterns
           , DataKinds
           , EmptyCase
           , ExistentialQuantification
           , FlexibleContexts
           , FlexibleInstances
           , GADTs
           , GeneralizedNewtypeDeriving
           , KindSignatures
           , MultiParamTypeClasses
           , OverloadedStrings
           , PolyKinds
           , ScopedTypeVariables
           , StandaloneDeriving
           , TupleSections
           , TypeFamilies
           , TypeOperators
           , UndecidableInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2017.02.01
-- |
-- Module      :  Language.Hakaru.Syntax.Hoist
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Hoist expressions to the point where their data dependencies are met.
-- This pass duplicates *a lot* of work and relies on a the CSE and pruning
-- passes to cleanup the junk (most of which is trivial to do, but we don't know
-- what is junk until after CSE has occured).
--
-- NOTE: This pass assumes globally unique variable ids, as two subterms may
-- otherwise bind the same variable. Those variables would potentially shadow
-- eachother if hoisted upward to a common scope.
--
----------------------------------------------------------------
module Language.Hakaru.Syntax.Hoist (hoist) where

import           Control.Applicative             (liftA2)
import           Control.Monad.RWS
import qualified Data.Foldable                   as F
import qualified Data.Graph                      as G
import qualified Data.IntMap                     as IM
import qualified Data.List                       as L
import           Data.Maybe                      (mapMaybe)
import           Data.Number.Nat
import           Data.Proxy                      (KProxy (..))
import qualified Data.Vector                     as V

import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.ANF      (isValue)
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.AST.Eq   (alphaEq)
import           Language.Hakaru.Syntax.Gensym
import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Types.DataKind
import           Language.Hakaru.Types.Sing      (Sing)

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative
#endif

data Entry (abt :: Hakaru -> *)
  = forall (a :: Hakaru) . Entry
  { varDependencies :: !(VarSet (KindOf a))
  , expression      :: !(abt a)
  -- The type of the expression, to allow for easy comparison of types.
  -- The typeOf operator is technically O(n) in the size of the expresion
  -- and we may need to call it many times.
  , sing            :: !(Sing a)
  , bindings        :: ![Variable a]
  }

instance Show (Entry abt) where
  show (Entry d _ _ b) = "Entry (" ++ show d ++ ") (" ++ show b ++ ")"

type HakaruProxy = ('KProxy :: KProxy Hakaru)
type LiveSet     = VarSet HakaruProxy
type HakaruVar   = SomeVariable HakaruProxy

-- The @HoistM@ monad makes use of three monadic layers to propagate information
-- both downwards to the leaves and upwards to the root node of the AST.
--
-- The Writer layer propagates the live expressions which may be hoisted (i.e.
-- all their data dependencies are currently filled) from each subexpression to
-- their parents.
--
-- The Reader layer propagates the currently bound variables which will be used
-- to decide when to introduce new bindings.
--
-- The State layer is just to provide a counter in order to gensym new
-- variables, since the process of adding new bindings is a little tricky.
-- What we want is to fully duplicate bindings without altering the original
-- variable identifiers. To do so, all original variable names are preserved and
-- new variables are added outside the range of existing variables.
newtype HoistM (abt :: [Hakaru] -> Hakaru -> *) a
  = HoistM { runHoistM :: RWS LiveSet (ExpressionSet abt) Nat a }

deriving instance                   Functor (HoistM abt)
deriving instance (ABT Term abt) => Applicative (HoistM abt)
deriving instance (ABT Term abt) => Monad (HoistM abt)
deriving instance (ABT Term abt) => MonadState Nat (HoistM abt)
deriving instance (ABT Term abt) => MonadWriter (ExpressionSet abt) (HoistM abt)
deriving instance (ABT Term abt) => MonadReader LiveSet (HoistM abt)

newtype ExpressionSet (abt :: [Hakaru] -> Hakaru -> *)
  = ExpressionSet [Entry (abt '[])]

mergeEntry :: (ABT Term abt) => Entry (abt '[]) -> Entry (abt '[]) -> Entry (abt '[])
mergeEntry (Entry d e s1 b1) (Entry _ e' s2 b2) =
  case jmEq1 s1 s2 of
    Just Refl -> Entry d e s1 $ L.nub (b1 ++ b2)
    Nothing   -> error "cannot union mismatched entries"

entryEqual :: (ABT Term abt) => Entry (abt '[]) -> Entry (abt '[]) -> Bool
entryEqual Entry{varDependencies=d1,expression=e1,sing=s1}
      Entry{varDependencies=d2,expression=e2,sing=s2} =
  case (d1 == d2, jmEq1 s1 s2) of
    (True , Just Refl) -> alphaEq e1 e2
    _                  -> False

unionEntrySet
  :: forall abt
  .  (ABT Term abt)
  => ExpressionSet abt
  -> ExpressionSet abt
  -> ExpressionSet abt
unionEntrySet (ExpressionSet xs) (ExpressionSet ys) =
  ExpressionSet . mapMaybe uniquify $ L.groupBy entryEqual (xs ++ ys)
  where
    uniquify :: [Entry (abt '[])] -> Maybe (Entry (abt '[]))
    uniquify [] = Nothing
    uniquify zs = Just $ L.foldl1' mergeEntry zs

intersectEntrySet
  :: forall abt
  .  (ABT Term abt)
  => ExpressionSet abt
  -> ExpressionSet abt
  -> ExpressionSet abt
intersectEntrySet (ExpressionSet xs) (ExpressionSet ys) = ExpressionSet cross
  where
    cross :: [Entry (abt '[])]
    cross = map (uncurry mergeEntry)
          . filter (uncurry entryEqual)
          $ liftA2 (,) xs ys

instance (ABT Term abt) => Monoid (ExpressionSet abt) where
  mempty  = ExpressionSet []
  mappend = unionEntrySet


-- Given a list of entries to introduce, order them so that their data
-- data dependencies are satisified.
topSortEntries
  :: forall abt
  .  [Entry (abt '[])]
  -> [Entry (abt '[])]
topSortEntries entryList = map (entries V.!) $ G.topSort graph
  where
    entries :: V.Vector (Entry (abt '[]))
    !entries = V.fromList entryList

    -- The graph is represented as dependencies between entries, where an entry
    -- (a) depends on entry (b) if (b) introduces a variable which (a) depends
    -- on.
    getVIDs :: Entry (abt '[]) -> [Int]
    getVIDs Entry{bindings=b} = map (fromNat . varID) b

    -- Associates all variables introduced by an entry to the entry itself.
    -- A given entry may introduce multiple bindings, since an entry stores all
    -- α-equivalent variable definitions.
    assocBindingsTo :: Int -> IM.IntMap Int -> Entry (abt '[]) -> IM.IntMap Int
    assocBindingsTo n m = L.foldl' (\acc v -> IM.insert v n acc) m . getVIDs

    -- Mapping from variable IDs to their corresponding entries
    varMap :: IM.IntMap Int
    !varMap = V.ifoldl' (flip assocBindingsTo) IM.empty entries

    -- Create an edge from each dependency to the variable
    makeEdges :: Int -> Entry (abt '[]) -> [G.Edge]
    makeEdges idx Entry{varDependencies=d} = map (, idx)
                                           . mapMaybe (flip IM.lookup varMap)
                                           $ varSetKeys d

    -- Collect all the verticies to build the full graph
    vertices :: [G.Edge]
    !vertices = V.foldr (++) [] $ V.imap makeEdges entries

    -- The full graph structure to be sorted
    graph :: G.Graph
    !graph = G.buildG (0, V.length entries - 1) vertices

recordEntry
  :: (ABT Term abt)
  => Variable a
  -> abt '[] a
  -> HoistM abt ()
recordEntry v abt = tell $ ExpressionSet [Entry (freeVars abt) abt (varType v) [v]]

execHoistM :: Nat -> HoistM abt a -> a
execHoistM counter act = a
  where
    hoisted   = runHoistM act
    (a, _, _) = runRWS hoisted emptyVarSet counter

-- | An expression is considered "toplevel" if it can be hoisted outside all
-- binders. This means that the expression has no data dependencies.
toplevelEntry
  :: Entry abt
  -> Bool
toplevelEntry Entry{varDependencies=d} = sizeVarSet d == 0

captureEntries
  :: (ABT Term abt)
  => HoistM abt a
  -> HoistM abt (a, ExpressionSet abt)
captureEntries = censor (const mempty) . listen

hoist
  :: (ABT Term abt)
  => abt '[] a
  -> abt '[] a
hoist abt = execHoistM (nextFreeOrBind abt) $
  captureEntries (hoist' abt) >>= uncurry (introduceToplevel emptyVarSet)

partitionEntrySet
  :: (Entry (abt '[]) -> Bool)
  -> ExpressionSet abt
  -> (ExpressionSet abt, ExpressionSet abt)
partitionEntrySet p (ExpressionSet xs) = (ExpressionSet true, ExpressionSet false)
  where
    (true, false) = L.partition p xs

introduceToplevel
  :: (ABT Term abt)
  => LiveSet
  -> abt '[] a
  -> ExpressionSet abt
  -> HoistM abt (abt '[] a)
introduceToplevel avail abt entries = do
  -- After transforming the given ast, we need to introduce all the toplevel
  -- bindings (i.e. bindings with no data dependencies), most of which should be
  -- eliminated by constant propagation.
  let (ExpressionSet toplevel, rest) = partitionEntrySet toplevelEntry entries
      intro = concatMap getBoundVars toplevel ++ fromVarSet avail
  -- First we wrap the now AST in the all terms which depdend on top level
  -- definitions
  wrapped <- introduceBindings intro abt rest
  -- Then wrap the result in the toplevel definitions
  wrapExpr wrapped toplevel

bindVar
  :: (ABT Term abt)
  => Variable (a :: Hakaru)
  -> HoistM abt b
  -> HoistM abt b
bindVar = local . insertVarSet

isolateBinder
  :: (ABT Term abt)
  => Variable (a :: Hakaru)
  -> HoistM abt b
  -> HoistM abt (b, ExpressionSet abt)
isolateBinder v = censor (const mempty) . listen . bindVar v

hoist'
  :: forall abt xs a . (ABT Term abt)
  => abt xs a
  -> HoistM abt (abt xs a)
hoist' = start
  where
    insertMany :: [HakaruVar] -> LiveSet -> LiveSet
    insertMany = flip $ L.foldl' (\ acc (SomeVariable v) -> insertVarSet v acc)

    start :: forall ys b . abt ys b -> HoistM abt (abt ys b)
    start = loop [] . viewABT

    isolateBinders :: [HakaruVar] -> HoistM abt c -> HoistM abt (c, ExpressionSet abt)
    isolateBinders xs = censor (const mempty) . listen . local (insertMany xs)

    -- @loop@ takes 2 parameters.
    --
    -- 1. The list of variables bound so far
    -- 2. The current term we are recurring over
    --
    -- We add a value to the first every time we hit a @Bind@ term, and when
    -- a @Syn@ term is finally reached, we introduce any hoisted values whose
    -- data dependencies are satisified by these new variables.
    loop :: forall ys b
         .  [HakaruVar]
         -> View (Term abt) ys b
         -> HoistM abt (abt ys b)
    loop _  (Var v)    = return (var v)

    -- This case is not needed, but we can avoid performing the expensive work
    -- of calling introduceBindings in the case were we won't be performing any
    -- work.
    loop [] (Syn s)    = hoistTerm s
    loop xs (Syn s)    = do
      (term, entries) <- isolateBinders xs (hoistTerm s)
      introduceBindings xs term entries

    loop xs (Bind v b) = bind v <$> loop (SomeVariable v : xs) b

getBoundVars :: Entry x -> [HakaruVar]
getBoundVars Entry{bindings=b} = fmap SomeVariable b

wrapExpr
  :: forall abt b . (ABT Term abt)
  => abt '[] b
  -> [Entry (abt '[])]
  -> HoistM abt (abt '[] b)
wrapExpr = F.foldrM wrap
  where
    mklet :: abt '[] a -> Variable a -> abt '[] b -> abt '[] b
    mklet e v b =
      case viewABT b of
        Var v' | Just Refl <- varEq v v' -> e
        _      -> syn (Let_ :$ e :* bind v b :* End)

    -- Binds the Entry's expression to a fresh variable and rebinds any other
    -- variable uses to the fresh variable.
    wrap :: Entry (abt '[]) -> abt '[] b ->  HoistM abt (abt '[] b)
    wrap Entry{expression=e,bindings=[]} acc = do
      tmp <- varForExpr e
      return $ mklet e tmp acc
    wrap Entry{expression=e,bindings=(x:xs)} acc = do
      let rhs  = var x
          body = foldr (mklet rhs) acc xs
      return $ mklet e x body

-- This will introduce all binders which must be introduced by binding the
-- @newVars@ set. As a side effect, the remaining entries are written into the
-- Writer layer of the stack.
introduceBindings
  :: forall (a :: Hakaru) abt
  .  (ABT Term abt)
  => [HakaruVar]
  -> abt '[] a
  -> ExpressionSet abt
  -> HoistM abt (abt '[] a)
introduceBindings newVars body (ExpressionSet entries) = do
  tell (ExpressionSet leftOver)
  wrapExpr body (topSortEntries resultEntries)
  where
    resultEntries, leftOver :: [Entry (abt '[])]
    (resultEntries, leftOver) = loop entries newVars

    introducedBy
      :: forall (b :: Hakaru)
      .  Variable b
      -> Entry (abt '[])
      -> Bool
    introducedBy v Entry{varDependencies=deps} = memberVarSet v deps

    loop
      :: [Entry (abt '[])]
      -> [HakaruVar]
      -> ([Entry (abt '[])], [Entry (abt '[])])
    loop exprs []                    = ([], exprs)
    loop exprs (SomeVariable v : xs) = (introduced ++ intro, acc)
      where
        ~(intro, acc)      = loop rest (xs ++ vars)
        vars               = concatMap getBoundVars introduced
        (introduced, rest) = L.partition (introducedBy v) exprs

-- Contrary to the other binding forms, let expressions are killed by the
-- hoisting pass. Their RHSs are floated upward in the AST and re-introduced
-- where their data dependencies are fulfilled. Thus, the result of hoisting
-- a let expression is just the hoisted body.
hoistTerm
  :: forall (a :: Hakaru) (abt :: [Hakaru] -> Hakaru -> *)
  .  (ABT Term abt)
  => Term abt a
  -> HoistM abt (abt '[] a)
hoistTerm (Let_ :$ rhs :* body :* End) =
  caseBind body $ \ v body' -> do
    rhs' <- hoist' rhs
    recordEntry v rhs'
    bindVar v (hoist' body')

hoistTerm (Lam_ :$ body :* End) =
  caseBind body $ \ v body' -> do
    available         <- fmap (insertVarSet v) ask
    (body'', entries) <- isolateBinder v (hoist' body')
    finalized         <- introduceToplevel available body'' entries
    return $ syn (Lam_ :$ bind v finalized :* End)

hoistTerm term = do
  result <- syn <$> traverse21 hoist' term
  if isValue result
    then return result
    else do fresh <- varForExpr result
            recordEntry fresh result
            return (var fresh)

