{-# LANGUAGE CPP
           , GADTs
           , KindSignatures
           , DataKinds
           , PolyKinds
           , TypeOperators
           , Rank2Types
           , FlexibleContexts
           , MultiParamTypeClasses
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
      getStatements, putStatements
    , ListContext(..), Ans, Dis(..), runDis
    -- ** TODO: IntMap-based version
    
    -- * Operators on the disintegration monad
    -- ** The \"zero\" and \"one\"
    , bot
    --, reject
    -- ** Emitting code
    , emit
    , emitMBind , emitMBind2
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
    , withIndices
    , extendIndices
    , selectMore
    , statementInds
    , sizeInnermostInd
    -- * Extras
    , Extra(..)
    , getExtras
    , putExtras
    , insertExtra
    , adjustExtra
    , mkLoc
    , freeLocError
    , apply
#ifdef __TRACE_DISINTEGRATE__
    , prettyExtra
    , prettyExtras
#endif    
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
import           Control.Monad        (MonadPlus(..),foldM,guard)
import           Data.Text            (Text)
import qualified Data.Text            as Text
import           Data.Number.Nat

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing    (Sing(..), sUnMeasure, sUnPair, sUnit)
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
import Debug.Trace (trace, traceM)
import qualified Text.PrettyPrint     as PP
import Language.Hakaru.Pretty.Haskell (ppVariable, pretty)
#endif

getStatements :: Dis abt [Statement abt 'Impure]
getStatements = Dis $ \_ c h -> c (statements h) h

putStatements :: [Statement abt 'Impure] -> Dis abt ()
putStatements ss =
    Dis $ \_ c (ListContext i _) extras ->
        c () (ListContext i ss) extras

----------------------------------------------------------------
----------------------------------------------------------------

-- | Capturing substitution: 
plug :: forall abt a xs b
     .  (ABT Term abt)
     => Variable a
     -> abt '[] a
     -> abt xs b
     -> abt xs b
plug x e = start
    where
      start :: forall xs' b' . abt xs' b' -> abt xs' b'
      start f = loop f (viewABT f)
      loop :: forall xs' b'. abt xs' b' -> View (Term abt) xs' b' -> abt xs' b'
      loop _ (Syn t) = syn $! fmap21 start t
      loop f (Var z) = case varEq x z of
                       Just Refl -> e
                       Nothing   -> f
      loop f (Bind _ _) = caseBind f $ \z f' -> 
                          bind z (loop f' (viewABT f'))

-- | Perform multiple capturing substitutions
plugs :: forall abt xs a
      .  (ABT Term abt)
      => Assocs (abt '[]) 
      -> abt xs a
      -> abt xs a
plugs rho0 e0 = F.foldl (\e (Assoc x v) -> plug x v e) e0 (unAssocs rho0)

-- | Plug a term into a context. That is, the 'statements' of the
-- context specifies a program with a hole in it; so we plug the
-- given term into that hole, returning the complete program.
residualizeListContext
    :: forall abt a
    .  (ABT Term abt)
    => ListContext abt 'Impure
    -> Assocs (abt '[])
    -> abt '[] ('HMeasure a)
    -> abt '[] ('HMeasure a)
residualizeListContext ss rho e0 =
    -- N.B., we use a left fold because the head of the list of
    -- statements is the one closest to the hole.
#ifdef __TRACE_DISINTEGRATE__
    trace ("e0: " ++ show (pretty e0) ++ "\n"
          ++ show (pretty_Statements (statements ss))) $
#endif
    foldl step (plugs rho e0) (statements ss)
    where    
    step
        :: abt '[] ('HMeasure a)
        -> Statement abt 'Impure
        -> abt '[] ('HMeasure a)
    step e s =        
#ifdef __TRACE_DISINTEGRATE__
        trace ("wrapping " ++ show (ppStatement 0 s) ++ "\n"
               ++ "around term " ++ show (pretty e)) $
#endif  
        case s of       
        SBind (Location x) body _ ->
            -- TODO: if @body@ is dirac, then treat as 'SLet'
            syn (MBind :$ plugs rho (fromLazy body) :* bind x e :* End)
        SLet (Location x) body _
            | not (x `memberVarSet` freeVars e) ->
#ifdef __TRACE_DISINTEGRATE__
               trace ("could not find location" ++ show x ++ "\n"
                     ++ "in term " ++ show (pretty e) ++ "\n"
                     ++ "given rho " ++ show (prettyAssocs rho)) $
#endif                
                e
            -- TODO: if used exactly once in @e@, then inline.
            | otherwise ->
                case getLazyVariable body of
                Just y  -> plug x (plugs rho (var y)) e
                Nothing ->
                    case getLazyLiteral body of
                    Just v  -> plug x (syn $ Literal_ v) e
                    Nothing ->
                        syn (Let_ :$ plugs rho (fromLazy body) :* bind x e :* End)
        SGuard xs pat scrutinee _ ->
            syn $ Case_ (plugs rho $ fromLazy scrutinee)
                [ Branch pat   (binds_ (fromLocations1 xs) e)
                , Branch PWild (P.reject $ typeOf e)
                ]
        SWeight body _ -> syn $ Superpose_ ((plugs rho $ fromLazy body, e) :| [])

----------------------------------------------------------------
-- An extra is a variable *use* instantiated at some list of indices.
data Extra :: (Hakaru -> *) -> Hakaru -> * where
     Loc :: Location a 
         -> [Variable 'HNat]
         -> Extra ast a
     MultiLoc
         :: Location a
         -> [Variable 'HNat]
         -> Extra ast ('HArray a)

extrasInds :: Extra ast a -> [Variable 'HNat]
extrasInds (Loc       _ inds) = inds
extrasInds (MultiLoc  _ inds) = inds

selectMore :: [Variable 'HNat] -> Variable 'HNat -> [Variable 'HNat]
selectMore = flip (:)

#ifdef __TRACE_DISINTEGRATE__
      
prettyExtra :: Extra ast (a :: Hakaru) -> PP.Doc
prettyExtra (Loc (Location x) inds)      = PP.text "Loc" PP.<+> ppVariable x
                                           PP.<+> ppList (map ppVariable inds)
prettyExtra (MultiLoc (Location x) inds) = PP.text "MultiLoc" PP.<+> ppVariable x
                                           PP.<+> ppList (map ppVariable inds)

prettyExtras :: (ABT Term abt)
           => Assocs (Extra (abt '[]))
           -> PP.Doc
prettyExtras a = PP.vcat $ map go (fromAssocs a)
  where go (Assoc x l) = ppVariable x PP.<+>
                         PP.text "->" PP.<+>
                         prettyExtra l

#endif                           

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
  -> Assocs (Extra (abt '[]))
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
    Dis { unDis :: forall a. [Index (abt '[])] -> (x -> Ans abt a) -> Ans abt a }
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
runDis d es =
    m0 [] c0 (ListContext i0 []) emptyAssocs
    where
    (Dis m0) = d >>= residualizeLocs
    -- TODO: we only use dirac because 'residualizeListContext' requires it to already be a measure; unfortunately this can result in an extraneous @(>>= \x -> dirac x)@ redex at the end of the program. In principle, we should be able to eliminate that redex by changing the type of 'residualizeListContext'...
    c0 (e,rho) ss _ = [residualizeListContext ss rho (syn(Dirac :$ e :* End))]
                  
    i0 = maxNextFree es

{---------------------------------------------------------------------------------- 
 
 residualizeLocs does the following:
 1. update the heap by constructing plate/array around statements with nonempty indices
 2. use locations to construct terms out of var and "!" (for indexing into arrays)

For example, consider the state:

  list context (aka heap) =
  l1 <- lebesgue []
  l2 <- plate (normal 0 1) []
  l3 <- lebesgue [i]
  l4 <- dirac x3 []
  l5 <- normal 0 1 [j]
  
  assocs (aka locs) =
  x1 -> Loc l1 []
  x2 -> Loc l2 []
  x3 -> MultiLoc l3 []
  x4 -> Loc l4 []
  x5 -> Loc l5 [k]
  
Here the types of the above variables are:

  l1, x1 :: Real
  l2, x2 :: Array Real
  l3 :: Real
  x3 :: Array Real
  l4, x4 :: Array Real
  l5, x5 :: Real

Then residualizeLoc does two things:

1.Change the heap

  list context = 
  l1' <- lebesgue []
  l2' <- plate (normal 0 1) []
  l3' <- plate i (lebesgue)
  l4' <- dirac x3
  l5' <- plate j (normal 0 1)

2.Create new association table

  rho = 
  x1 -> var l1'
  x2 -> var l2'
  x3 -> array i' (l3' ! i')
  x4 -> var l4'
  x5 -> var l5' ! k 

----------------------------------------------------------------------------------}
residualizeLocs :: forall a abt. (ABT Term abt)
                => abt '[] a
                -> Dis abt (abt '[] a, Assocs (abt '[]))
residualizeLocs e = do
  ss <- getStatements
  (ss', newlocs) <- foldM step ([], emptyLAssocs) ss
  rho <- convertLocs newlocs
  putStatements (reverse ss')
#ifdef __TRACE_DISINTEGRATE__
  trace ("residualizeLocs: old heap:\n" ++ show (pretty_Statements ss )) $ return ()
  trace ("residualizeLocs: new heap:\n" ++ show (pretty_Statements ss')) $ return ()
  extras <- getExtras
  traceM ("oldlocs:\n" ++ show (prettyExtras extras) ++ "\n")
  traceM ("new assoc for renaming:\n" ++ show (prettyAssocs rho))
#endif
  return (e, rho)
    where step (ss',newlocs) s = do (s',newlocs') <- residualizeLoc s
                                    return (s':ss', insertLAssocs newlocs' newlocs)

data Name (a :: Hakaru) = Name {nameHint :: Text, nameID :: Nat}

locName :: Location a -> Name b
locName (Location x) = Name (varHint x) (varID x)

residualizeLoc :: (ABT Term abt)
               => Statement abt 'Impure
               -> Dis abt (Statement abt 'Impure, LAssocs Name)
residualizeLoc s =
    case s of
      SBind l _ _ -> do 
             (s', newname) <- reifyStatement s
             return (s', singletonLAssocs l newname)
      SLet  l _ _ -> do
             (s', newname) <- reifyStatement s
             return (s', singletonLAssocs l newname)
      SWeight w inds    -> do
             x <- freshVar Text.empty sUnit
             let bodyW = Thunk $ P.weight (fromLazy w)
             (s', newname) <- reifyStatement (SBind (Location x) bodyW inds)
             return (s', singletonLAssocs (Location x) newname)
      SGuard ls _ _ ixs
        | null ixs  -> return (s, toLAssocs1 ls (fmap11 locName ls))
        | otherwise -> error "undefined: case statement under an array"

reifyStatement :: (ABT Term abt)
               => Statement abt 'Impure
               -> Dis abt (Statement abt 'Impure, Name a)
reifyStatement s =
    case s of
      SBind l _    []     -> return (s, locName l)
      SBind l body (i:is) -> do
        let plate = Thunk . P.plateWithVar (indSize i) (indVar i)
        x' <- freshVar (locHint l) (SArray (locType l))
        reifyStatement (SBind (Location x') (plate $ fromLazy body) is)
      SLet  l _    []     -> return (s, locName l)
      SLet  l body (i:is) -> do
        let array = Thunk . P.arrayWithVar (indSize i) (indVar i)
        x' <- freshVar (locHint l) (SArray (locType l))
        reifyStatement (SLet  (Location x') (array $ fromLazy body) is)
      SWeight _    _      -> error "reifyStatement called on SWeight"
      SGuard _ _ _ _      -> error "reifyStatement called on SGuard"
                             
sizeInnermostInd :: (ABT Term abt)
                 => Location (a :: Hakaru)
                 -> Dis abt (abt '[] 'HNat)
sizeInnermostInd l =
    (maybe (freeLocError l) return =<<) . select l $ \s ->
        do guard (length (statementInds s) >= 1)
           case s of
             SBind l' _ ixs -> do Refl <- locEq l l'
                                  Just $ unsafePush s >>
                                         return (indSize (head ixs))
             SLet  l' _ ixs -> do Refl <- locEq l l'
                                  Just $ unsafePush s >>
                                         return (indSize (head ixs))
             SWeight _ _    -> Nothing
             SGuard _ _ _ _ -> error "TODO: sizeInnermostInd{SGuard}"
                                         
fromName :: (ABT Term abt)
         => Name b
         -> Sing a
         -> [Variable 'HNat]
         -> abt '[] a
fromName name typ []     = var $ Variable { varHint = nameHint name
                                         , varID   = nameID name
                                         , varType = typ }
fromName name typ (i:is) = fromName name (SArray typ) is P.! var i
                     
convertLocs :: (ABT Term abt)
            => LAssocs Name
            -> Dis abt (Assocs (abt '[]))
convertLocs newlocs = F.foldr step emptyAssocs . fromAssocs <$> getExtras
    where
      build :: (ABT Term abt)
            => Assoc (Extra (abt '[]))
            -> Name a
            -> Assoc (abt '[])
      build (Assoc x extra) name =
          Assoc x (fromName name (varType x) (extrasInds extra))
      step assoc@(Assoc _ extra) = insertAssoc $
          case extra of
                 Loc      l _ -> maybe (freeLocError l)
                                       (build assoc)
                                       (lookupLAssoc l newlocs)
                 MultiLoc l _ -> maybe (freeLocError l)
                                       (build assoc)
                                       (lookupLAssoc l newlocs)

freeLocError :: Location (a :: Hakaru) -> b
freeLocError l = error $ "Found a free location " ++ show l

apply :: (ABT Term abt)
      => [(Index (abt '[]), Index (abt '[]))]
      -> abt '[] a
      -> Dis abt (abt '[] a)
apply ijs e = do extras <- fromAssocs <$> getExtras
                 rho' <- foldM step rho extras
                 return (renames rho' e)
    where
      rho = toAssocs $ map (\(i,j) -> Assoc (indVar i) (indVar j)) ijs
      step r (Assoc x extra) =
            let inds  = extrasInds extra
                check i = lookupAssoc i rho
                inds' = map (\i -> fromMaybe i (check i)) inds
            in if (any isJust (map check inds))
               then do x' <- case extra of
                               Loc      l _ -> mkLoc      Text.empty l inds'
                               MultiLoc l _ -> mkMultiLoc Text.empty l inds'
                       return (insertAssoc (Assoc x x') r)
               else return r
                           
extendIndices
    :: (ABT Term abt)
    => Index (abt '[])
    -> [Index (abt '[])]
    -> [Index (abt '[])]
-- TODO: check all Indices are unique
extendIndices j js | j `elem` js
                   = error ("Duplicate index between " )
                     -- TODO finish this error message by
                     -- defining Show for Index
                   | otherwise
                   = j : js

-- give better name
statementInds :: Statement abt p -> [Index (abt '[])]
statementInds (SBind   _ _   i) = i
statementInds (SLet    _ _   i) = i
statementInds (SWeight _     i) = i
statementInds (SGuard  _ _ _ i) = i
statementInds (SStuff0 _     i) = i
statementInds (SStuff1 _ _   i) = i

getExtras :: (ABT Term abt)
          => Dis abt (Assocs (Extra (abt '[])))
getExtras = Dis $ \_ c h l -> c l h l

putExtras :: (ABT Term abt)
          => Assocs (Extra (abt '[]))
          -> Dis abt ()
putExtras l = Dis $ \_ c h _ -> c () h l

insertExtra :: (ABT Term abt)
            => Variable a
            -> Extra (abt '[]) a
            -> Dis abt ()
insertExtra v extra = 
  Dis $ \_ c h l -> c () h $
    insertAssoc (Assoc v extra) l

adjustExtra :: (ABT Term abt)
            => Variable (a :: Hakaru)
            -> (Assoc (Extra (abt '[])) -> Assoc (Extra (abt '[])))
            -> Dis abt ()
adjustExtra x f = do
    extras <- getExtras
    putExtras $ adjustAssoc x f extras

mkLoc
    :: (ABT Term abt)
    => Text
    -> Location (a :: Hakaru)
    -> [Variable 'HNat]
    -> Dis abt (Variable a)
mkLoc hint l inds = do
  x <- freshVar hint (locType l)
  insertExtra x (Loc l inds)
  return x

mkLocs
    :: (ABT Term abt)
    => List1 Location (xs :: [Hakaru])
    -> [Variable 'HNat]
    -> Dis abt (List1 Variable xs)
mkLocs Nil1         _    = return Nil1
mkLocs (Cons1 l ls) inds = Cons1
                           <$> mkLoc Text.empty l inds
                           <*> mkLocs ls inds

mkMultiLoc
    :: (ABT Term abt)
    => Text
    -> Location a
    -> [Variable 'HNat]
    -> Dis abt (Variable ('HArray a))
mkMultiLoc hint l inds = do
  x' <- freshVar hint (SArray $ locType l)
  insertExtra x' (MultiLoc l inds)
  return x'

instance Functor (Dis abt) where
    fmap f (Dis m)  = Dis $ \i c -> m i (c . f)

instance Applicative (Dis abt) where
    pure x            = Dis $ \_ c -> c x
    Dis mf <*> Dis mx = Dis $ \i c -> mf i $ \f -> mx i $ \x -> c (f x)

instance Monad (Dis abt) where
    return      = pure
    Dis m >>= k = Dis $ \i c -> m i $ \x -> unDis (k x) i c

instance Alternative (Dis abt) where
    empty           = Dis $ \_ _ _ _ -> []
    Dis m <|> Dis n = Dis $ \i c h l -> m i c h l ++ n i c h l

instance MonadPlus (Dis abt) where
    mzero = empty -- aka "bot"
    mplus = (<|>) -- aka "lub"

instance (ABT Term abt) => EvaluationMonad abt (Dis abt) 'Impure where
    freshNat =
        Dis $ \_ c (ListContext n ss) ->
            c n (ListContext (n+1) ss)

    -- Note: we assume that freshenStatement is never called on a
    -- statement already on the heap (list context)
    freshenStatement s =
        case s of
          SWeight _ _    -> return (s, mempty)
          SBind l body i -> do
               l' <- freshenLoc l
               v  <- mkLoc (locHint l) l' (map indVar i)
               return (SBind l' body i, singletonAssocs (fromLocation l) v)
          SLet  l body i -> do
               l' <- freshenLoc l
               v  <- mkLoc (locHint l) l' (map indVar i)
               return (SLet l' body i, singletonAssocs (fromLocation l) v)
          SGuard ls pat scrutinee i -> do
               ls'  <- freshenLocs ls
               vs   <- mkLocs ls' (map indVar i)
               return (SGuard ls' pat scrutinee i,
                       toAssocs1 (fromLocations1 ls) vs)

    getIndices =  Dis $ \i c -> c i

    unsafePush s =
        Dis $ \_ c (ListContext i ss) ->
            c () (ListContext i (s:ss))

    -- N.B., the use of 'reverse' is necessary so that the order
    -- of pushing matches that of 'pushes'
    unsafePushes ss =
        Dis $ \_ c (ListContext i ss') ->
            c () (ListContext i (reverse ss ++ ss'))

    select l p = loop []
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
                    case l `isBoundBy` s >> p s of
                    Nothing -> loop (s:ss)
                    Just mr -> do
                        r <- mr
                        unsafePushes ss
                        return (Just r)

withIndices :: [Index (abt '[])] -> Dis abt a -> Dis abt a
withIndices inds (Dis m) = Dis $ \_ c -> m inds c

-- | Not exported because we only need it for defining 'select' on 'Dis'.
unsafePop :: Dis abt (Maybe (Statement abt 'Impure))
unsafePop =
    Dis $ \_ c h@(ListContext i ss) extras ->
        case ss of
        []    -> c Nothing  h extras
        s:ss' -> c (Just s) (ListContext i ss') extras

pushPlate
    :: (ABT Term abt)
    => abt '[] 'HNat
    -> abt '[ 'HNat ] ('HMeasure a)
    -> Dis abt (Variable ('HArray a))
pushPlate n e =
  caseBind e $ \x body -> do
    inds <- getIndices
    i    <- freshInd n
    p    <- Location <$> freshVar Text.empty (sUnMeasure $ typeOf body)
    unsafePush (SBind p (Thunk $ rename x (indVar i) body)
                (extendIndices i inds))
    mkMultiLoc Text.empty p (map indVar inds)

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
    Dis $ \_ c h l -> (f . bind x) <$> c x h l

-- This function was called @lift@ in the finally-tagless code.
-- | Emit an 'MBind' (i.e., \"@m >>= \x ->@\") and return the
-- variable thus bound (i.e., @x@).
emitMBind :: (ABT Term abt) => abt '[] ('HMeasure a) -> Dis abt (Variable a)
emitMBind m =
    emit Text.empty (sUnMeasure $ typeOf m) $ \e ->
        syn (MBind :$ m :* e :* End)

emitMBind2 :: (ABT Term abt) => abt '[] ('HMeasure a) -> Dis abt (abt '[] a)
emitMBind2 m = do
  inds <- getIndices
  let b = Whnf_ $ fromMaybe (error "emitMBind2: non-hnf term") (toWhnf m)
      typ = sUnMeasure $ typeOf m
  l <- Location <$> freshVar Text.empty typ
  (SBind l' b' _, name) <- reifyStatement (SBind l b inds)
  let (idx, p) = (fromName name typ (map indVar inds), fromLazy b')
  Dis $ \_ c h ex ->
      c idx h ex >>= \e ->
      return $ syn (MBind :$ p :* bind (fromLocation l') e :* End)

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
        Dis $ \_ c h l ->
            ( syn
            . Case_ e
            . (:[])
            . Branch (pPair PVar PVar)
            . bind x
            . bind y
            ) <$> c (var x, var y) h l

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
emit_ f = Dis $ \_ c h l -> f <$> c () h l


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
emitFork_ f ms = Dis $ \i c h l -> f <$> T.traverse (\m -> unDis m i c h l) ms


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
                let rho = toAssocs1 vars vars'
                in  GBranch pat vars' (f $ renames rho body')
            ) <$> freshenVars vars
    Dis $ \i c h l ->
        (syn . Case_ e) <$> T.for gms (\gm ->
            fromGBranch <$> T.for gm (\m ->
                unDis m i c h l))
{-# INLINE emitCaseWith #-}


----------------------------------------------------------------
----------------------------------------------------------- fin.
