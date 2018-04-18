{-# LANGUAGE CPP
           , DataKinds
           , PolyKinds
           , GADTs
           , TypeOperators
           , TypeFamilies
           , Rank2Types
           , ScopedTypeVariables
           , FlexibleInstances
           , FlexibleContexts
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.04.28
-- |
-- Module      :  Language.Hakaru.Syntax.DatumCase
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Reduction of case analysis on user-defined data types.
----------------------------------------------------------------
module Language.Hakaru.Syntax.DatumCase
    (
    -- * External API
      MatchResult(..)
    , DatumEvaluator
    , matchBranches
    , matchBranch

    -- * Internal API
    , MatchState(..)
    , matchTopPattern
    , matchPattern
    , viewDatum
    ) where

import Data.Proxy (Proxy(..))
import Prelude hiding ((<>))

import Language.Hakaru.Syntax.IClasses
-- TODO: make things polykinded so we can make our ABT implementation
-- independend of Hakaru's type system.
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.AST (Term(Datum_))
import Language.Hakaru.Syntax.ABT

import qualified Data.Text        as Text
import           Data.Number.Nat  (fromNat)
import           Text.PrettyPrint (Doc, (<+>), (<>))
import qualified Text.PrettyPrint as PP

----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: would it be better to combine the 'Maybe' for failure into
-- the MatchResult itself instead of nesting the types? That'd make
-- the return types for 'matchBranch'\/'matchBranches' a bit trickier;
-- we'd prolly have to turn MatchResult into a monad (namely the
-- @Maybe (Either e (Writer (DList...) (Reader (List1...) a)))@
-- monad, or similar but restricting the Reader to a stream consumer).

-- BUG: haddock doesn't like annotations on GADT constructors. So
-- here we'll avoid using the GADT syntax, even though it'd make
-- the data type declaration prettier\/cleaner.
-- <https://github.com/hakaru-dev/hakaru/issues/6>
data MatchResult
    (ast :: Hakaru -> *)
    (abt :: [Hakaru] -> Hakaru -> *)
    (a   :: Hakaru)

    -- | Our 'DatumEvaluator' failed (perhaps in a nested pattern),
    -- thus preventing us from continuing case-reduction.
    = GotStuck

    -- | We successfully matched everything. The first argument
    -- gives the substitution for all the pattern variables. The
    -- second argument gives the body of the branch matched. N.B.,
    -- the substitution maps variables to some type @ast@ which is
    -- defined by the 'DatumEvaluator' used; it is not necessarily
    -- @abt '[]@! However, the body is definitely @abt '[]@ since
    -- thats what a 'Branch' stores after we account for the
    -- pattern-bound variables.
    --
    -- N.B., because the substitution may not have the right type
    -- (and because we are lazy), we do not perform substitution.
    -- Thus, the body has \"free\" variables which are defined\/bound
    -- in the association list. It's up to callers to perform the
    -- substitution, push the assocs onto the heap, or whatever.
    | Matched !(Assocs ast) !(abt '[] a)


instance (Show1 ast, Show2 abt) => Show1 (MatchResult ast abt) where
    showsPrec1 _ GotStuck           = showString "GotStuck"
    showsPrec1 p (Matched rho body) =
        showParen (p > 9)
            ( showString "Matched "
            . showsPrec  11 rho
            . showString " "
            . showsPrec2 11 body
            )

instance (Show1 ast, Show2 abt) => Show (MatchResult ast abt a) where
    showsPrec = showsPrec1
    show      = show1


-- | A function for trying to extract a 'Datum' from an arbitrary
-- term. This function is called every time we enter the 'matchPattern'
-- function. If this function returns 'Nothing' then the final
-- 'MatchResult' will be 'GotStuck'; otherwise, this function returns
-- 'Just' some 'Datum' that we can take apart to continue matching.
--
-- We don't care anything about the monad @m@, we just order the
-- effects in a top-down left-to-right manner as we traverse the
-- pattern. However, do note that we may end up calling this evaluator
-- repeatedly on the same argument, so it should be sufficiently
-- idempotent to work under those conditions. In particular,
-- 'matchBranches' will call it once on the top-level scrutinee for
-- each branch. (We should fix that, but it'll require using pattern
-- automata rather than a list of patterns\/branches.)
--
-- TODO: we could change this from returning 'Maybe' to returning
-- 'Either', that way the evaluator could give some reason for its
-- failure (we would store it in the 'GotStuck' constructor).
type DatumEvaluator ast m =
    forall t
    .  ast (HData' t)
    -> m (Maybe (Datum ast (HData' t)))


-- TODO: see the todo for 'matchBranch' about changing the return
-- type. For this function we'd want to return the list of branches
-- including not just the stuck one but all the ones after it too.
-- (Though there's no need to return earlier branches, since we
-- already know they won't match.)
--
-- | Walk through a list of branches and try matching against them
-- in order. We just call 'matchBranches' repeatedly, and return
-- the first non-failure.
matchBranches
    :: (ABT Term abt, Monad m)
    => DatumEvaluator ast m
    -> ast a
    -> [Branch a abt b]
    -> m (Maybe (MatchResult ast abt b))
matchBranches getDatum e = go
    where
    -- TODO: isn't there a combinator in "Control.Monad" for this?
    -- TODO: lift the call to 'getDatum' out here, to avoid duplicating work
    go []     = return Nothing
    go (b:bs) = do
        match <- matchBranch getDatum e b
        case match of
            Nothing -> go bs
            Just _  -> return match


-- TODO: change the result type to have values @Nothing@, @Just
-- (GotStuck modifiedScrutinee theStuckBranch)@ and @Just (Matched
-- assocs body)@. That is, give more information about getting
-- stuck, and avoid returning stupid stuff when we get stuck.
--
-- | Try matching against a single branch. This function is a thin
-- wrapper around 'matchTopPattern'; we just take apart the 'Branch'
-- to extract the pattern, list of variables to bind, and the body
-- of the branch.
matchBranch
    :: (ABT Term abt, Monad m)
    => DatumEvaluator ast m
    -> ast a
    -> Branch a abt b
    -> m (Maybe (MatchResult ast abt b))
matchBranch getDatum e (Branch pat body) = do
    let (vars,body') = caseBinds body
    match <- matchTopPattern getDatum e pat vars
    return $
        case match of
        Nothing                  -> Nothing
        Just GotStuck_           -> Just GotStuck
        Just (Matched_ rho Nil1) ->
            Just (Matched (toAssocs $ rho []) body')


----------------------------------------------------------------
type DList a = [a] -> [a]

-- | The internal version of 'MatchResult' for giving us the properly
-- generalized inductive hypothesis.
data MatchState
    (ast  :: Hakaru -> *)
    (vars :: [Hakaru])

    -- | Our 'DatumEvaluator' failed (perhaps in a nested pattern),
    -- thus preventing us from continuing case-reduction.
    = GotStuck_

    -- TODO: we used to use @DList1 (Pair1 Variable (abt '[]))
    -- vars1@ for the first argument, with @vars1@ another parameter
    -- to the type; this would be helpful internally for guaranteeing
    -- that we return the right number and types of bindings.
    -- However, because the user-facing 'matchBranch' uses 'Branch'
    -- which existentializes over @vars1@, we'd need our user-facing
    -- 'MatchResult' type to also existentialize over @vars1@. Also,
    -- actually keeping track of @vars1@ makes the 'matchStruct'
    -- function much more difficult to get to typecheck. But,
    -- supposing we get that working, would the added guarantees
    -- of this more specific type be helpful for anyone else?
    --
    -- | We successfully matched everything (so far). The first
    -- argument gives the bindings for all the pattern variables
    -- we've already checked. The second argument gives the pattern
    -- variables remaining to be bound by checking the rest of the
    -- pattern.
    | Matched_
        (DList (Assoc ast))
        (List1 Variable vars)


instance Show1 ast => Show (MatchState ast vars) where
    showsPrec p = shows . ppMatchState p

ppMatchState :: Show1 ast => Int -> MatchState ast vars -> Doc
ppMatchState _ GotStuck_ = PP.text "GotStuck_"
ppMatchState p (Matched_ boundVars unboundVars) =
    let f = "Matched_" in
    parens (p > 9)
        (PP.text f <+> PP.nest (1 + length f) (PP.sep
            [ ppList . map prettyPrecAssoc $ boundVars []
            , ppList $ ppVariables unboundVars
            ]))
    where
    ppList       = PP.brackets . PP.nest 1 . PP.fsep . PP.punctuate PP.comma
    parens True  = PP.parens   . PP.nest 1
    parens False = id

    prettyPrecAssoc :: Show1 ast => Assoc ast -> Doc
    prettyPrecAssoc (Assoc x e) =
        -- PP.cat $ ppFun 11 "Assoc" [ppVariable x, ...]
        let f = "Assoc" in
        PP.cat [PP.text f <+> PP.nest (1 + length f) (PP.sep
            [ ppVariable x
            , PP.text $ showsPrec1 11 e ""
            ])]

    ppVariables :: List1 Variable xs -> [Doc]
    ppVariables Nil1         = []
    ppVariables (Cons1 x xs) = ppVariable x : ppVariables xs

    ppVariable :: Variable a -> Doc
    ppVariable x = hint <> (PP.int . fromNat . varID) x
        where
        hint
            | Text.null (varHint x) = PP.char 'x' -- We used to use '_' but...
            | otherwise             = (PP.text . Text.unpack . varHint) x


-- | Try matching against a (top-level) pattern. This function is
-- a thin wrapper around 'matchPattern' in order to restrict the
-- type.
matchTopPattern
    :: (Monad m)
    => DatumEvaluator ast m
    -> ast a
    -> Pattern vars a
    -> List1 Variable vars
    -> m (Maybe (MatchState ast '[]))
matchTopPattern getDatum e pat vars =
    case eqAppendIdentity (secondProxy pat) of
    Refl -> matchPattern getDatum e pat vars

secondProxy :: f i j -> Proxy i
secondProxy _ = Proxy


-- | A trivial \"evaluation function\". If the term is already a
-- 'Datum_', then we extract the 'Datum' value; otherwise we fail.
-- You can 'return' the result to turn this into an 'DatumEvaluator'.
viewDatum
    :: (ABT Term abt)
    => abt '[] (HData' t)
    -> Maybe (Datum (abt '[]) (HData' t))
viewDatum e =
    caseVarSyn e (const Nothing) $ \t ->
        case t of
        Datum_ d -> Just d
        _        -> Nothing


-- | Try matching against a (potentially nested) pattern. This
-- function generalizes 'matchTopPattern', which is necessary for
-- being able to handle nested patterns correctly. You probably
-- don't ever need to call this function.
matchPattern
    :: (Monad m)
    => DatumEvaluator ast m
    -> ast a
    -> Pattern vars1 a
    -> List1 Variable (vars1 ++ vars2)
    -> m (Maybe (MatchState ast vars2))
matchPattern getDatum e pat vars =
    case pat of
    PWild              -> return . Just $ Matched_ id vars
    PVar               ->
        case vars of
        Cons1 x vars'  -> return . Just $ Matched_ (Assoc x e :) vars'
    PDatum _hint1 pat1 -> do
        mb <- getDatum e
        case mb of
            Nothing                     -> return $ Just GotStuck_
            Just (Datum _hint2 _typ2 d) -> matchCode getDatum d pat1 vars


matchCode
    :: (Monad m)
    => DatumEvaluator ast m
    -> DatumCode  xss ast   (HData' t)
    -> PDatumCode xss vars1 (HData' t)
    -> List1 Variable (vars1 ++ vars2)
    -> m (Maybe (MatchState ast vars2))
matchCode getDatum d pat vars =
    case (d,pat) of
    (Inr d2, PInr pat2) -> matchCode   getDatum d2 pat2 vars
    (Inl d1, PInl pat1) -> matchStruct getDatum d1 pat1 vars
    _                   -> return Nothing


matchStruct
    :: forall m ast xs t vars1 vars2
    .  (Monad m)
    => DatumEvaluator ast m
    -> DatumStruct  xs ast   (HData' t)
    -> PDatumStruct xs vars1 (HData' t)
    -> List1 Variable (vars1 ++ vars2)
    -> m (Maybe (MatchState ast vars2))
matchStruct getDatum d pat vars =
    case (d,pat) of
    (Done,     PDone)     -> return . Just $ Matched_ id vars
    (Et d1 d2, PEt p1 p2) ->
        let vars0 =
                case
                    eqAppendAssoc
                        (secondProxy p1)
                        (secondProxy p2)
                        (Proxy :: Proxy vars2) -- HACK: is there any other way to get our hands on @vars2@?
                of Refl -> vars
        in
        matchFun    getDatum d1 p1 vars0 `bindMMR` \xs1 vars1 ->
        matchStruct getDatum d2 p2 vars1 `bindMMR` \xs2 vars2 ->
        return . Just $ Matched_ (xs1 . xs2) vars2
    where
    -- TODO: just turn @Maybe MatchState@ into a monad already?
    bindMMR m k = do
        mb <- m
        case mb of
            Nothing                  -> return Nothing
            Just GotStuck_           -> return $ Just GotStuck_
            Just (Matched_ xs vars') -> k xs vars'

matchFun
    :: (Monad m)
    => DatumEvaluator ast m
    -> DatumFun  x ast   (HData' t)
    -> PDatumFun x vars1 (HData' t)
    -> List1 Variable (vars1 ++ vars2)
    -> m (Maybe (MatchState ast vars2))
matchFun getDatum d pat vars =
    case (d,pat) of
    (Konst d2, PKonst p2) -> matchPattern getDatum d2 p2 vars
    (Ident d1, PIdent p1) -> matchPattern getDatum d1 p1 vars

----------------------------------------------------------------
----------------------------------------------------------- fin.
