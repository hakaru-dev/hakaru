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
--                                                    2015.11.03
-- |
-- Module      :  Language.Hakaru.Syntax.DatumCase
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Reduction of case analysis on user-defined data types.
----------------------------------------------------------------
module Language.Hakaru.Syntax.DatumCase
    ( MatchResult(..)
    , DatumEvaluator
    , matchBranches
    , matchBranch
    , matchTopPattern
    , matchPattern
    , viewDatum
    ) where

import Data.Proxy (Proxy(..))

import Language.Hakaru.Syntax.IClasses
-- TODO: make things polykinded so we can make our ABT implementation
-- independend of Hakaru's type system.
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.AST (Term(Datum_))
import Language.Hakaru.Syntax.ABT

import           Language.Hakaru.Pretty.Haskell
import           Text.PrettyPrint (Doc, (<+>))
import qualified Text.PrettyPrint as PP

----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: would it be better to combine the 'Maybe' for failure into the MatchResult itself instead of nesting the types? That'd make the return types for 'matchBranch'\/'matchBranches' a bit trickier; we'd prolly have to turn MatchResult into a monad (namely the @Maybe (Either e (Writer (DList...) (Reader (List1...) a)))@ monad, or similar but restricting the Reader to a stream consumer).

-- BUG: haddock doesn't like annotations on GADT constructors. So
-- here we'll avoid using the GADT syntax, even though it'd make
-- the data type declaration prettier\/cleaner.
-- <https://github.com/hakaru-dev/hakaru/issues/6>
data MatchResult
    (abt  :: [Hakaru] -> Hakaru -> *)
    (vars :: [Hakaru])

    -- | Our 'DatumEvaluator' failed (perhaps in a nested pattern),
    -- thus preventing us from continuing case-reduction.
    = GotStuck

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
    | Matched
        (DList (Assoc abt))
        (List1 Variable vars)


type DList a = [a] -> [a]


instance (ABT Term abt) => Show (MatchResult abt vars) where
    showsPrec p = shows . ppMatchResult p

ppMatchResult :: (ABT Term abt) => Int -> MatchResult abt vars -> Doc
ppMatchResult _ GotStuck = PP.text "GotStuck"
ppMatchResult p (Matched boundVars unboundVars) =
    parens (p > 9)
        (PP.text f <+> PP.nest (1 + length f) (PP.sep
            [ ppList . map (prettyPrecAssoc 11) $ boundVars []
            , ppList $ ppVariables unboundVars
            ]))
    where
    f            = "Matched"
    ppList       = PP.brackets . PP.nest 1 . PP.fsep . PP.punctuate PP.comma
    parens True  = PP.parens   . PP.nest 1
    parens False = id

    ppVariables :: List1 (Variable :: Hakaru -> *) xs -> [Doc]
    ppVariables Nil1         = []
    ppVariables (Cons1 x xs) = ppVariable x : ppVariables xs



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


-- | Walk through a list of branches and try matching against them
-- in order. We just call 'matchBranches' repeatedly, and return
-- the first non-failure.
--
-- N.B., the second component of the result pair is determined by
-- the 'Branch' that doesn't fail. Thus, we can offer up that body
-- even if that branch 'GotStuck' rather than fully matching.
matchBranches
    :: (ABT Term abt, Monad m)
    => DatumEvaluator (abt '[]) m
    -> abt '[] a
    -> [Branch a abt b]
    -> m (Maybe (MatchResult abt '[], abt '[] b))
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


-- | Try matching against a single branch. This function is a thin
-- wrapper around 'matchTopPattern'; we just take apart the 'Branch'
-- to extract the pattern, list of variables to bind, and the body
-- of the branch.
--
-- N.B., the second component of the result pair is determined by
-- the 'Branch' itself. Thus, we can offer up that body even if the
-- branch 'GotStuck' rather than fully matching.
matchBranch
    :: (ABT Term abt, Monad m)
    => DatumEvaluator (abt '[]) m
    -> abt '[] a
    -> Branch a abt b
    -> m (Maybe (MatchResult abt '[], abt '[] b))
matchBranch getDatum e (Branch pat body) = do
    let (vars,body') = caseBinds body
    match <- matchTopPattern getDatum e pat vars
    return $ fmap (\mr -> (mr,body')) match


-- | Try matching against a (top-level) pattern. This function is
-- a thin wrapper around 'matchPattern' in order to restrict the
-- type.
matchTopPattern
    :: (ABT Term abt, Monad m)
    => DatumEvaluator (abt '[]) m
    -> abt '[] a
    -> Pattern vars a
    -> List1 Variable vars
    -> m (Maybe (MatchResult abt '[]))
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
    :: (ABT Term abt, Monad m)
    => DatumEvaluator (abt '[]) m
    -> abt '[] a
    -> Pattern vars1 a
    -> List1 Variable (vars1 ++ vars2)
    -> m (Maybe (MatchResult abt vars2))
matchPattern getDatum e pat vars =
    case pat of
    PWild              -> return . Just $ Matched id vars
    PVar               ->
        case vars of
        Cons1 x vars'  -> return . Just $ Matched (Assoc x e :) vars'
        _              -> error "matchPattern: the impossible happened"
    PDatum _hint1 pat1 -> do
        mb <- getDatum e
        case mb of
            Nothing               -> return $ Just GotStuck
            Just (Datum _hint2 d) -> matchCode getDatum d pat1 vars


matchCode
    :: (ABT Term abt, Monad m)
    => DatumEvaluator (abt '[]) m
    -> DatumCode  xss (abt '[]) (HData' t)
    -> PDatumCode xss vars1     (HData' t)
    -> List1 Variable (vars1 ++ vars2)
    -> m (Maybe (MatchResult abt vars2))
matchCode getDatum d pat vars =
    case (d,pat) of
    (Inr d2, PInr pat2) -> matchCode   getDatum d2 pat2 vars
    (Inl d1, PInl pat1) -> matchStruct getDatum d1 pat1 vars
    _                   -> return Nothing


matchStruct
    :: forall m abt xs t vars1 vars2
    .  (ABT Term abt, Monad m)
    => DatumEvaluator (abt '[]) m
    -> DatumStruct  xs (abt '[]) (HData' t)
    -> PDatumStruct xs vars1     (HData' t)
    -> List1 Variable (vars1 ++ vars2)
    -> m (Maybe (MatchResult abt vars2))
matchStruct getDatum d pat vars =
    case (d,pat) of
    (Done,     PDone)     -> return . Just $ Matched id vars
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
        return . Just $ Matched (xs1 . xs2) vars2
    _ -> return Nothing
    where
    -- TODO: just turn @Maybe MatchResult@ into a monad already?
    bindMMR m k = do
        mb <- m
        case mb of
            Nothing                 -> return Nothing
            Just GotStuck           -> return $ Just GotStuck
            Just (Matched xs vars') -> k xs vars'

matchFun
    :: (ABT Term abt, Monad m)
    => DatumEvaluator (abt '[]) m
    -> DatumFun  x (abt '[]) (HData' t)
    -> PDatumFun x vars1     (HData' t)
    -> List1 Variable (vars1 ++ vars2)
    -> m (Maybe (MatchResult abt vars2))
matchFun getDatum d pat vars =
    case (d,pat) of
    (Konst d2, PKonst p2) -> matchPattern getDatum d2 p2 vars
    (Ident d1, PIdent p1) -> matchPattern getDatum d1 p1 vars
    _                     -> return Nothing

----------------------------------------------------------------
----------------------------------------------------------- fin.
