{-# LANGUAGE CPP
           , DataKinds
           , PolyKinds
           , GADTs
           , StandaloneDeriving
           , TypeOperators
           , TypeFamilies
           , Rank2Types
           , ScopedTypeVariables
           , FlexibleInstances
           , FlexibleContexts
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.29
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
    , matchBranches
    , matchBranch
    , matchTopPattern
    , matchPattern
    ) where

import Data.Proxy (Proxy(..))

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.AST (AST(Datum_, Value_), Value(VDatum))
import Language.Hakaru.Syntax.ABT2

import           Language.Hakaru.PrettyPrint
import           Text.PrettyPrint (Doc, (<+>))
import qualified Text.PrettyPrint as PP

----------------------------------------------------------------
----------------------------------------------------------------
-- BUG: haddock doesn't like annotations on GADT constructors. So
-- here we'll avoid using the GADT syntax, even though it'd make
-- the data type declaration prettier\/cleaner.
-- <https://github.com/hakaru-dev/hakaru/issues/6>
data MatchResult
    (abt  :: [Hakaru] -> Hakaru -> *)
    (vars :: [Hakaru])

    -- | We encountered some non-HNF (perhaps in a nested pattern).
    --
    -- TODO: actually store some information about where we got
    -- stuck, so the caller can evaluate the appropriate expression.
    -- As a bonus, the caller should then be able to continue
    -- matching the rest of the pattern without redoing the parts
    -- that we already matched. (Of course, until we factor @[Branch]@
    -- into a single pattern automaton, getting stuck in one branch
    -- doesn't tell us enough to actually avoid restarting; since
    -- some other branch could match if the rest of this one fails.)
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


instance (ABT AST abt) => Show (MatchResult abt vars) where
    showsPrec p = shows . ppMatchResult p

ppMatchResult :: (ABT AST abt) => Int -> MatchResult abt vars -> Doc
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



-- | Walk through a list of branches and try matching against them
-- in order.
--
-- N.B., the second component of the pair is determined by the
-- 'Branch' that matches. Thus, we can offer up that body even if
-- the match itself 'GotStuck'.
matchBranches
    :: (ABT AST abt)
    => abt '[] a
    -> [Branch a abt b]
    -> Maybe (MatchResult abt '[], abt '[] b)
matchBranches e = go
    where
    go []     = Nothing
    go (b:bs) =
        case matchBranch e b of
        Nothing -> go bs
        Just m  -> Just m


-- | Try matching against a single branch. This function is a thin
-- wrapper around 'matchTopPattern'; we just take apart the 'Branch'
-- to extract the pattern, list of variables to bind, and the body
-- of the branch.
--
-- N.B., the second component of the pair is determined by the
-- 'Branch'. Thus, we can offer up that body even if the match
-- itself 'GotStuck'.
matchBranch
    :: (ABT AST abt)
    => abt '[] a
    -> Branch a abt b
    -> Maybe (MatchResult abt '[], abt '[] b)
matchBranch e (Branch pat body) = do
    let (vars,body') = caseBinds body
    match <- matchTopPattern e pat vars
    return (match,body')


-- | Try matching against a (top-level) pattern. This function is
-- a thin wrapper around 'matchPattern' in order to restrict the
-- type.
matchTopPattern
    :: (ABT AST abt)
    => abt '[] a
    -> Pattern vars a
    -> List1 Variable vars
    -> Maybe (MatchResult abt '[])
matchTopPattern e pat vars =
    case eqAppendIdentity (secondProxy pat) of
    Refl -> matchPattern e pat vars

secondProxy :: f i j -> Proxy i
secondProxy _ = Proxy


-- | Try matching against a (potentially nested) pattern. This
-- function generalizes 'matchTopPattern', which is necessary for
-- being able to handle nested patterns correctly. You probably
-- don't ever need to call this function.
matchPattern
    :: (ABT AST abt)
    => abt '[] a
    -> Pattern vars1 a
    -> List1 Variable (vars1 ++ vars2)
    -> Maybe (MatchResult abt vars2)
matchPattern e pat vars =
    case pat of
    PWild              -> Just (Matched id vars)
    PVar               ->
        case vars of
        Cons1 x vars'  -> Just (Matched (Assoc x e :) vars')
        _              -> error "matchPattern: the impossible happened"
    PDatum _hint1 pat1 ->
        case viewDatum e of
        Nothing               -> Just GotStuck
        Just (Datum _hint2 d) -> matchCode d pat1 vars


-- HACK: we must give this a top-level binding rather than inlining it. Again, I'm not entirely sure why...
viewDatum
    :: (ABT AST abt)
    => abt '[] (HData' t)
    -> Maybe (Datum (abt '[]) (HData' t))
viewDatum e =
    caseVarSyn e (const Nothing) $ \t ->
        case t of
        Value_ (VDatum d) -> Just (fmap11 (syn . Value_) d)
        Datum_         d  -> Just d
        _                 -> Nothing


matchCode
    :: (ABT AST abt)
    => DatumCode  xss (abt '[]) (HData' t)
    -> PDatumCode xss vars1     (HData' t)
    -> List1 Variable (vars1 ++ vars2)
    -> Maybe (MatchResult abt vars2)
matchCode (Inr d2) (PInr p2) vars = matchCode   d2 p2 vars
matchCode (Inl d1) (PInl p1) vars = matchStruct d1 p1 vars
matchCode _        _         _    = Nothing


matchStruct
    :: forall abt xs t vars1 vars2
    .  (ABT AST abt)
    => DatumStruct  xs (abt '[]) (HData' t)
    -> PDatumStruct xs vars1     (HData' t)
    -> List1 Variable (vars1 ++ vars2)
    -> Maybe (MatchResult abt vars2)
matchStruct Done       PDone       vars = Just (Matched id vars)
matchStruct (Et d1 d2) (PEt p1 p2) vars = do
    m1 <- 
        case eqAppendAssoc
                (secondProxy p1)
                (secondProxy p2)
                (Proxy :: Proxy vars2)
        of
        Refl -> matchFun d1 p1 vars
    case m1 of
        GotStuck          -> return GotStuck
        Matched xs1 vars' -> do
            m2 <- matchStruct d2 p2 vars'
            return $
                case m2 of
                GotStuck           -> GotStuck
                Matched xs2 vars'' -> Matched (xs1 . xs2) vars''
matchStruct _ _ _ = Nothing


matchFun
    :: (ABT AST abt)
    => DatumFun  x (abt '[]) (HData' t)
    -> PDatumFun x vars1     (HData' t)
    -> List1 Variable (vars1 ++ vars2)
    -> Maybe (MatchResult abt vars2)
matchFun (Konst d2) (PKonst p2) vars = matchPattern d2 p2 vars
matchFun (Ident d1) (PIdent p1) vars = matchPattern d1 p1 vars
matchFun _           _          _    = Nothing

----------------------------------------------------------------
----------------------------------------------------------- fin.
