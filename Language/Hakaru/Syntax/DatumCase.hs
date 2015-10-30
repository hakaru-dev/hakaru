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
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.27
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
    ) where

import Data.Proxy (Proxy(..))

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.AST (AST(Datum_, Value_), Value(VDatum))
import Language.Hakaru.Syntax.ABT

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
    (a    :: Hakaru)

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

    -- TODO: internally if we went back to using @DList1 (Pair1 Variable (abt '[])) vars1@ for the first argument, with @vars1@ another parameter to the type, it would guarantee correctness of the number and types of bindings we produce. However, because the user-facing 'matchBranch' uses 'Branch' which existentializes over @vars1@, we'd need our user-facing 'MatchResult' type to also existentialize over @vars1@. But supposing we did go back to doing that for the internal stuff; would it be helpful for anyone else?
    --
    -- | We successfully matched everything (so far). The first
    -- argument gives the bindings for all the pattern variables
    -- we've already checked. The second argument gives the body
    -- of the branch (where @vars@ are the pattern variables remaining
    -- to be bound by checking the remainder of the pattern).
    | Matched
        (DList (Assoc abt))
        !(abt vars a)


type DList a = [a] -> [a]


instance ABT abt => Show (MatchResult abt '[] a) where
    showsPrec p = shows . ppMatchResult p

ppMatchResult :: (ABT abt) => Int -> MatchResult abt '[] a -> Doc
ppMatchResult _ GotStuck = PP.text "GotStuck"
ppMatchResult p (Matched xs body) =
    parens (p > 9)
        (PP.text f <+> PP.nest (1 + length f) (PP.sep
            [ ppList . map (prettyPrecAssoc 11) $ xs []
            , prettyPrec 11 body
            ]))
    where
    f            = "Matched"
    ppList       = PP.brackets . PP.nest 1 . PP.fsep . PP.punctuate PP.comma
    parens True  = PP.parens   . PP.nest 1
    parens False = id



-- | Walk through a list of branches and try matching against them in order.
matchBranches
    :: (ABT abt)
    => abt '[] a
    -> [Branch a abt b]
    -> Maybe (MatchResult abt '[] b)
matchBranches e = go
    where
    go []     = Nothing
    go (b:bs) =
        case matchBranch e b of
        Nothing -> go bs
        Just m  -> Just m


-- | Try matching against a single branch.
matchBranch
    :: (ABT abt)
    => abt '[] a
    -> Branch a abt b
    -> Maybe (MatchResult abt '[] b)
matchBranch e (Branch pat body) =
    case eqAppendIdentity (secondProxy body) of
    Refl -> matchPattern e pat body

secondProxy :: f i j -> Proxy i
secondProxy _ = Proxy


-- | This function must be distinguished from 'matchBranch' since
-- we allow nested patterns. If we enter this function from
-- 'matchBranch' then we know @vars2@ must be @'[]@, but we also
-- enter this function from 'matchFun' where @vars2@ could be
-- anything! Thus, this function gives us the generalize inductive hypothesis needed to define 'matchBranch'.
matchPattern
    :: (ABT abt)
    => abt '[] a
    -> Pattern vars1 a
    -> abt (vars1 ++ vars2)  b
    -> Maybe (MatchResult abt vars2 b)
matchPattern e pat body =
    case pat of
    PWild              -> Just (Matched id body)
    PVar               ->
        caseBind body $ \x body' ->
            Just (Matched (Assoc x e :) body')
    PDatum _hint1 pat1 ->
        case viewDatum e of
        Nothing               -> Just GotStuck
        Just (Datum _hint2 d) -> matchCode d pat1 body


-- HACK: we must give this a top-level binding rather than inlining it. Again, I'm not entirely sure why...
viewDatum
    :: (ABT abt)
    => abt '[] (HData' t)
    -> Maybe (Datum (abt '[]) (HData' t))
viewDatum e =
    caseVarSyn e (const Nothing) $ \t ->
        case t of
        Value_ (VDatum d) -> Just (fmap11 (syn . Value_) d)
        Datum_         d  -> Just d
        _                 -> Nothing


matchCode
    :: (ABT abt)
    => DatumCode  xss (abt '[]) (HData' t)
    -> PDatumCode xss vars1     (HData' t)
    -> abt (vars1 ++ vars2) b
    -> Maybe (MatchResult abt vars2 b)
matchCode (Inr d2) (PInr p2) body = matchCode   d2 p2 body
matchCode (Inl d1) (PInl p1) body = matchStruct d1 p1 body
matchCode _        _         _    = Nothing


matchStruct
    :: forall abt xs t vars1 vars2 b
    .  (ABT abt)
    => DatumStruct  xs (abt '[]) (HData' t)
    -> PDatumStruct xs vars1     (HData' t)
    -> abt (vars1 ++ vars2)  b
    -> Maybe (MatchResult abt vars2 b)
matchStruct Done       PDone       body = Just (Matched id body)
matchStruct (Et d1 d2) (PEt p1 p2) body = do
    m1 <- 
        case eqAppendAssoc
                (secondProxy p1)
                (secondProxy p2)
                (Proxy :: Proxy vars2)
        of
        Refl -> matchFun d1 p1 body
    case m1 of
        GotStuck         -> return GotStuck
        Matched xs body' -> do
            m2 <- matchStruct d2 p2 body'
            return $
                case m2 of
                GotStuck          -> GotStuck
                Matched ys body'' -> Matched (xs . ys) body''
matchStruct _ _ _ = Nothing


matchFun
    :: (ABT abt)
    => DatumFun  x (abt '[]) (HData' t)
    -> PDatumFun x vars1     (HData' t)
    -> abt (vars1 ++ vars2)  b
    -> Maybe (MatchResult abt vars2 b)
matchFun (Konst d2) (PKonst p2) body = matchPattern d2 p2 body
matchFun (Ident d1) (PIdent p1) body = matchPattern d1 p1 body
matchFun _           _          _    = Nothing

----------------------------------------------------------------
----------------------------------------------------------- fin.
