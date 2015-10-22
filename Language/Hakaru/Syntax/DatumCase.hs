{-# LANGUAGE CPP
           , DataKinds
           , PolyKinds
           , GADTs
           , StandaloneDeriving
           , TypeOperators
           , TypeFamilies
           , Rank2Types
           , ScopedTypeVariables
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.22
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

import Data.Proxy (Proxy(..)) -- TODO: Is this in Prelude for modern GHC?

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.AST (AST(Datum_, Value_), Value(VDatum))
import Language.Hakaru.Syntax.ABT
import qualified Language.Hakaru.Syntax.Prelude as P

----------------------------------------------------------------
----------------------------------------------------------------

data MatchResult :: ([Hakaru] -> Hakaru -> *) -> [Hakaru] -> Hakaru -> * where
    -- TODO: actually store information inside GotStuck so we can
    -- force the appropriate expression and continue without needing
    -- to backtrack and redo what we've already done. (Of course,
    -- until we factor @[Branch]@ into a single pattern automaton,
    -- getting stuck in one branch doesn't tell us enough to avoid
    -- restarting.)
    --
    -- | For when we encounter free variables and non-head-normal forms.
    GotStuck :: MatchResult abt vars a

    -- | We successfully matched everything (so far). The @vars2@
    -- are for tracking variables bound by the future\/rest of the
    -- pattern (i.e., for recursing into the left part of a product,
    -- @vars2@ are the variables in the right part of the product).
    Matched
        :: DList1 (Pair1 Variable (abt '[])) vars1
        -> !(abt vars2 a)
        -> MatchResult abt vars2 a


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
    case eqAppendNil (secondProxy body) of
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
    PWild              -> Just (Matched dnil1 body)
    PVar               ->
        caseBind body $ \x body' ->
            Just (Matched (dsingleton1 (Pair1 x e)) body')
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
        Value_ (VDatum d) -> Just (fmap11 P.value_ d)
        Datum_         d  -> Just d
        _                 -> Nothing


matchCode
    :: (ABT abt)
    => DatumCode  xss (abt '[]) (HData' t)
    -> PDatumCode xss vars1     (HData' t)
    -> abt (vars1 ++ vars2)  b
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
matchStruct Done       PDone       body = Just (Matched dnil1 body)
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
                Matched ys body'' -> Matched (xs `dappend1` ys) body''
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
