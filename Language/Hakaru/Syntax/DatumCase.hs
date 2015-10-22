{-# LANGUAGE CPP
           , DataKinds
           , PolyKinds
           , GADTs
           , StandaloneDeriving
           , TypeOperators
           , TypeFamilies
           , Rank2Types
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
    (
    -- * Helper types
      Some(..)
    , Pair1(..)
    , DList1(..), runDList1, dnil1, dcons1, dappend1

    -- * Reduction of case analysis
    , MatchResult(..)
    , matchPatterns
    , matchPattern
    ) where

import Unsafe.Coerce (unsafeCoerce) -- TODO: move the stuff that uses this off to a separate file
#if __GLASGOW_HASKELL__ < 710
import Data.Monoid   hiding (Sum)
#endif

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.AST (AST(Datum_, Value_), Value(VDatum))
import Language.Hakaru.Syntax.ABT
import qualified Language.Hakaru.Syntax.Prelude as P

----------------------------------------------------------------
----------------------------------------------------------------

-- | Existentially quantify over an index.
-- TODO: move elsewhere.
-- TODO: replace 'SomeVariable' with @(Some Variable)@
data Some :: (k -> *) -> * where
    Some :: !(f a) -> Some f


data Pair1 (f :: k -> *) (g :: k -> *) (i :: k) = Pair1 !(f i) !(g i)


-- TODO: move 'DList1' and all associated things somewhere else (e.g., IClasses.hs)
newtype DList1 a xs =
    DList1 { unDList1 :: forall ys. List1 a ys -> List1 a (xs ++ ys) }

runDList1 :: DList1 a xs -> List1 a xs
runDList1 dx@(DList1 xs) =
    case eqAppendNil dx of
    Refl -> xs Nil1

toDList1 :: List1 a xs -> DList1 a xs
toDList1 xs = DList1 (append1 xs) -- N.B., can't use (.) here

append1 :: List1 a xs -> List1 a ys -> List1 a (xs ++ ys)
append1 Nil1         ys = ys
append1 (Cons1 x xs) ys = Cons1 x (append1 xs ys)

dnil1 :: DList1 a '[]
dnil1 = DList1 id

dcons1 :: a x -> DList1 a '[ x ]
dcons1 x = DList1 (Cons1 x)

dappend1 :: DList1 a xs -> DList1 a ys -> DList1 a (xs ++ ys)
dappend1 dx@(DList1 xs) dy@(DList1 ys) =
    DList1 $ \zs ->
        case eqAppendAssoc dx dy zs of
        Refl -> xs (ys zs)

{-
instance Show1 a => Show1 (DList1 a) where
    showsPrec1 p xs =

instance Show1 a => Show (DList1 a xs) where
    showsPrec = showsPrec1
    show      = show1

instance JmEq1 a => JmEq1 (DList1 a) where
    jmEq1 xs ys = 
    
instance Eq1 a => Eq1 (DList1 a) where
    eq1 xs ys = 

instance Eq1 a => Eq (DList1 a xs) where
    (==) = eq1

instance Functor11 DList1 where
    fmap11 f xs =

instance Foldable11 DList1 where
    foldMap11 f xs =
-}

----------------------------------------------------------------
data MatchResult :: ([Hakaru] -> Hakaru -> *) -> [Hakaru] -> Hakaru -> * where
    MatchFail  :: MatchResult abt vars a
    MatchStuck :: MatchResult abt vars a
    Matched
        :: DList1 (Pair1 Variable (abt '[])) vars1
        -> !(abt vars2 a)
        -> MatchResult abt (vars1 ++ vars2) a


matchPatterns
    :: (ABT abt)
    => abt '[] a
    -> [Branch a abt b]
    -> Maybe (MatchResult abt '[] b)
matchPatterns e bs0 = go id bs0
    where
    go _  []     = Nothing
    go ps (b:bs) =
        case b of
        Branch pat body ->
            let  m = matchPattern e pat body in
            case m of
            MatchFail   -> go (ps . (b:)) bs
            MatchStuck  -> Just m
            Matched _ _ -> Just m


matchPattern
    :: (ABT abt)
    => abt '[] a
    -> Pattern vars a
    -> abt vars b
    -> MatchResult abt vars b
matchPattern e pat body =
    case pat of
    PWild              -> Matched dnil1 body
    PVar               ->
        caseBind body $ \x body' ->
            Matched (dcons1 (Pair1 x e)) body'
    PDatum _hint1 pat1 ->
        caseVarSyn e (const MatchStuck) $ \t ->
            case t of
            Value_ (VDatum (Datum _hint2 d)) ->
                matchCode (fmap11 P.value_ d) pat1 body
            Datum_         (Datum _hint2 d)  ->
                matchCode d pat1 body
            _                                -> MatchStuck


matchCode
    :: (ABT abt)
    => DatumCode  xss (abt '[]) (HData' t)
    -> PDatumCode xss vars      (HData' t)
    -> abt vars b
    -> MatchResult abt vars b
matchCode (Inr d2) (PInr p2) body = matchCode   d2 p2 body
matchCode (Inl d1) (PInl p1) body = matchStruct d1 p1 body
matchCode _        _         _    = MatchFail


matchStruct
    :: (ABT abt)
    => DatumStruct  xs (abt '[]) (HData' t)
    -> PDatumStruct xs vars      (HData' t)
    -> abt vars b
    -> MatchResult abt vars b
matchStruct Done       PDone       body = Matched dnil1 body
matchStruct (Et d1 d2) (PEt p1 p2) body =
    error "TODO: matchStruct"
    {-
    case matchFun d1 p1 body of -- BUG: needs type coercion
    MatchFail        -> MatchFail
    MatchStuck       -> MatchStuck
    Matched xs body' -> 
        case matchStruct d2 p2 body' of -- BUG: needs type coercion
        MatchFail         -> MatchFail
        MatchStuck        -> MatchStuck
        Matched ys body'' -> Matched (xs `dappend1` ys) body''
    -}
matchStruct _ _ _ = MatchFail

matchFun
    :: (ABT abt)
    => DatumFun  x (abt '[]) (HData' t)
    -> PDatumFun x vars      (HData' t)
    -> abt vars b
    -> MatchResult abt vars b
matchFun (Konst d2) (PKonst p2) body = matchPattern d2 p2 body
matchFun (Ident d1) (PIdent p1) body = matchPattern d1 p1 body
matchFun _           _          _    = MatchFail

----------------------------------------------------------------
----------------------------------------------------------- fin.
