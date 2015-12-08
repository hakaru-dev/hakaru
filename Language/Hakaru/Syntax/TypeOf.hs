{-# LANGUAGE CPP
           , DataKinds
           , GADTs
           , EmptyCase
           , FlexibleContexts
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.11.23
-- |
-- Module      :  Language.Hakaru.Syntax.TypeOf
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- BUG: can't put this in "Language.Hakaru.Syntax.TypeHelpers" because of some sort of cyclic dependency...
----------------------------------------------------------------
module Language.Hakaru.Syntax.TypeOf
    ( typeOf
    ) where

import qualified Data.Foldable as F
#if __GLASGOW_HASKELL__ < 710
import Data.Functor ((<$>))
#endif

import Language.Hakaru.Syntax.Sing (Sing(..))
import Language.Hakaru.Syntax.Coercion
    (singCoerceCod, singCoerceDom, singCoerceFrom, singCoerceTo)
import Language.Hakaru.Syntax.TypeHelpers
    (sing_PrimOp, sing_MeasureOp, sing_NaryOp, sing_Literal)
import Language.Hakaru.Syntax.Datum (Branch(..))
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Variable (varType)
import Language.Hakaru.Syntax.ABT (ABT, caseVarSyn, caseBind, caseBinds)

----------------------------------------------------------------
----------------------------------------------------------------

typeOf :: (ABT Term abt) => abt '[] a -> Sing a
typeOf e0 =
    case typeOf_ e0 of
    Left  err -> error $ "typeOf: " ++ err
    Right typ -> typ


typeOf_ :: (ABT Term abt) => abt '[] a -> Either String (Sing a)
typeOf_ e0 =
    caseVarSyn e0 (return . varType) $ \t ->
        case t of
        Lam_ :$ e1 :* End ->
            caseBind e1 $ \x e1' ->
                SFun (varType x) <$> typeOf_ e1'
        App_ :$ e1 :* _ :* End -> do
            typ1 <- typeOf_ e1
            case typ1 of
                SFun _ typ3 -> return typ3
                typ1'       -> case typ1' of {} -- The impossible happened
        Let_ :$ _  :* e2 :* End   -> caseBind e2 (const typeOf_)
        Ann_      typ :$ _        -> return typ
        CoerceTo_   c :$ e1 :* End ->
            case singCoerceCod c of
            Nothing  -> singCoerceTo c <$> typeOf_ e1
            Just typ -> return typ
        UnsafeFrom_ c :$ e1 :* End ->
            case singCoerceDom c of
            Nothing  -> singCoerceFrom c <$> typeOf_ e1
            Just typ -> return typ
        PrimOp_     o :$ _        -> return . snd $ sing_PrimOp o
        MeasureOp_  o :$ _        -> return . SMeasure . snd $ sing_MeasureOp o
        Dirac  :$ e1 :* End       -> SMeasure <$> typeOf_ e1
        MBind  :$ _  :* e2 :* End -> caseBind e2 (const typeOf_)
        Expect :$ _               -> return SProb
        
        NaryOp_  o  _  -> return $ sing_NaryOp o
        Literal_ v     -> return $ sing_Literal v
        Empty_   typ   -> return typ
        Array_   _  e2 -> caseBind e2 $ \_ e2' -> SArray <$> typeOf_ e2'
        Datum_   d     -> error "TODO: typeOf_{Datum_}"
        Case_    _  bs -> tryAll "Case_" typeOfBranch bs
        Superpose_ pes -> tryAll "Superpose_" (typeOf_ . snd) pes
        
        _ :$ _ -> error "typeOf_: the impossible happened"


typeOfBranch :: (ABT Term abt) => Branch a abt b -> Either String (Sing b)
typeOfBranch (Branch _ e0) = typeOf_ . snd $ caseBinds e0


tryAll
    :: F.Foldable f
    => String
    -> (a -> Either String b)
    -> f a
    -> Either String b
tryAll name f =
    F.foldr step (Left $ "no unique type for " ++ name)
    where
    step x rest =
        case f x of
        r@(Right _) -> r
        Left _      -> rest

----------------------------------------------------------------
----------------------------------------------------------- fin.
