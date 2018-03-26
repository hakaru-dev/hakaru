{-# LANGUAGE CPP, GADTs #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.12.19
-- |
-- Module      :  Language.Hakaru.Syntax.AST.Sing
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Factored out from "Language.Hakaru.Syntax.AST".
--
-- TODO: if we're not going to have this in "Language.Hakaru.Syntax.AST", then we should rename it to @Language.Hakaru.Syntax.AST.Sing@ or the like.
----------------------------------------------------------------
module Language.Hakaru.Syntax.AST.Sing
    ( sing_NaryOp
    , sing_PrimOp
    , sing_ArrayOp
    , sing_MeasureOp
    , sing_Literal
    ) where

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Types.Sing
import Language.Hakaru.Syntax.AST

----------------------------------------------------------------
----------------------------------------------------------------

-- N.B., we do case analysis so that we don't need the class constraint!
sing_Literal :: Literal a -> Sing a
sing_Literal (LNat  _) = sing
sing_Literal (LInt  _) = sing
sing_Literal (LProb _) = sing
sing_Literal (LReal _) = sing

-- TODO: we don't need to store the HOrd\/HSemiring values here,
-- we can recover them by typeclass, just like we use 'sing' to get
-- 'sBool' for the other ones...
sing_NaryOp :: NaryOp a -> Sing a
sing_NaryOp And            = sing
sing_NaryOp Or             = sing
sing_NaryOp Xor            = sing
sing_NaryOp Iff            = sing
sing_NaryOp (Min  theOrd)  = sing_HOrd      theOrd
sing_NaryOp (Max  theOrd)  = sing_HOrd      theOrd
sing_NaryOp (Sum  theSemi) = sing_HSemiring theSemi
sing_NaryOp (Prod theSemi) = sing_HSemiring theSemi

-- TODO: is there any way to define a @sing_List1@ like @sing@ for automating all these monomorphic cases?
sing_PrimOp :: PrimOp typs a -> (List1 Sing typs, Sing a)
sing_PrimOp Not          = (sing `Cons1` Nil1, sing)
sing_PrimOp Impl         = (sing `Cons1` sing `Cons1` Nil1, sing)
sing_PrimOp Diff         = (sing `Cons1` sing `Cons1` Nil1, sing)
sing_PrimOp Nand         = (sing `Cons1` sing `Cons1` Nil1, sing)
sing_PrimOp Nor          = (sing `Cons1` sing `Cons1` Nil1, sing)
sing_PrimOp Pi           = (Nil1, sing)
sing_PrimOp Sin          = (sing `Cons1` Nil1, sing)
sing_PrimOp Cos          = (sing `Cons1` Nil1, sing)
sing_PrimOp Tan          = (sing `Cons1` Nil1, sing)
sing_PrimOp Asin         = (sing `Cons1` Nil1, sing)
sing_PrimOp Acos         = (sing `Cons1` Nil1, sing)
sing_PrimOp Atan         = (sing `Cons1` Nil1, sing)
sing_PrimOp Sinh         = (sing `Cons1` Nil1, sing)
sing_PrimOp Cosh         = (sing `Cons1` Nil1, sing)
sing_PrimOp Tanh         = (sing `Cons1` Nil1, sing)
sing_PrimOp Asinh        = (sing `Cons1` Nil1, sing)
sing_PrimOp Acosh        = (sing `Cons1` Nil1, sing)
sing_PrimOp Atanh        = (sing `Cons1` Nil1, sing)
sing_PrimOp RealPow      = (sing `Cons1` sing `Cons1` Nil1, sing)
sing_PrimOp Choose       = (sing `Cons1` sing `Cons1` Nil1, sing)
sing_PrimOp Exp          = (sing `Cons1` Nil1, sing)
sing_PrimOp Log          = (sing `Cons1` Nil1, sing)
sing_PrimOp Floor        = (sing `Cons1` Nil1, sing)
sing_PrimOp (Infinity h) = (Nil1, sing_HIntegrable h)
sing_PrimOp GammaFunc    = (sing `Cons1` Nil1, sing)
sing_PrimOp BetaFunc     = (sing `Cons1` sing `Cons1` Nil1, sing)
-- Mere case analysis isn't enough for the rest of these, because
-- of the class constraints. We fix that by various helper functions
-- on explicit dictionary passing.
--
-- TODO: is there any way to automate building these from their
-- respective @a@ proofs?
sing_PrimOp (Equal theEq) =
    let a = sing_HEq theEq
    in  (a `Cons1` a `Cons1` Nil1, sBool)
sing_PrimOp (Less theOrd) =
    let a = sing_HOrd theOrd
    in  (a `Cons1` a `Cons1` Nil1, sBool)
sing_PrimOp (NatPow theSemi) =
    let a = sing_HSemiring theSemi
    in  (a `Cons1` SNat `Cons1` Nil1, a)
sing_PrimOp (Negate theRing) =
    let a = sing_HRing theRing
    in  (a `Cons1` Nil1, a)
sing_PrimOp (Abs theRing) =
    let a = sing_HRing theRing
        b = sing_NonNegative theRing
    in  (a `Cons1` Nil1, b)
sing_PrimOp (Signum theRing) =
    let a = sing_HRing theRing
    in  (a `Cons1` Nil1, a)
sing_PrimOp (Recip theFrac) =
    let a = sing_HFractional theFrac
    in  (a `Cons1` Nil1, a)
sing_PrimOp (NatRoot theRad) =
    let a = sing_HRadical theRad
    in  (a `Cons1` SNat `Cons1` Nil1, a)
sing_PrimOp (Erf theCont) =
    let a = sing_HContinuous theCont
    in  (a `Cons1` Nil1, a)


sing_ArrayOp :: ArrayOp typs a -> (List1 Sing typs, Sing a)
sing_ArrayOp (Index  a) = (SArray a `Cons1` SNat `Cons1` Nil1, a)
sing_ArrayOp (Size   a) = (SArray a `Cons1` Nil1, SNat)
sing_ArrayOp (Reduce a) =
    ((a `SFun` a `SFun` a) `Cons1` a `Cons1` SArray a `Cons1` Nil1, a)


sing_MeasureOp :: MeasureOp typs a -> (List1 Sing typs, Sing a)
sing_MeasureOp Lebesgue    = (sing `Cons1` sing `Cons1` Nil1, sing)
sing_MeasureOp Counting    = (Nil1, sing)
sing_MeasureOp Categorical = (sing `Cons1` Nil1, sing)
sing_MeasureOp Uniform     = (sing `Cons1` sing `Cons1` Nil1, sing)
sing_MeasureOp Normal      = (sing `Cons1` sing `Cons1` Nil1, sing)
sing_MeasureOp Poisson     = (sing `Cons1` Nil1, sing)
sing_MeasureOp Gamma       = (sing `Cons1` sing `Cons1` Nil1, sing)
sing_MeasureOp Beta        = (sing `Cons1` sing `Cons1` Nil1, sing)

----------------------------------------------------------------
----------------------------------------------------------- fin.
