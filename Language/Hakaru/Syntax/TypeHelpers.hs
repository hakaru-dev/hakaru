{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.22
-- |
-- Module      :  Language.Hakaru.Syntax.TypeHelpers
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Factored out from "Language.Hakaru.Syntax.AST"
----------------------------------------------------------------
module Language.Hakaru.Syntax.TypeHelpers
    ( sing_NaryOp
    , sing_PrimOp
    , sing_MeasureOp
    , sing_Value
    ) where

import Data.Number.LogFloat            (logFloat)

import Language.Hakaru.Syntax.Nat      (unsafeNat)
import Language.Hakaru.Syntax.IClasses (List1(..), Some1(..))
import Language.Hakaru.Syntax.HClasses
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum

import qualified Language.Hakaru.Parser.AST as U
----------------------------------------------------------------
----------------------------------------------------------------

-- N.B., we do case analysis so that we don't need the class constraint!
sing_Value :: Value a -> Sing a
sing_Value (VNat   _) = sing
sing_Value (VInt   _) = sing
sing_Value (VProb  _) = sing
sing_Value (VReal  _) = sing
sing_Value (VDatum (Datum hint d)) = error "TODO: sing_Value{VDatum}"
    {-
    -- @fmap1 sing_Value d@ gets us halfway there, but then what....
    -- This seems vaguely on the right track; but how can we get
    -- it to actually typecheck? Should we just have VDatum (or
    -- Datum) store the Sing when it's created?
    SData sing (goC d)
    where
    goC :: DatumCode xss Value a -> Sing xss
    goC (Inr d1)   = SPlus sing (goS d1)
    goC (Inl d1)   = SPlus (goC d1) sing

    goS :: DatumStruct xs Value a -> Sing xs
    goS (Et d1 d2) = SEt (goF d1) (goS d2)
    goS Done       = SDone

    goF :: DatumFun x Value a -> Sing x
    goF (Konst e1) = SKonst (sing_Value e1)
    goF (Ident e1) = SIdent -- @sing_Value e1@ is what the first argument to SData should be; assuming we actually make it to this branch...
    -}

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
sing_PrimOp :: PrimOp args a -> (List1 Sing args, Sing a)
sing_PrimOp Not        = (sing `Cons1` Nil1, sing)
sing_PrimOp Impl       = (sing `Cons1` sing `Cons1` Nil1, sing)
sing_PrimOp Diff       = (sing `Cons1` sing `Cons1` Nil1, sing)
sing_PrimOp Nand       = (sing `Cons1` sing `Cons1` Nil1, sing)
sing_PrimOp Nor        = (sing `Cons1` sing `Cons1` Nil1, sing)
sing_PrimOp Pi         = (Nil1, sing)
sing_PrimOp Sin        = (sing `Cons1` Nil1, sing)
sing_PrimOp Cos        = (sing `Cons1` Nil1, sing)
sing_PrimOp Tan        = (sing `Cons1` Nil1, sing)
sing_PrimOp Asin       = (sing `Cons1` Nil1, sing)
sing_PrimOp Acos       = (sing `Cons1` Nil1, sing)
sing_PrimOp Atan       = (sing `Cons1` Nil1, sing)
sing_PrimOp Sinh       = (sing `Cons1` Nil1, sing)
sing_PrimOp Cosh       = (sing `Cons1` Nil1, sing)
sing_PrimOp Tanh       = (sing `Cons1` Nil1, sing)
sing_PrimOp Asinh      = (sing `Cons1` Nil1, sing)
sing_PrimOp Acosh      = (sing `Cons1` Nil1, sing)
sing_PrimOp Atanh      = (sing `Cons1` Nil1, sing)
sing_PrimOp RealPow    = (sing `Cons1` sing `Cons1` Nil1, sing)
sing_PrimOp Exp        = (sing `Cons1` Nil1, sing)
sing_PrimOp Log        = (sing `Cons1` Nil1, sing)
sing_PrimOp Infinity   = (Nil1, sing)
sing_PrimOp NegativeInfinity = (Nil1, sing)
sing_PrimOp GammaFunc  = (sing `Cons1` Nil1, sing)
sing_PrimOp BetaFunc   = (sing `Cons1` sing `Cons1` Nil1, sing)
sing_PrimOp Integrate  = (sing `Cons1` sing `Cons1` sing `Cons1` Nil1, sing)
sing_PrimOp Summate    = (sing `Cons1` sing `Cons1` sing `Cons1` Nil1, sing)
-- Mere case analysis isn't enough for the rest of these, because
-- of the class constraints. We fix that by various helper functions
-- on explicit dictionary passing.
--
-- TODO: is there any way to automate building these from their
-- respective @a@ proofs?
sing_PrimOp (Index  a) = (SArray a `Cons1` SNat `Cons1` Nil1, a)
sing_PrimOp (Size   a) = (SArray a `Cons1` Nil1, SNat)
sing_PrimOp (Reduce a) =
    ((a `SFun` a `SFun` a) `Cons1` a `Cons1` SArray a `Cons1` Nil1, a)
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

sing_MeasureOp :: MeasureOp args a -> (List1 Sing args, Sing a)
sing_MeasureOp (Dirac a)   = (a `Cons1` Nil1, SMeasure a)
sing_MeasureOp Lebesgue    = (Nil1, sing)
sing_MeasureOp Counting    = (Nil1, sing)
sing_MeasureOp Categorical = (sing `Cons1` Nil1, sing)
sing_MeasureOp Uniform     = (sing `Cons1` sing `Cons1` Nil1, sing)
sing_MeasureOp Normal      = (sing `Cons1` sing `Cons1` Nil1, sing)
sing_MeasureOp Poisson     = (sing `Cons1` Nil1, sing)
sing_MeasureOp Gamma       = (sing `Cons1` sing `Cons1` Nil1, sing)
sing_MeasureOp Beta        = (sing `Cons1` sing `Cons1` Nil1, sing)
sing_MeasureOp (DirichletProcess a) =
    ( SProb `Cons1` SMeasure a `Cons1` Nil1
    , SMeasure (SMeasure a))
sing_MeasureOp (Plate a)   =
    (SArray (SMeasure a) `Cons1` Nil1, SMeasure (SArray a))
sing_MeasureOp (Chain s a) =
    ( SArray (s `SFun` SMeasure (sPair a s)) `Cons1` s `Cons1` Nil1
    , SMeasure (sPair (SArray a) s))

----------------------------------------------------------------
----------------------------------------------------------- fin.
