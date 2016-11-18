{-# LANGUAGE GADTs
           , KindSignatures
           , DataKinds
           , ScopedTypeVariables
           , PatternGuards
           , Rank2Types
           , TypeOperators
           , FlexibleContexts
           , UndecidableInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.05.28
-- |
-- Module      :  Language.Hakaru.Pretty.Concrete
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
--
----------------------------------------------------------------
module Language.Hakaru.Pretty.Concrete
    (
    -- * The user-facing API
      pretty
    , prettyPrec
    , prettyType
    , prettyAssoc
    , prettyPrecAssoc
    , prettyValue
    -- * Helper functions (semi-public internal API)
    ) where

import           System.Console.ANSI
import           Text.PrettyPrint                (Doc, (<>), (<+>))
import qualified Text.PrettyPrint                as PP
import qualified Data.Foldable                   as F
import qualified Data.List.NonEmpty              as L
import qualified Data.Text                       as Text

-- Because older versions of "Data.Foldable" do not export 'null' apparently...
import qualified Data.Sequence                   as Seq
import qualified Data.Vector                     as V
import           Data.Ratio

import           Data.Number.Natural  (fromNatural, fromNonNegativeRational)
import           Data.Number.Nat
import qualified Data.Number.LogFloat            as LF

import Language.Hakaru.Syntax.IClasses (fmap11, foldMap11, jmEq1, TypeEq(..))
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.Value
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Pretty.Haskell
    (ppRatio, prettyAssoc, prettyPrecAssoc, Associativity(..))

----------------------------------------------------------------
-- | Pretty-print a term.
pretty :: (ABT Term abt) => abt '[] a -> Doc
pretty = prettyPrec 0


-- | Pretty-print a term at a given precendence level.
prettyPrec :: (ABT Term abt) => Int -> abt '[] a -> Doc
prettyPrec p = toDoc . prettyPrec_ p . LC_

----------------------------------------------------------------
class Pretty (f :: Hakaru -> *) where
    -- | A polymorphic variant if 'prettyPrec', for internal use.
    prettyPrec_ :: Int -> f a -> Docs

type Docs = [Doc] 

-- So far as I can tell from the documentation, if the input is a singleton list then the result is the same as that singleton.
toDoc :: Docs -> Doc
toDoc = PP.cat

-- | Color a Doc
color :: Color -> Doc -> Doc
color c d =
    PP.text (setSGRCode [SetColor Foreground Dull c])
    <> d
    <> PP.text (setSGRCode [Reset])

keyword :: Doc -> Doc
keyword = color Red

-- | Pretty-print a variable.
ppVariable :: Variable (a :: Hakaru) -> Doc
ppVariable x = hint
    where
    hint
        | Text.null (varHint x) = PP.char 'x'  <> (PP.int . fromNat . varID) x -- We used to use '_' but...
        | otherwise             = (PP.text . Text.unpack . varHint) x

ppVariableWithType :: Variable (a :: Hakaru) -> (Doc, Doc)
ppVariableWithType x = (hint, (prettyType 0 . varType) x)
    where
    hint
        | Text.null (varHint x) = PP.char 'x' <> (PP.int . fromNat . varID) x -- We used to use '_' but...
        | otherwise             = (PP.text . Text.unpack . varHint) x

-- BUG: we still use this in a few places. I'm pretty sure they should all actually be 'ppBinder2', in which case we can delete this function and just use that one.
ppBinder :: (ABT Term abt) => abt xs a -> Docs
ppBinder e =
    case go [] (viewABT e) of
    ([],  body) -> body
    (vars,body) -> PP.char '\\' <> PP.sep vars <+> PP.text "-> " : body
    where
    go :: (ABT Term abt) => [Doc] -> View (Term abt) xs a -> ([Doc],Docs)
    go xs (Bind x v) = go (ppVariable x : xs) v
    go xs (Var  x)   = (reverse xs, [ppVariable x])
    go xs (Syn  t)   = (reverse xs, prettyPrec_ 0 (LC_ (syn t)))


ppBinder2 :: (ABT Term abt) => abt xs a -> ([Doc], [Doc], Docs)
ppBinder2 e = unpackVarTypes $ go [] (viewABT e)
    where
    unpackVarTypes (varTypes, body) =
        (map fst varTypes, map snd varTypes, body)

    go :: (ABT Term abt) => [(Doc, Doc)] -> View (Term abt) xs a -> ([(Doc, Doc)],Docs)
    go xs (Bind x v) = go (ppVariableWithType x : xs) v
    go xs (Var  x)   = (reverse xs, [ppVariable x])
    go xs (Syn  t)   = (reverse xs, prettyPrec_ 0 (LC_ (syn t)))


-- TODO: since switching to ABT2, this instance requires -XFlexibleContexts; we should fix that if we can
-- BUG: since switching to ABT2, this instance requires -XUndecidableInstances; must be fixed!
instance (ABT Term abt) => Pretty (LC_ abt) where
  prettyPrec_ p (LC_ e) =
    caseVarSyn e ((:[]) . ppVariable) $ \t ->
        case t of
        o :$ es      -> ppSCon p o es
        NaryOp_ o es ->
            if Seq.null es then identityElement o
            else
                case o of
                  And      -> parens (p > 3)
                              . PP.punctuate (PP.text " && ")
                              . map (prettyPrec 3)
                              $ F.toList es
                  Or       -> parens (p > 2)
                              . PP.punctuate (PP.text " || ")
                              . map (prettyPrec 2)
                              $ F.toList es
                  Xor      -> parens (p > 0)
                              . PP.punctuate (PP.text " != ")
                              . map (prettyPrec 0)
                              $ F.toList es
                -- BUG: even though 'Iff' is associative (in Boolean algebras), we should not support n-ary uses in our *surface* syntax. Because it's too easy for folks to confuse "a <=> b <=> c" with "(a <=> b) /\ (b <=> c)".
                  Iff      -> [F.foldl1 (\a b -> toDoc $ ppFun p "iff" [a, b])
                                         (fmap (toDoc . ppArg) es)]
                  (Min  _) -> [F.foldl1 (\a b -> toDoc $ ppFun p "min" [a, b])
                                         (fmap (toDoc . ppArg) es)]
                  (Max  _) -> [F.foldl1 (\a b -> toDoc $ ppFun p "max" [a, b])
                                          (fmap (toDoc . ppArg) es)]
                  (Sum  _) -> case Seq.viewl es of
                                Seq.EmptyL -> [PP.text "0"]
                                (e' Seq.:< es') -> parens (p > 6) $
                                    F.foldl (\a b -> a ++ (ppNaryOpSum 6 b))
                                            [prettyPrec 6 e']
                                            es'
                  (Prod _) ->  case Seq.viewl es of
                                Seq.EmptyL -> [PP.text "1"]
                                (e' Seq.:< es') -> parens (p > 7) $
                                    F.foldl (\a b -> a ++ (ppNaryOpProd 7 b))
                                            [prettyPrec 7 e']
                                            es'

          where identityElement :: NaryOp a -> Docs
                identityElement And      = [PP.text "true"]
                identityElement Or       = [PP.text "false"]
                identityElement Xor      = [PP.text "false"]
                identityElement Iff      = [PP.text "true"]
                identityElement (Min  _) = error "min can not be used with no arguements"
                identityElement (Max  _) = error "max can not be used with no arguements"
                identityElement (Sum  _) = [PP.text "0"]
                identityElement (Prod _) = [PP.text "1"]

        Literal_ v    -> prettyPrec_ p v
        Empty_   _    -> [PP.text "empty"]
        Array_ e1 e2  ->
            let (vars, _, body) = ppBinder2 e2 in
            [ PP.text "array"
              <+> toDoc vars
              <+> PP.text "of"
              <+> toDoc (ppArg e1)
              <> PP.colon <> PP.space
            , PP.nest 1 (toDoc body)]

        Datum_ d      -> prettyPrec_ p (fmap11 LC_ d)
        Case_  e1 bs  -> parens True $
            -- TODO: should we also add hints to the 'Case_' constructor to know whether it came from 'if_', 'unpair', etc?
            [ PP.text "match"
              <+> (toDoc $ ppArg e1)
              <> PP.colon <> PP.space
            , PP.nest 1 (PP.vcat (map (toDoc . prettyPrec_ 0) bs))
            ]
        Superpose_ pes ->
            PP.punctuate (PP.text " <|> ") $ L.toList $ fmap ppWeight pes
          where ppWeight (w,m)
                    | (PP.render $ pretty w) == "1" =
                        toDoc $ ppArg m
                    | otherwise                 =
                        toDoc $ ppFun p "weight" [pretty w, pretty m]

        Reject_ typ -> [PP.text "reject." <+> prettyType 0 typ]

ppNaryOpSum
    :: forall abt a
    . (ABT Term abt)
    => Int
    -> abt '[] a
    -> Docs
ppNaryOpSum p e =
    caseVarSyn e (const $ prefixToTerm "+" e) $ \t ->
        case t of
        Literal_ (LInt  i) | i < 0 ->      prefixToTerm "-" (syn . Literal_ . LInt  . abs $ i)
        Literal_ (LReal i) | i < 0 ->      prefixToTerm "-" (syn . Literal_ . LReal . abs $ i)
        PrimOp_ (Negate _) :$ e1 :* End -> prefixToTerm "-" e1
        _ -> prefixToTerm "+" e
  where prefixToTerm :: forall a. String -> abt '[] a -> Docs
        prefixToTerm s e = [ PP.space <> PP.text s <> PP.space
                           , prettyPrec p e
                           ]

ppNaryOpProd
    :: forall abt a
    . (ABT Term abt)
    => Int
    -> abt '[] a
    -> Docs
ppNaryOpProd p e =
    caseVarSyn e (const $ prefixToTerm "*" e) $ \t ->
        case t of
        Literal_ (LProb i) | numerator i == 1 -> 
          prefixToTerm "/" (syn . Literal_ . LProb . fromIntegral . denominator $ i)
        Literal_ (LReal i) | numerator i == 1 -> 
          prefixToTerm "/" (syn . Literal_ . LReal . fromIntegral . denominator $ i)
        PrimOp_ (Recip _) :$ e1 :* End -> prefixToTerm "/" e1
        _ -> prefixToTerm "*" e
  where prefixToTerm :: forall a. String -> abt '[] a -> Docs
        prefixToTerm s e = [ PP.space <> PP.text s <> PP.space
                           , prettyPrec p e
                           ]

-- | Pretty-print @(:$)@ nodes in the AST.
ppSCon :: (ABT Term abt) => Int -> SCon args a -> SArgs abt args -> Docs
ppSCon _ Lam_ = \(e1 :* End) ->
    let (vars, types, body) = ppBinder2 e1 in
    [ PP.text "fn" <+> toDoc vars
                   <+> toDoc types
                    <> PP.colon <> PP.space
    , PP.nest 1 (toDoc body)]

--ppSCon p App_ = \(e1 :* e2 :* End) -> ppArg e1 ++ parens True (ppArg e2)
ppSCon _ App_ = \(e1 :* e2 :* End) -> prettyApps e1 e2

ppSCon _ Let_ = \(e1 :* e2 :* End) ->
    {-
    caseBind e2 $ \x e2' ->
        (ppVariable x <+> PP.equals <+> PP.nest n (pretty e1))
        : pretty e2'
    -}
    let (vars, _, body) = ppBinder2 e2 in
    [toDoc vars <+> PP.equals <+> toDoc (ppArg e1)
    PP.$$ (toDoc body)]
{-
ppSCon p (Ann_ typ) = \(e1 :* End) ->
    [toDoc (ppArg e1) <+> PP.text "::" <+> prettyType p typ]
-}

ppSCon p (PrimOp_     o) = \es          -> ppPrimOp     p o es
ppSCon p (ArrayOp_    o) = \es          -> ppArrayOp    p o es
ppSCon p (CoerceTo_   c) = \(e1 :* End) -> ppCoerceTo   p c e1
ppSCon p (UnsafeFrom_ c) = \(e1 :* End) -> ppUnsafeFrom p c e1
ppSCon p (MeasureOp_  o) = \es          -> ppMeasureOp  p o es
ppSCon _ Dirac = \(e1 :* End) -> [PP.text "return" <+> toDoc (ppArg e1)]
ppSCon _ MBind = \(e1 :* e2 :* End) ->
    let (vars, _, body) = ppBinder2 e2 in
    [toDoc vars <+> PP.text "<~" <+> toDoc (ppArg e1)
        PP.$$ (toDoc body)]

ppSCon p Plate = \(e1 :* e2 :* End) ->
    let (vars, types, body) = ppBinder2 e2 in
    [ PP.text "plate"
      <+> toDoc vars
      <+> PP.text "of"
      <+> (toDoc $ ppArg e1)
      <> PP.colon <> PP.space
    , PP.nest 1 (toDoc body)
    ]

ppSCon p Chain = \(e1 :* e2 :* e3 :* End) ->
    ppFun 11 "chain"
        [ toDoc (ppArg e1)
        , toDoc (ppArg e2) <+> PP.char '$'
        , toDoc $ ppBinder e2
        ]

ppSCon p Integrate = \(e1 :* e2 :* e3 :* End) ->
    let (vars, types, body) = ppBinder2 e3 in
    [ PP.text "integrate"
      <+> toDoc vars
      <+> PP.text "from"
      <+> (toDoc $ ppArg e1)
      <+> PP.text "to"
      <+> (toDoc $ ppArg e2)
      <> PP.colon <> PP.space
    , PP.nest 1 (toDoc body)
    ]

ppSCon p (Summate _ _) = \(e1 :* e2 :* e3 :* End) ->
    let (vars, types, body) = ppBinder2 e3 in
    [ PP.text "summate"
      <+> toDoc vars
      <+> PP.text "from"
      <+> (toDoc $ ppArg e1)
      <+> PP.text "to"
      <+> (toDoc $ ppArg e2)
      <> PP.colon <> PP.space
    , PP.nest 1 (toDoc body)
    ]

ppSCon p (Product _ _) = \(e1 :* e2 :* e3 :* End) ->
    let (vars, types, body) = ppBinder2 e3 in
    [ PP.text "product"
      <+> toDoc vars
      <+> PP.text "from"
      <+> (toDoc $ ppArg e1)
      <+> PP.text "to"
      <+> (toDoc $ ppArg e2)
      <> PP.colon <> PP.space
    , PP.nest 1 (toDoc body)
    ]

ppSCon p Expect = \(e1 :* e2 :* End) ->
    let (vars, types, body) = ppBinder2 e2 in
    [ PP.text "expect"
      <+> toDoc vars
      <+> (toDoc . parens True $ ppArg e1)
      <> PP.colon
    , PP.nest 1 (toDoc body)
    ]

ppSCon p Observe = \(e1 :* e2 :* End) ->
    [ PP.text "observe"
      <+> (toDoc $ ppArg e1)
      <+> (toDoc $ ppArg e2)
    ]


ppCoerceTo :: ABT Term abt => Int -> Coercion a b -> abt '[] a -> Docs
ppCoerceTo =
    -- BUG: this may not work quite right when the coercion isn't one of the special named ones...
    \p c e -> ppFun p (prettyShow c) [toDoc $ ppArg e]
    where
    prettyShow (CCons (Signed HRing_Real) CNil)           = "prob2real"
    prettyShow (CCons (Signed HRing_Int)  CNil)           = "nat2int"
    prettyShow (CCons (Continuous HContinuous_Real) CNil) = "int2real"
    prettyShow (CCons (Continuous HContinuous_Prob) CNil) = "nat2prob"
    prettyShow (CCons (Continuous HContinuous_Prob)
        (CCons (Signed HRing_Real) CNil))                 = "nat2real"
    prettyShow (CCons (Signed HRing_Int)
        (CCons (Continuous HContinuous_Real) CNil))       = "nat2real"
    prettyShow c = "coerceTo_ " ++ showsPrec 11 c ""


ppUnsafeFrom :: ABT Term abt => Int -> Coercion a b -> abt '[] b -> Docs
ppUnsafeFrom =
    -- BUG: this may not work quite right when the coercion isn't one of the special named ones...
    \p c e -> ppFun p (prettyShow c) [toDoc $ ppArg e]
    where
    prettyShow (CCons (Signed HRing_Real) CNil) = "real2prob"
    prettyShow (CCons (Signed HRing_Int)  CNil) = "int2nat"
    prettyShow c = "unsafeFrom_ " ++ showsPrec 11 c ""


-- | Pretty-print a type.
prettyType :: Int -> Sing (a :: Hakaru) -> Doc
prettyType _ SNat         = PP.text "nat"
prettyType _ SInt         = PP.text "int"
prettyType _ SProb        = PP.text "prob"
prettyType _ SReal        = PP.text "real"
prettyType p (SMeasure a) = PP.text "measure" <> PP.parens (prettyType p a)
prettyType p (SArray   a) = PP.text "array" <> PP.parens (prettyType p a)
prettyType p (SFun   a b) = prettyType p a <+> PP.text "->" <+> prettyType p b  
prettyType p typ          =
    case typ of
    SData (STyCon sym `STyApp` a `STyApp` b) _
      | Just Refl <- jmEq1 sym sSymbol_Pair
      -> toDoc $ ppFun p "pair" [prettyType p a, prettyType p b]
      | Just Refl <- jmEq1 sym sSymbol_Either
      -> toDoc $ ppFun p "either" [prettyType p a, prettyType p b]
    SData (STyCon sym `STyApp` a) _
      | Just Refl <- jmEq1 sym sSymbol_Maybe
      -> toDoc $ ppFun p "maybe" [prettyType p a]
    SData (STyCon sym) _
      | Just Refl <- jmEq1 sym sSymbol_Bool
      -> PP.text "bool"
      | Just Refl <- jmEq1 sym sSymbol_Unit
      -> PP.text "unit"
    _ -> PP.text (showsPrec 11 typ "")


-- | Pretty-print a 'PrimOp' @(:$)@ node in the AST.
ppPrimOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => Int -> PrimOp typs a -> SArgs abt args -> Docs
ppPrimOp p Not  = \(e1 :* End)       -> ppApply1 p "not" e1
ppPrimOp p Impl = \(e1 :* e2 :* End) ->
    -- TODO: make prettier
    ppFun p "syn"
        [ toDoc $ ppFun 11 "Impl"
            [ toDoc $ ppArg e1
            , toDoc $ ppArg e2
            ]]
ppPrimOp p Diff = \(e1 :* e2 :* End) ->
    -- TODO: make prettier
    ppFun p "syn"
        [ toDoc $ ppFun 11 "Diff"
            [ toDoc $ ppArg e1
            , toDoc $ ppArg e2
            ]]
ppPrimOp p Nand = \(e1 :* e2 :* End) -> ppApply2 p "nand" e1 e2 -- TODO: make infix...
ppPrimOp p Nor  = \(e1 :* e2 :* End) -> ppApply2 p "nor" e1 e2 -- TODO: make infix...
ppPrimOp _ Pi        = \End               -> [PP.text "pi"]
ppPrimOp p Sin       = \(e1 :* End)       -> ppApply1 p "sin"   e1
ppPrimOp p Cos       = \(e1 :* End)       -> ppApply1 p "cos"   e1
ppPrimOp p Tan       = \(e1 :* End)       -> ppApply1 p "tan"   e1
ppPrimOp p Asin      = \(e1 :* End)       -> ppApply1 p "asin"  e1
ppPrimOp p Acos      = \(e1 :* End)       -> ppApply1 p "acos"  e1
ppPrimOp p Atan      = \(e1 :* End)       -> ppApply1 p "atan"  e1
ppPrimOp p Sinh      = \(e1 :* End)       -> ppApply1 p "sinh"  e1
ppPrimOp p Cosh      = \(e1 :* End)       -> ppApply1 p "cosh"  e1
ppPrimOp p Tanh      = \(e1 :* End)       -> ppApply1 p "tanh"  e1
ppPrimOp p Asinh     = \(e1 :* End)       -> ppApply1 p "asinh" e1
ppPrimOp p Acosh     = \(e1 :* End)       -> ppApply1 p "acosh" e1
ppPrimOp p Atanh     = \(e1 :* End)       -> ppApply1 p "atanh" e1
ppPrimOp p RealPow   = \(e1 :* e2 :* End) -> ppBinop "**" 8 RightAssoc p e1 e2
ppPrimOp p Exp       = \(e1 :* End)       -> ppApply1 p "exp"   e1
ppPrimOp p Log       = \(e1 :* End)       -> ppApply1 p "log"   e1
ppPrimOp _ (Infinity _) = \End               -> [PP.text "∞"]
ppPrimOp p GammaFunc    = \(e1 :* End)       -> ppApply1 p "gammaFunc" e1
ppPrimOp p BetaFunc     = \(e1 :* e2 :* End) -> ppApply2 p "betaFunc" e1 e2

ppPrimOp p (Equal   _) = \(e1 :* e2 :* End) -> ppBinop "==" 4 NonAssoc   p e1 e2
ppPrimOp p (Less    _) = \(e1 :* e2 :* End) -> ppBinop "<"  4 NonAssoc   p e1 e2
ppPrimOp p (NatPow  _) = \(e1 :* e2 :* End) -> ppBinop "^"  8 RightAssoc p e1 e2
ppPrimOp p (Negate  _) = \(e1 :* End)       -> ppApply1  p "negate"  e1
ppPrimOp p (Abs     _) = \(e1 :* End)       -> ppApply1  p "abs"     e1
ppPrimOp p (Signum  _) = \(e1 :* End)       -> ppApply1  p "signum"  e1
ppPrimOp p (Recip   _) = \(e1 :* End)       -> ppApply1  p "recip"   e1
ppPrimOp p (NatRoot _) = \(e1 :* e2 :* End) -> ppNatRoot p e1 e2
ppPrimOp p (Erf _)     = \(e1 :* End)       -> ppApply1  p "erf"     e1


ppNatRoot
    :: (ABT Term abt)
    => Int
    -> abt '[] a
    -> abt '[] 'HNat
    -> Docs
ppNatRoot p e1 e2 =
    caseVarSyn e2 (\x -> ppApply2 p "natroot" e1 e2) $ \t ->
        case t of
          Literal_ (LNat 2) -> ppApply1 p "sqrt"    e1
          _                 -> ppApply2 p "natroot" e1 e2


-- | Pretty-print a 'ArrayOp' @(:$)@ node in the AST.
ppArrayOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => Int -> ArrayOp typs a -> SArgs abt args -> Docs
ppArrayOp p (Index   _) = \(e1 :* e2 :* End) ->
    [(toDoc $ parensIf (isArray e1) $ ppArg e1) <>
     PP.text "["        <>
     (toDoc $ ppArg e2) <>
     PP.text "]"]
  where isArray e = caseVarSyn e (const False) $ \t ->
                      case t of
                      Array_ _ _ -> True
                      _          -> False
        parensIf True  e = parens True e
        parensIf False e = e

ppArrayOp p (Size    _) = \(e1 :* End)       -> ppApply1 p "size" e1
ppArrayOp p (Reduce  _) = \(e1 :* e2 :* e3 :* End) ->
    ppFun p "reduce"
        [ toDoc $ ppArg e1 -- N.B., @e1@ uses lambdas rather than being a binding form!
        , toDoc $ ppArg e2
        , toDoc $ ppArg e3
        ]


-- | Pretty-print a 'MeasureOp' @(:$)@ node in the AST.
ppMeasureOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => Int -> MeasureOp typs a -> SArgs abt args -> Docs
ppMeasureOp _ Lebesgue    = \End           -> [PP.text "lebesgue"]
ppMeasureOp _ Counting    = \End           -> [PP.text "counting"]
ppMeasureOp p Categorical = \(e1 :* End)   -> ppApply1 p "categorical" e1
ppMeasureOp p Uniform = \(e1 :* e2 :* End) -> ppApply2 p "uniform"     e1 e2
ppMeasureOp p Normal  = \(e1 :* e2 :* End) -> ppApply2 p "normal"      e1 e2
ppMeasureOp p Poisson = \(e1 :* End)       -> ppApply1 p "poisson"     e1
ppMeasureOp p Gamma   = \(e1 :* e2 :* End) -> ppApply2 p "gamma"       e1 e2
ppMeasureOp p Beta    = \(e1 :* e2 :* End) -> ppApply2 p "beta"        e1 e2

-- BUG: doubles may not properly and unambiguously represent the correct rational! Consider using 'ppRatio' instead.
instance Pretty Literal where
    prettyPrec_ _ (LNat  n) = [PP.integer (fromNatural n)]
    prettyPrec_ _ (LInt  i) = [PP.integer i]
    prettyPrec_ p (LProb l) =
        [ppRatio p $ fromNonNegativeRational l]
    prettyPrec_ p (LReal r) = [ppRatio p r]

instance Pretty Value where
    prettyPrec_ _ (VNat  n)    = [PP.int (fromNat n)]
    prettyPrec_ _ (VInt  i)    = [PP.int i]
    prettyPrec_ _ (VProb l)    =
        [PP.double $ LF.fromLogFloat l]
    prettyPrec_ _ (VReal r)    = [PP.double r]
    prettyPrec_ p (VDatum d)   = prettyPrec_ p d
    prettyPrec_ _ (VLam _)     = [PP.text "<function>"]
    prettyPrec_ _ (VMeasure _) = [PP.text "<measure>"]
    prettyPrec_ p (VArray a)   =
        ppList . V.toList $ V.map (toDoc . prettyPrec_ p) a

prettyValue :: Value a -> Doc
prettyValue = toDoc . prettyPrec_ 0

instance Pretty f => Pretty (Datum f) where
    prettyPrec_ p (Datum hint _typ d)
        | Text.null hint =
            ppFun p "datum_"
                [error "TODO: prettyPrec_@Datum"]
        | otherwise =
            case Text.unpack hint of
            -- Special cases for certain datums
            "pair"  -> ppFun p ""
                (foldMap11 ((:[]) . toDoc . prettyPrec_ 11) d) 
            "true"  -> [PP.text "true"]
            "false" -> [PP.text "false"]
            "unit"  -> [PP.text "()"]
            -- General case
            _       -> ppFun p (Text.unpack hint)
                (foldMap11 ((:[]) . toDoc . prettyPrec_ 11) d)
                ++ [PP.text "." <+> prettyType p _typ]


-- HACK: need to pull this out in order to get polymorphic recursion over @xs@
ppPattern :: Int -> [Doc] -> Pattern xs a -> (Docs, [Doc])
ppPattern _ _      PWild = ([PP.text "_"], [])
ppPattern _ (v:vs) PVar  = ([v], vs)
ppPattern p vars   (PDatum hint d0)
    | Text.null hint = error "TODO: prettyPrec_@Pattern"
    | otherwise      =
        case Text.unpack hint of
        -- Special cases for certain pDatums
        "true"  -> ([PP.text "true"],  vars)
        "false" -> ([PP.text "false"], vars)
        "pair"  -> ppFunWithVars p Text.empty
        -- General case
        _        -> ppFunWithVars p hint
    where
    ppFunWithVars p hint = (ppFun p (Text.unpack hint) g, vars')
       where (g, vars') = goCode d0 vars

    goCode :: PDatumCode xss vars a -> [Doc] -> (Docs, [Doc])
    goCode (PInr d) = goCode   d
    goCode (PInl d) = goStruct d

    goStruct :: PDatumStruct xs vars a -> [Doc] -> (Docs, [Doc])
    goStruct PDone       vars  = ([], vars)
    goStruct (PEt d1 d2) vars = (gF ++ gS, vars'')
       where (gF, vars')  = goFun d1 vars
             (gS, vars'') = goStruct d2 vars' 

    goFun :: PDatumFun x vars a -> [Doc] -> (Docs, [Doc])
    goFun (PKonst d) vars = ([toDoc $ fst r], snd r)
       where r = ppPattern 11 vars d
    goFun (PIdent d) vars = ([toDoc $ fst r], snd r)
       where r = ppPattern 11 vars d


instance (ABT Term abt) => Pretty (Branch a abt) where
    -- BUG: we can't actually use the HOAS API here, since we
    --      aren't using a Prelude-defined @branch@...
    -- HACK: don't *always* print parens; pass down the precedence to
    --       'ppBinder' to have them decide if they need to or not.
    prettyPrec_ p (Branch pat e) =
        let (vars, _, body) = ppBinder2 e in
        [ (toDoc . fst $ ppPattern 11 vars pat) <> PP.colon <> PP.space
        , PP.nest 1 $ toDoc $ body
        ]

----------------------------------------------------------------
type DList a = [a] -> [a]

prettyApps :: (ABT Term abt) => abt '[] (a ':-> b) -> abt '[] a -> Docs
prettyApps = \ e1 e2 ->
    case reduceLams e1 e2 of
    Just e2' -> ppArg e2'
    Nothing  ->
      let (d, vars) = collectApps e1 (pretty e2 :) in
      [d <> ppTuple (vars [])]
    where
    reduceLams
        :: (ABT Term abt)
        => abt '[] (a ':-> b) -> abt '[] a -> Maybe (abt '[] b)
    reduceLams e1 e2 =
        caseVarSyn e1 (const Nothing) $ \t ->
            case t of
            Lam_ :$ e1 :* End ->
              caseBind e1 $ \x e1' ->
                Just (subst x e2 e1')
            _                 -> Nothing

    collectApps
        :: (ABT Term abt)
        => abt '[] (a ':-> b) -> DList Doc -> (Doc, DList Doc)
    collectApps e es = 
        caseVarSyn e (\x -> (ppVariable x, es)) $ \t ->
            case t of
            App_ :$ e1 :* e2 :* End -> collectApps e1 ((pretty e2 :) . es)
            _                       -> (pretty e, es)


prettyLams :: (ABT Term abt) => abt '[a] b -> Doc
prettyLams = \e ->
    let (d, vars) = collectLams e id in
    PP.char '\\' <+> PP.sep (vars []) <+> PP.text "->" <+> d
    where
    collectLams
        :: (ABT Term abt)
        => abt '[a] b -> DList Doc -> (Doc, DList Doc)
    collectLams e xs = 
        caseBind e $ \x e' ->
            let xs' = xs . (ppVariable x :) in
            caseVarSyn e' (\y -> (ppVariable y, xs')) $ \t ->
                case t of
                Lam_ :$ e1 :* End -> collectLams e1 xs'
                _                 -> (pretty e', xs')


-- | For the \"@lam $ \x ->\n@\"  style layout.
adjustHead :: (Doc -> Doc) -> Docs -> Docs
adjustHead f []     = [f (toDoc [])]
adjustHead f (d:ds) = f d : ds

parens :: Bool -> Docs -> Docs
parens True  ds = [PP.parens (PP.nest 1 (toDoc ds))]
parens False ds = [PP.parens (toDoc ds)]

ppList :: [Doc] -> Docs
ppList = (:[]) . PP.brackets . PP.nest 1 . PP.fsep . PP.punctuate PP.comma

ppTuple :: [Doc] -> Doc
ppTuple = PP.parens . PP.sep . PP.punctuate PP.comma

-- TODO: why does this take the precedence argument if it doesn't care?
ppFun :: Int -> String -> [Doc] -> Docs
ppFun _ f [] = [PP.text f <> PP.text "()"]
ppFun _ f ds = [PP.text f <> ppTuple ds]

ppArg :: (ABT Term abt) => abt '[] a -> Docs
ppArg = prettyPrec_ 11 . LC_

ppApply1 :: (ABT Term abt) => Int -> String -> abt '[] a -> Docs
ppApply1 p f e1 = ppFun p f [toDoc $ ppArg e1]

ppApply2
    :: (ABT Term abt) => Int -> String -> abt '[] a -> abt '[] b -> Docs
ppApply2 p f e1 e2 = ppFun p f [toDoc $ ppArg e1, toDoc $ ppArg e2]

ppBinop
    :: (ABT Term abt)
    => String -> Int -> Associativity
    -> Int -> abt '[] a -> abt '[] b -> Docs
ppBinop op p0 assoc =
    let (p1,p2) =
            case assoc of
            LeftAssoc  -> (p0, 1 + p0)
            RightAssoc -> (1 + p0, p0)
            NonAssoc   -> (1 + p0, 1 + p0)
    in \p e1 e2 ->
        parens (p > p0)
            [ prettyPrec p1 e1
            , PP.space <> PP.text op <> PP.space
            , prettyPrec p2 e2
            ]

----------------------------------------------------------------
----------------------------------------------------------- fin.
