{-# LANGUAGE GADTs
           , KindSignatures
           , DataKinds
           , ScopedTypeVariables
           , PatternGuards
           , Rank2Types
           , TypeOperators
           , FlexibleContexts
           , UndecidableInstances
           , LambdaCase
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
    , prettyValue
    , prettyT
    , prettyTypeT, prettyTypeS
    -- * Helper functions (semi-public internal API)
    ) where

import           Text.PrettyPrint      (Doc, text, integer, double,
                                        (<+>), (<>), ($$), sep, cat, fsep, vcat,
                                        nest, parens, brackets, punctuate,
                                        comma, colon, equals)
import qualified Data.Foldable         as F
import qualified Data.List.NonEmpty    as L
import qualified Data.Text             as Text

-- Because older versions of "Data.Foldable" do not export 'null' apparently...
import qualified Data.Sequence         as Seq
import qualified Data.Vector           as V
import           Data.Ratio
import qualified Data.Text             as T
import           Control.Applicative   (Applicative(..))

import           Data.Number.Natural   (fromNatural, fromNonNegativeRational)
import           Data.Number.Nat
import qualified Data.Number.LogFloat  as LF

import Language.Hakaru.Syntax.IClasses (fmap11, foldMap11, jmEq1, TypeEq(..)
                                       ,Foldable21(..))
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.Value
import Language.Hakaru.Syntax.Reducer
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Pretty.Haskell (Associativity(..))

----------------------------------------------------------------
-- | Pretty-print a term.
pretty :: (ABT Term abt) => abt '[] a -> Doc
pretty = prettyPrec 0

-- | Pretty print a term as a Text
prettyT :: (ABT Term abt) => abt '[] a -> T.Text
prettyT = T.pack . show . pretty

-- | Pretty-print a type as a Text
prettyTypeT :: Sing (a :: Hakaru) -> T.Text
prettyTypeT = T.pack . show . prettyType 0

-- | Pretty-print a type as a String
prettyTypeS :: Sing (a :: Hakaru) -> String
prettyTypeS = show . prettyType 0

-- | Pretty-print a term at a given precendence level.
prettyPrec :: (ABT Term abt) => Int -> abt '[] a -> Doc
prettyPrec p = prettyPrec_ p . LC_

----------------------------------------------------------------
class Pretty (f :: Hakaru -> *) where
    -- | A polymorphic variant if 'prettyPrec', for internal use.
    prettyPrec_ :: Int -> f a -> Doc

mapInit :: (a -> a) -> [a] -> [a]
mapInit f (x:xs@(_:_)) = f x : mapInit f xs
mapInit _ xs           = xs

sepByR :: String -> [Doc] -> Doc
sepByR s = sep . mapInit (<+> text s)

sepComma :: [Doc] -> Doc
sepComma = fsep . punctuate comma
    -- It's safe to use fsep here despite our indentation-sensitive syntax,
    -- because commas are not a binary operator.

parensIf :: Bool -> Doc -> Doc
parensIf False = id
parensIf True  = parens

-- | Pretty-print a variable.
ppVariable :: Variable (a :: Hakaru) -> Doc
ppVariable x
    | Text.null (varHint x) = text ('x' : show (fromNat (varID x))) -- We used to use '_' but...
    | otherwise             = text (Text.unpack (varHint x))

ppBinder :: (ABT Term abt) => abt xs a -> ([Doc], Doc)
ppBinder e = go [] (viewABT e)
    where
    go :: (ABT Term abt) => [Doc] -> View (Term abt) xs a -> ([Doc], Doc)
    go xs (Bind x v) = go (ppVariable x : xs) v
    go xs (Var  x)   = (reverse xs, ppVariable x)
    go xs (Syn  t)   = (reverse xs, pretty (syn t))

ppBinderAsFun :: forall abt xs a . ABT Term abt => abt xs a -> Doc
ppBinderAsFun e =
  let (vars, body) = ppBinder e in
  if null vars then body else sep [fsep vars <> colon, body]

ppBinder1 :: (ABT Term abt) => abt '[x] a -> (Doc, Doc, Doc)
ppBinder1 e = caseBind e $ \x v ->
              (ppVariable x,
               prettyType 0 (varType x),
               caseVarSyn v ppVariable (pretty . syn))

-- TODO: since switching to ABT2, this instance requires -XFlexibleContexts; we should fix that if we can
-- BUG: since switching to ABT2, this instance requires -XUndecidableInstances; must be fixed!
instance (ABT Term abt) => Pretty (LC_ abt) where
  prettyPrec_ p (LC_ e) =
    caseVarSyn e ppVariable $ \t ->
        case t of
        o :$ es      -> ppSCon p o es
        NaryOp_ o es ->
            if Seq.null es then identityElement o
            else
                case o of
                  And    -> asOp 3 "&&" es
                  Or     -> asOp 2 "||" es
                  Xor    -> asFun "xor" es
                  Iff    -> asFun "iff" es
                  Min  _ -> asFun "min" es
                  Max  _ -> asFun "max" es

                  Sum  _ -> case F.toList es of
                    [e1] -> prettyPrec p e1
                    e1:es' -> parensIf (p > 6) $ sep $
                              prettyPrec 6 e1 :
                              map ppNaryOpSum es'

                  Prod _ -> case F.toList es of
                    [e1] -> prettyPrec p e1
                    e1:e2:es' -> parensIf (p > 7) $ sep $
                                 d1' :
                                 ppNaryOpProd second e2 :
                                 map (ppNaryOpProd False) es'
                      where d1 = prettyPrec 7 e1
                            (d1', second) =
                              caseVarSyn e1 (const (d1,False)) (\t -> case t of
                                -- Use parens to distinguish division into 1
                                -- from recip
                                Literal_ (LNat 1) -> (parens d1, False)
                                Literal_ (LNat _) -> (d1, True)
                                _                 -> (d1, False))

          where identityElement :: NaryOp a -> Doc
                identityElement And      = text "true"
                identityElement Or       = text "false"
                identityElement Xor      = text "false"
                identityElement Iff      = text "true"
                identityElement (Min  _) = error "min cannot be used with no arguments"
                identityElement (Max  _) = error "max cannot be used with no arguments"
                identityElement (Sum  _) = text "0"
                identityElement (Prod _) = text "1"

                asOp :: (ABT Term abt)
                     => Int -> String -> Seq.Seq (abt '[] a) -> Doc
                asOp p0 s = parensIf (p > p0)
                          . sepByR s
                          . map (prettyPrec (p0 + 1))
                          . F.toList

                asFun :: (ABT Term abt)
                      => String -> Seq.Seq (abt '[] a) -> Doc
                asFun   s = ($ p)
                          . F.foldr1 (\a b p' -> ppFun p' s [a, b])
                          . fmap (flip prettyPrec)

        Literal_ v    -> prettyPrec_ p v
        Empty_   typ  -> parensIf (p > 5) (text "[]." <+> prettyType 0 typ)
        Array_ e1 e2  -> parensIf (p > 0) $
            let (var, _, body) = ppBinder1 e2 in
            sep [ sep [ text "array" <+> var
                      , text "of" <+> pretty e1 <> colon ]
                , body ]

        ArrayLiteral_ es -> ppList $ map pretty es

        Datum_ d      -> prettyPrec_ p (fmap11 LC_ d)
        Case_  e1 [Branch (PDatum h2 _) e2, Branch (PDatum h3 _) e3]
            | "true"  <- Text.unpack h2
            , "false" <- Text.unpack h3
            , ([], body2) <- ppBinder e2
            , ([], body3) <- ppBinder e3
            -> parensIf (p > 0) $
               sep [ sep [ text "if" <+> pretty e1 <> colon, nest 2 body2 ]
                   , sep [ text "else" <> colon, nest 2 body3 ] ]
        Case_  e1 bs  -> parensIf (p > 0) $
            sep [ text "match" <+> pretty e1 <> colon
                , vcat (map (prettyPrec_ 0) bs) ]
        Superpose_ pes -> case L.toList pes of
                            [wm] -> ppWeight p wm
                            wms  -> parensIf (p > 1)
                                  . sepByR "<|>"
                                  $ map (ppWeight 2) wms
          where ppWeight p (w,m)
                    | Syn (Literal_ (LProb 1)) <- viewABT w
                    = prettyPrec p m
                    | otherwise
                    = ppApply2 p "weight" w m

        Reject_ typ -> parensIf (p > 5) (text "reject." <+> prettyType 0 typ)

        Bucket lo hi red -> ppFun p "rbucket"
                            [ flip prettyPrec lo, flip prettyPrec hi
                            , flip prettyPrec_ red ]

instance ABT Term abt => Pretty (Reducer abt xs) where
  prettyPrec_ = flip ppr where
    ppRbinder :: abt xs1 a -> Int -> Doc
    ppRbinder f p =
      let (vs,b) = ppBinder f
      in parensIf (p > 0) $ sep [ sepComma vs <> colon, b ]

    ppr :: Reducer abt xs1 a -> Int -> Doc
    ppr red p =
      case red of
        Red_Fanout l r  -> ppFun p "rfanout"
                             [ ppr l
                             , ppr r ]
        Red_Index s k r -> ppFun p "rindex"
                             [ ppRbinder s
                             , ppRbinder k
                             , ppr r ]
        Red_Split b l r -> ppFun p "rsplit"
                             [ ppRbinder b
                             , ppr l
                             , ppr r ]
        Red_Nop         -> text "rnop"
        Red_Add _ k     -> ppFun p "radd" [ ppRbinder k ]

ppNaryOpSum
    :: forall abt a . (ABT Term abt) => abt '[] a -> Doc
ppNaryOpSum e =
    caseVarSyn e (const d) $ \t ->
        case t of
        PrimOp_ (Negate _) :$ e1 :* End -> text "-" <+> prettyPrec 7 e1
        _ -> d
  where d = text "+" <+> prettyPrec 7 e

ppNaryOpProd
    :: forall abt a . (ABT Term abt) => Bool -> abt '[] a -> Doc
ppNaryOpProd second e =
    caseVarSyn e (const d) $ \t ->
        case t of
        PrimOp_ (Recip _) :$ e1 :* End ->
            if not second then d' else
            caseVarSyn e1 (const d') $ \t' ->
                case t' of
                -- Use parens to distinguish division of nats
                -- from prob literal
                Literal_ (LNat _) -> text "/" <+> parens (pretty e1)
                _ -> d'
          where d' = text "/" <+> prettyPrec 8 e1
        _ -> d
  where d = text "*" <+> prettyPrec 8 e

-- | Pretty-print @(:$)@ nodes in the AST.
ppSCon :: (ABT Term abt) => Int -> SCon args a -> SArgs abt args -> Doc
ppSCon p Lam_ = \(e1 :* End) ->
    let (var, typ, body) = ppBinder1 e1 in
    parensIf (p > 0) $
    sep [ text "fn" <+> var <+> typ <> colon
        , body ]

--ppSCon p App_ = \(e1 :* e2 :* End) -> ppArg e1 ++ parens True (ppArg e2)
ppSCon p App_ = \(e1 :* e2 :* End) -> prettyApps p e1 e2

ppSCon p Let_ = \(e1 :* e2 :* End) ->
    -- TODO: generate 'def' if possible
    let (var, _, body) = ppBinder1 e2 in
    parensIf (p > 0) $
    var <+> equals <+> pretty e1 $$ body
{-
ppSCon p (Ann_ typ) = \(e1 :* End) ->
    parensIf (p > 5) (prettyPrec 6 e1 <> text "." <+> prettyType 0 typ)
-}

ppSCon p (PrimOp_     o) = \es          -> ppPrimOp     p o es
ppSCon p (ArrayOp_    o) = \es          -> ppArrayOp    p o es
ppSCon p (CoerceTo_   c) = \(e1 :* End) -> ppCoerceTo   p c e1
ppSCon p (UnsafeFrom_ c) = \(e1 :* End) -> ppUnsafeFrom p c e1
ppSCon p (MeasureOp_  o) = \es          -> ppMeasureOp  p o es
ppSCon p Dirac = \(e1 :* End) ->
    parensIf (p > 0) $
    text "return" <+> pretty e1
ppSCon p MBind = \(e1 :* e2 :* End) ->
    let (var, _, body) = ppBinder1 e2 in
    parensIf (p > 0) $
    var <+> text "<~" <+> pretty e1 $$ body

ppSCon p Plate = \(e1 :* e2 :* End) ->
    let (var, _, body) = ppBinder1 e2 in
    parensIf (p > 0) $
    sep [ sep [ text "plate" <+> var
              , text "of" <+> pretty e1 <> colon ]
        , body ]

ppSCon p Chain = \(e1 :* e2 :* e3 :* End) ->
    let (var, _, body) = ppBinder1 e3 in
    parensIf (p > 0) $
    sep [ sep [ text "chain" <+> var
              , text "from" <+> pretty e2
              , text "of" <+> pretty e1 <> colon ]
        , body ]

ppSCon p Integrate = \(e1 :* e2 :* e3 :* End) ->
    let (var, _, body) = ppBinder1 e3 in
    parensIf (p > 0) $
    sep [ sep [ text "integrate" <+> var
              , text "from" <+> pretty e1
              , text "to" <+> pretty e2 <> colon ]
        , body ]

ppSCon p (Summate _ _) = \(e1 :* e2 :* e3 :* End) ->
    let (var, _, body) = ppBinder1 e3 in
    parensIf (p > 0) $
    sep [ sep [ text "summate" <+> var
              , text "from" <+> pretty e1
              , text "to" <+> pretty e2 <> colon ]
        , body ]

ppSCon p (Product _ _) = \(e1 :* e2 :* e3 :* End) ->
    let (var, _, body) = ppBinder1 e3 in
    parensIf (p > 0) $
    sep [ sep [ text "product" <+> var
              , text "from" <+> pretty e1
              , text "to" <+> pretty e2 <> colon ]
        , body ]

ppSCon p (Transform_ t) = ppTransform p t

ppTransform :: (ABT Term abt)
            => Int -> Transform args a
            -> SArgs abt args -> Doc
ppTransform p t es =
  case t of
    Expect ->
      case es of
        e1 :* e2 :* End ->
          let (var, _, body) = ppBinder1 e2 in
          parensIf (p > 0) $
          sep [ text "expect" <+> var <+> pretty e1 <> colon
              , body ]
    _ -> ppApply p (transformName t) es

ppCoerceTo :: ABT Term abt => Int -> Coercion a b -> abt '[] a -> Doc
ppCoerceTo p c = ppApply1 p f
    -- BUG: this may not work quite right when the coercion isn't one of the special named ones...
    where
    f = case c of
          Signed HRing_Real             `CCons` CNil -> "prob2real"
          Signed HRing_Int              `CCons` CNil -> "nat2int"
          Continuous HContinuous_Real   `CCons` CNil -> "int2real"
          Continuous HContinuous_Prob   `CCons` CNil -> "nat2prob"
          Continuous HContinuous_Prob   `CCons`
            Signed HRing_Real           `CCons` CNil -> "nat2real"
          Signed HRing_Int              `CCons`
            Continuous HContinuous_Real `CCons` CNil -> "nat2real"
          _ -> "coerceTo_ (" ++ show c ++ ")"


ppUnsafeFrom :: ABT Term abt => Int -> Coercion a b -> abt '[] b -> Doc
ppUnsafeFrom p c = ppApply1 p f
    -- BUG: this may not work quite right when the coercion isn't one of the special named ones...
    where
    f = case c of
          Signed HRing_Real `CCons` CNil -> "real2prob"
          Signed HRing_Int  `CCons` CNil -> "int2nat"
          _ -> "unsafeFrom_ (" ++ show c ++ ")"


-- | Pretty-print a type.
prettyType :: Int -> Sing (a :: Hakaru) -> Doc
prettyType _ SNat         = text "nat"
prettyType _ SInt         = text "int"
prettyType _ SProb        = text "prob"
prettyType _ SReal        = text "real"
prettyType p (SFun   a b) = parensIf (p > 0)
                          $ sep [ prettyType 1 a <+> text "->"
                                , prettyType 0 b ]
prettyType p (SMeasure a) = ppFun p "measure" [flip prettyType a]
prettyType p (SArray   a) = ppFun p "array" [flip prettyType a]
prettyType p (SData (STyCon sym `STyApp` a `STyApp` b) _)
    | Just Refl <- jmEq1 sym sSymbol_Pair
    = ppFun p "pair" [flip prettyType a, flip prettyType b]
    | Just Refl <- jmEq1 sym sSymbol_Either
    = ppFun p "either" [flip prettyType a, flip prettyType b]
prettyType p (SData (STyCon sym `STyApp` a) _)
    | Just Refl <- jmEq1 sym sSymbol_Maybe
    = ppFun p "maybe" [flip prettyType a]
prettyType p (SData (STyCon sym) _)
    | Just Refl <- jmEq1 sym sSymbol_Bool
    = text "bool"
    | Just Refl <- jmEq1 sym sSymbol_Unit
    = text "unit"
prettyType _ typ
    = parens (text (show typ))


-- | Pretty-print a 'PrimOp' @(:$)@ node in the AST.
ppPrimOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => Int -> PrimOp typs a -> SArgs abt args -> Doc
ppPrimOp p Not          (e1 :* End)
  | Syn (PrimOp_ Less{}  :$ e2 :* e3 :* End) <- viewABT e1
  = ppBinop "<=" 4 NonAssoc p e3 e2
  | Syn (PrimOp_ Equal{} :$ e2 :* e3 :* End) <- viewABT e1
  = ppBinop "/=" 4 NonAssoc p e2 e3
  | otherwise
  = ppApply1 p "not" e1
ppPrimOp p Impl         (e1 :* e2 :* End) = ppApply2 p "impl" e1 e2
ppPrimOp p Diff         (e1 :* e2 :* End) = ppApply2 p "diff" e1 e2
ppPrimOp p Nand         (e1 :* e2 :* End) = ppApply2 p "nand" e1 e2
ppPrimOp p Nor          (e1 :* e2 :* End) = ppApply2 p "nor" e1 e2
ppPrimOp _ Pi           End               = text "pi"
ppPrimOp p Sin          (e1 :* End)       = ppApply1 p "sin"   e1
ppPrimOp p Cos          (e1 :* End)       = ppApply1 p "cos"   e1
ppPrimOp p Tan          (e1 :* End)       = ppApply1 p "tan"   e1
ppPrimOp p Asin         (e1 :* End)       = ppApply1 p "asin"  e1
ppPrimOp p Acos         (e1 :* End)       = ppApply1 p "acos"  e1
ppPrimOp p Atan         (e1 :* End)       = ppApply1 p "atan"  e1
ppPrimOp p Sinh         (e1 :* End)       = ppApply1 p "sinh"  e1
ppPrimOp p Cosh         (e1 :* End)       = ppApply1 p "cosh"  e1
ppPrimOp p Tanh         (e1 :* End)       = ppApply1 p "tanh"  e1
ppPrimOp p Asinh        (e1 :* End)       = ppApply1 p "asinh" e1
ppPrimOp p Acosh        (e1 :* End)       = ppApply1 p "acosh" e1
ppPrimOp p Atanh        (e1 :* End)       = ppApply1 p "atanh" e1
ppPrimOp p RealPow      (e1 :* e2 :* End) = ppBinop "**" 8 RightAssoc p e1 e2
ppPrimOp p Choose       (e1 :* e2 :* End) = ppApply2 p "choose" e1 e2
ppPrimOp p Exp          (e1 :* End)       = ppApply1 p "exp"   e1
ppPrimOp p Log          (e1 :* End)       = ppApply1 p "log"   e1
ppPrimOp _ (Infinity _) End               = text "∞"
ppPrimOp p GammaFunc    (e1 :* End)       = ppApply1 p "gammaFunc" e1
ppPrimOp p BetaFunc     (e1 :* e2 :* End) = ppApply2 p "betaFunc" e1 e2
ppPrimOp p (Equal   _)  (e1 :* e2 :* End) = ppBinop "==" 4 NonAssoc   p e1 e2
ppPrimOp p (Less    _)  (e1 :* e2 :* End) = ppBinop "<"  4 NonAssoc   p e1 e2
ppPrimOp p (NatPow  _)  (e1 :* e2 :* End) = ppBinop "^"  8 RightAssoc p e1 e2
ppPrimOp p (Negate  _)  (e1 :* End)       = ppNegate p e1
ppPrimOp p (Abs     _)  (e1 :* End)       = ppApply1  p "abs"     e1
ppPrimOp p (Signum  _)  (e1 :* End)       = ppApply1  p "signum"  e1
ppPrimOp p (Recip   _)  (e1 :* End)       = ppRecip p e1
ppPrimOp p (NatRoot _)  (e1 :* e2 :* End) = ppNatRoot p e1 e2
ppPrimOp p (Erf _)      (e1 :* End)       = ppApply1  p "erf"     e1
ppPrimOp p Floor        (e1 :* End)       = ppApply1 p "floor"   e1

ppNegate :: (ABT Term abt) => Int -> abt '[] a -> Doc
ppNegate p e = parensIf (p > 6) $
    caseVarSyn e (const d) $ \t ->
        case t of
        -- Use parens to distinguish between negation of nats/probs
        -- from int/real literal
        Literal_ (LNat  _) -> d'
        Literal_ (LProb _) -> d'
        _                  -> d
    where d  = text "-" <> prettyPrec 7 e
          d' = text "-" <> parens (pretty e)

ppRecip :: (ABT Term abt) => Int -> abt '[] a -> Doc
ppRecip p e = parensIf (p > 7) $
    caseVarSyn e (const d) $ \t ->
        case t of
        -- Use parens to distinguish between reciprocal of nat
        -- from prob literal
        Literal_ (LNat _) -> d'
        _                 -> d
    where d  = text "1/" <+> prettyPrec 8 e
          d' = text "1/" <+> parens (pretty e)

ppNatRoot
    :: (ABT Term abt)
    => Int
    -> abt '[] a
    -> abt '[] 'HNat
    -> Doc
ppNatRoot p e1 e2 =
    caseVarSyn e2 (const d) $ \t ->
        case t of
          Literal_ (LNat 2) -> ppApply1 p "sqrt" e1
          _                 -> d
    where d = ppApply2 p "natroot" e1 e2


-- | Pretty-print a 'ArrayOp' @(:$)@ node in the AST.
ppArrayOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => Int -> ArrayOp typs a -> SArgs abt args -> Doc
ppArrayOp p (Index   _) = \(e1 :* e2 :* End) -> parensIf (p > 10)
    $ cat [ prettyPrec 10 e1, nest 2 (brackets (pretty e2)) ]

ppArrayOp p (Size    _) = \(e1 :* End)       -> ppApply1 p "size" e1
ppArrayOp p (Reduce  _) = \(e1 :* e2 :* e3 :* End) ->
    ppFun p "reduce"
        [ flip prettyPrec e1
        , flip prettyPrec e2
        , flip prettyPrec e3 ]


-- | Pretty-print a 'MeasureOp' @(:$)@ node in the AST.
ppMeasureOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => Int -> MeasureOp typs a -> SArgs abt args -> Doc
ppMeasureOp p Lebesgue    = \(e1 :* e2 :* End) -> ppApply2 p "lebesgue" e1 e2
ppMeasureOp _ Counting    = \End           -> text "counting"
ppMeasureOp p Categorical = \(e1 :* End)   -> ppApply1 p "categorical" e1
ppMeasureOp p Uniform = \(e1 :* e2 :* End) -> ppApply2 p "uniform"     e1 e2
ppMeasureOp p Normal  = \(e1 :* e2 :* End) -> ppApply2 p "normal"      e1 e2
ppMeasureOp p Poisson = \(e1 :* End)       -> ppApply1 p "poisson"     e1
ppMeasureOp p Gamma   = \(e1 :* e2 :* End) -> ppApply2 p "gamma"       e1 e2
ppMeasureOp p Beta    = \(e1 :* e2 :* End) -> ppApply2 p "beta"        e1 e2

instance Pretty Literal where
    prettyPrec_ _ (LNat  n) = integer (fromNatural n)
    prettyPrec_ p (LInt  i) = parensIf (p > 6) $
        if i < 0 then text "-" <> integer (-i)
                 else text "+" <> integer   i
    prettyPrec_ p (LProb l) = parensIf (p > 7) $
        cat [ integer n, text "/" <> integer d ]
        where r = fromNonNegativeRational l
              n = numerator   r
              d = denominator r
    prettyPrec_ p (LReal r) = parensIf (p > 6) $
        if n < 0 then text "-" <> cat [ integer (-n), text "/" <> integer d ]
                 else text "+" <> cat [ integer   n , text "/" <> integer d ]
        where n = numerator   r
              d = denominator r

instance Pretty Value where
    prettyPrec_ _ (VNat  n)    = integer (fromNatural n)
    prettyPrec_ p (VInt  i)    = parensIf (p > 6) $
        if i < 0 then integer i else text "+" <> integer i
    prettyPrec_ _ (VProb l)    = double (LF.fromLogFloat l)
    prettyPrec_ p (VReal r)    = parensIf (p > 6) $
        if r < 0 then double r else text "+" <> double r
    prettyPrec_ p (VDatum d)   = prettyPrec_ p d
    prettyPrec_ _ (VLam _)     = text "<function>"
    prettyPrec_ _ (VMeasure _) = text "<measure>"
    prettyPrec_ _ (VArray a)   = ppList . V.toList $ V.map (prettyPrec_ 0) a

prettyValue :: Value a -> Doc
prettyValue = prettyPrec_ 0

instance Pretty f => Pretty (Datum f) where
    prettyPrec_ p (Datum hint _typ d)
        | Text.null hint =
            ppFun p "datum_"
                [error "TODO: prettyPrec_@Datum"]
        | otherwise =
            case Text.unpack hint of
            -- Special cases for certain datums
            "pair"  -> ppTuple p (foldMap11 (\e -> [flip prettyPrec_ e]) d) 
            "true"  -> text "true"
            "false" -> text "false"
            "unit"  -> text "()"
            -- General case
            f       -> parensIf (p > 5) $
                       ppFun 6 f (foldMap11 (\e -> [flip prettyPrec_ e]) d)
                       <> text "." <+> prettyType 0 _typ


-- HACK: need to pull this out in order to get polymorphic recursion over @xs@
ppPattern :: [Doc] -> Pattern xs a -> (Int -> Doc, [Doc])
ppPattern vars   PWild = (const (text "_"), vars)
ppPattern (v:vs) PVar  = (const v         , vs)
ppPattern vars   (PDatum hint d0)
    | Text.null hint = error "TODO: prettyPrec_@Pattern"
    | otherwise      =
        case Text.unpack hint of
        -- Special cases for certain pDatums
        "true"  -> (const (text "true" ), vars)
        "false" -> (const (text "false"), vars)
        "pair"  -> ppFunWithVars ppTuple
        -- General case
        f       -> ppFunWithVars (flip ppFun f)
    where
    ppFunWithVars ppHint = (flip ppHint g, vars')
       where (g, vars') = goCode d0 vars

    goCode :: PDatumCode xss vars a -> [Doc] -> ([Int -> Doc], [Doc])
    goCode (PInr d) = goCode   d
    goCode (PInl d) = goStruct d

    goStruct :: PDatumStruct xs vars a -> [Doc] -> ([Int -> Doc], [Doc])
    goStruct PDone       vars  = ([], vars)
    goStruct (PEt d1 d2) vars = (gF ++ gS, vars'')
       where (gF, vars')  = goFun d1 vars
             (gS, vars'') = goStruct d2 vars' 

    goFun :: PDatumFun x vars a -> [Doc] -> ([Int -> Doc], [Doc])
    goFun (PKonst d) vars = ([g], vars')
       where (g, vars') = ppPattern vars d
    goFun (PIdent d) vars = ([g], vars')
       where (g, vars') = ppPattern vars d


instance (ABT Term abt) => Pretty (Branch a abt) where
    prettyPrec_ p (Branch pat e) =
        let (vars, body) = ppBinder e
            (pp, []) = ppPattern vars pat
        in sep [ pp 0 <> colon, nest 2 body ]

----------------------------------------------------------------
prettyApps :: (ABT Term abt) => Int -> abt '[] (a ':-> b) -> abt '[] a -> Doc
prettyApps = \ p e1 e2 ->
{- TODO: confirm not using reduceLams
    case reduceLams e1 e2 of
    Just e2' -> ppArg e2'
    Nothing  ->
-}
      uncurry (ppApp p) (collectApps e1 [flip prettyPrec e2])
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

    -- collectApps makes sure f(x,y) is not printed f(x)(y)
    collectApps
        :: (ABT Term abt)
        => abt '[] (a ':-> b) -> [Int -> Doc] -> (Int -> Doc, [Int -> Doc])
    collectApps e es = 
        caseVarSyn e (const ret) $ \t ->
            case t of
            App_ :$ e1 :* e2 :* End -> collectApps e1 (flip prettyPrec e2 : es)
            _                       -> ret
        where ret = (flip prettyPrec e, es)



ppList :: [Doc] -> Doc
ppList = brackets . sepComma

ppTuple :: Int -> [Int -> Doc] -> Doc
ppTuple _ = parens . sepComma . map ($ 0)

ppApp :: Int -> (Int -> Doc) -> [Int -> Doc] -> Doc
ppApp p f ds = parensIf (p > 10)
             $ cat [ f 10, nest 2 (ppTuple 11 ds) ]

ppFun :: Int -> String -> [Int -> Doc] -> Doc
ppFun p = ppApp p . const . text

ppApply1 :: (ABT Term abt) => Int -> String -> abt '[] a -> Doc
ppApply1 p f e1 = ppFun p f [flip prettyPrec e1]

ppApply2 :: (ABT Term abt) => Int -> String -> abt '[] a -> abt '[] b -> Doc
ppApply2 p f e1 e2 = ppFun p f [flip prettyPrec e1, flip prettyPrec e2]

ppApply :: ABT Term abt => Int -> String
        -> SArgs abt xs -> Doc
ppApply p f es =
  ppFun p f $ foldMap21 (pure . const . ppBinderAsFun) es

ppBinop
    :: (ABT Term abt)
    => String -> Int -> Associativity
    -> Int -> abt '[] a -> abt '[] b -> Doc
ppBinop op p0 assoc =
    let (p1,p2,f1,f2) =
            case assoc of
            NonAssoc   -> (1 + p0, 1 + p0, id, (text op <+>))
            LeftAssoc  -> (    p0, 1 + p0, id, (text op <+>))
            RightAssoc -> (1 + p0,     p0, (<+> text op), id)
    in \p e1 e2 ->
        parensIf (p > p0) $ sep [ f1 (prettyPrec p1 e1)
                                , f2 (prettyPrec p2 e2) ]

----------------------------------------------------------------
----------------------------------------------------------- fin.
