{-# LANGUAGE GADTs
           , KindSignatures
           , DataKinds
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.18
-- |
-- Module      :  Language.Hakaru.MeSoPretty
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- An in-progress replacement for "Language.Hakaru.PrettyPrint". When this is complete, we will move it to that module name.
----------------------------------------------------------------
module Language.Hakaru.MeSoPretty (pretty, prettyPrec) where

import           Text.PrettyPrint (Doc, (<>), (<+>))
import qualified Text.PrettyPrint as PP
import qualified Data.Foldable    as F
import qualified Data.Text        as Text
import qualified Data.Sequence    as Seq -- Because older versions of "Data.Foldable" do not export 'null' apparently...

import Language.Hakaru.Syntax.Nat      (fromNat)
import Language.Hakaru.Syntax.IClasses (fmap11, foldMap11)
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Coercion
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT
----------------------------------------------------------------
-- TODO: can we avoid using Text.unpack?


-- | Pretty-print a term.
pretty :: (ABT abt) => abt '[] a -> Doc
pretty = prettyPrec 0


-- | Pretty-print a term at a given precendence level.
prettyPrec :: (ABT abt) => Int -> abt '[] a -> Doc
prettyPrec p = prettyPrec_ p . LC_


-- | Pretty-print a variable.
ppVariable :: Variable a -> Doc
ppVariable x = hint <> (PP.int . fromNat . varID) x
    where
    hint
        | Text.null (varHint x) = PP.char '_'
        | otherwise             = (PP.text . Text.unpack . varHint) x


-- | Pretty-print Hakaru binders as a Haskell lambda, as per our HOAS API.
ppBinder :: (ABT abt) => abt xs a -> Doc
ppBinder e =
    case go [] (viewABT e) of
    ([],  body) -> PP.parens body
    (vars,body) ->
        PP.parens $ PP.sep
            [ PP.char '\\'
                <+> PP.sep vars
                <+> PP.text "->"
            , PP.nest 4 body -- TODO: is there a better nesting than constant 4?
            ]
    where
    go :: (ABT abt) => [Doc] -> View abt xs a -> ([Doc],Doc)
    go xs (Bind x e) = go (ppVariable x : xs) e
    go xs (Var  x)   = (reverse xs, ppVariable x)
    go xs (Syn  t)   = (reverse xs, pretty (syn t))
{-
-- Simpler version in case we only need to handle singleton binders.
ppBinder :: (ABT abt) => abt '[ x ] a -> Doc
ppBinder e =
    caseBind e $ \x e' ->
        PP.parens $ PP.sep
            [ PP.char '\\'
                <+> ppVariable x
                <+> PP.text "->"
            , PP.nest 4 (pretty e')
            ]
-}


class Pretty (f :: Hakaru -> *) where
    -- | A polymorphic variant if 'prettyPrec', for internal use.
    prettyPrec_ :: Int -> f a -> Doc


-- HACK: so we can safely give a 'Pretty' instance
-- TODO: unify this with the same hack used in AST.hs for 'Show'
newtype LC_ (abt :: [Hakaru] -> Hakaru -> *) (a :: Hakaru) =
    LC_ { unLC_ :: abt '[] a }


instance (ABT abt) => Pretty (LC_ abt) where
  prettyPrec_ p (LC_ e) =
    caseVarSyn e ppVariable $ \t -> 
        case t of
        o :$ es      -> ppSCon p o es
        NaryOp_ o es ->
            -- TODO: make sure these ops actually have those precedences in the Prelude!!
            let prettyNaryOp :: NaryOp a -> (String, Int, Maybe String)
                prettyNaryOp And  = ("&&", 3, Just "true")
                prettyNaryOp Or   = ("||", 2, Just "false")
                prettyNaryOp Xor  = ("`xor`", 0, Just "false")
                -- BUG: even though 'Iff' is associative (in Boolean algebras), we should not support n-ary uses in our *surface* syntax. Because it's too easy for folks to confuse "a <=> b <=> c" with "(a <=> b) /\ (b <=> c)".
                prettyNaryOp Iff      = ("`iff`", 0, Just "true")
                prettyNaryOp (Min  _) = ("`min`", 5, Nothing)
                prettyNaryOp (Max  _) = ("`max`", 5, Nothing)
                -- HACK: we don't actually have polymorphic literals; thus we should only print "0"/"1" wrapped with the appropriate value wrapper. We can use the Prelude's 'zero' and 'one', provided we actually give them legit implementations
                prettyNaryOp (Sum  _) = ("+", 6, Just "0")
                prettyNaryOp (Prod _) = ("*", 7, Just "1")
            in
            let (opName,opPrec,maybeIdentity) = prettyNaryOp o in
            if Seq.null es
            then
                case maybeIdentity of
                Just identity -> PP.text identity
                Nothing ->
                    ppFun p "syn"
                        [ ppFun 11 "NaryOp_"
                            [ PP.text (showsPrec 11 o "")
                            , PP.text "(Seq.fromList [])"
                            ]
                        ]
            else
                tryParens (p > opPrec)
                . PP.sep
                . PP.punctuate (PP.space <> PP.text opName)
                . map (prettyPrec opPrec)
                $ F.toList es

        Value_ v      -> prettyPrec_ p v
        Empty_        -> PP.text "empty"
        Array_ e1 e2  -> ppFun p "array" [ppArg e1, ppBinder e2]
        Datum_ d      -> prettyPrec_ p (fmap11 LC_ d)
        Case_  e1 bs  ->
            -- TODO: should we also add hints to the 'Case_' constructor to know whether it came from 'if_', 'unpair', etc?
            ppFun p "syn"
                [ ppFun 11 "Case_"
                    [ ppArg e1
                    , ppList (map (prettyPrec_ 0) bs)
                    ]
                ]
        Superpose_ pes ->
            ppFun p "superpose"
                [ ppList
                . map (\(e1,e2) -> ppTuple [pretty e1, pretty e2])
                $ pes
                ]
        Lub_ es -> ppFun p "syn" [ppFun 11 "Lub_" [ppList (map pretty es)]]


-- | Pretty-print @(:$)@ nodes in the AST.
ppSCon :: (ABT abt) => Int -> SCon args a -> SArgs abt args -> Doc
ppSCon p Lam_ (e1 :* End)       = ppFun p "lam"  [ppBinder e1]
    -- TODO: use the 'adjustHead' trick from the old PrettyPrint.hs
ppSCon p App_ (e1 :* e2 :* End) = ppFun p "app"  [ppArg e1, ppArg e2]
    -- TODO: use infix instead! must enable @infixl 9 `app`@ in the Prelude
ppSCon p Let_ (e1 :* e2 :* End) = ppFun p "let_" [ppArg e1, ppBinder e2]
    -- TODO: use the 'adjustHead' trick from the old PrettyPrint.hs
ppSCon p Fix_       (e1 :* End) = ppFun p "fix"  [ppBinder e1]
ppSCon p (Ann_ typ) (e1 :* End) =
    ppFun p "ann_"
        [ PP.text (showsPrec 11 typ "") -- TODO: make this prettier. Add hints to the singletons?
        , ppArg e1
        ]
ppSCon p (PrimOp_     o) es = ppPrimOp p o es
ppSCon p (CoerceTo_   c) (e1 :* End) =
    ppFun p "coerceTo_"
        [ PP.text (showsPrec 11 c "") -- TODO: make this prettier. Add hints to the coercions?
        , ppArg e1
        ]
ppSCon p (UnsafeFrom_ c) (e1 :* End) =
    ppFun p "unsafeFrom_"
        [ PP.text (showsPrec 11 c "") -- TODO: make this prettier. Add hints to the coercions?
        , ppArg e1
        ]
ppSCon p (MeasureOp_  o) es = ppMeasureOp p o es
ppSCon p MBind (e1 :* e2 :* End) =
    -- TODO: use the 'adjustHead' trick from the old PrettyPrint.hs
    -- @ppBinop ">>=" 1 LeftAssoc p e1 e2@ doesn't work because the binder...
    tryParens (p > 1) $ PP.sep
        [ prettyPrec 1 e1
        , PP.text ">>="
            <+> ppBinder e2 -- TODO: add a precedence arg to ppBinder so we can capture the left-associativity appropriately; only meaningful if we allow non-parenthesization of HOAS-lambdas...
        ]
ppSCon p Expect (e1 :* e2 :* End) =
    ppFun p "syn"
        [ ppFun 11 "Expect"
            [ ppArg e1
            , ppBinder e2 -- BUG: we can't actually use the HOAS API here, since we aren't using a Prelude-defined @expect@ but rather are using 'syn'...
            ]
        ]
-- HACK: GHC can't figure out that there are no other type-safe cases
ppSCon _ _ _ = error "ppSCon: the impossible happened"


-- | Pretty-print a 'PrimOp' @(:$)@ node in the AST.
ppPrimOp
    :: (ABT abt, typs ~ UnLCs args, args ~ LCs typs)
    => Int -> PrimOp typs a -> SArgs abt args -> Doc
ppPrimOp p Not  (e1 :* End)       = ppFun p "not" [ppArg e1]
ppPrimOp p Impl (e1 :* e2 :* End) =
    -- TODO: make prettier
    ppFun p "syn" [ppFun 11 "Impl" [ppArg e1, ppArg e2]]
ppPrimOp p Diff (e1 :* e2 :* End) =
    -- TODO: make prettier
    ppFun p "syn" [ppFun 11 "Diff" [ppArg e1, ppArg e2]]
ppPrimOp p Nand (e1 :* e2 :* End) =
    -- TODO: make infix...
    ppFun p "nand" [ppArg e1, ppArg e2]
ppPrimOp p Nor  (e1 :* e2 :* End) =
    -- TODO: make infix...
    ppFun p "nor" [ppArg e1, ppArg e2]
ppPrimOp _ Pi      End               = PP.text "pi"
ppPrimOp p Sin     (e1 :* End)       = ppFun p "sin"   [ppArg e1]
ppPrimOp p Cos     (e1 :* End)       = ppFun p "cos"   [ppArg e1]
ppPrimOp p Tan     (e1 :* End)       = ppFun p "tan"   [ppArg e1]
ppPrimOp p Asin    (e1 :* End)       = ppFun p "asin"  [ppArg e1]
ppPrimOp p Acos    (e1 :* End)       = ppFun p "acos"  [ppArg e1]
ppPrimOp p Atan    (e1 :* End)       = ppFun p "atan"  [ppArg e1]
ppPrimOp p Sinh    (e1 :* End)       = ppFun p "sinh"  [ppArg e1]
ppPrimOp p Cosh    (e1 :* End)       = ppFun p "cosh"  [ppArg e1]
ppPrimOp p Tanh    (e1 :* End)       = ppFun p "tanh"  [ppArg e1]
ppPrimOp p Asinh   (e1 :* End)       = ppFun p "asinh" [ppArg e1]
ppPrimOp p Acosh   (e1 :* End)       = ppFun p "acosh" [ppArg e1]
ppPrimOp p Atanh   (e1 :* End)       = ppFun p "atanh" [ppArg e1]
ppPrimOp p RealPow (e1 :* e2 :* End) = ppBinop "**" 8 RightAssoc p e1 e2
ppPrimOp p Exp     (e1 :* End)       = ppFun p "exp"   [ppArg e1]
ppPrimOp p Log     (e1 :* End)       = ppFun p "log"   [ppArg e1]
ppPrimOp _ Infinity         End      = PP.text "infinity"
ppPrimOp _ NegativeInfinity End      = PP.text "negativeInfinity"
ppPrimOp p GammaFunc (e1 :* End)     = ppFun p "gammaFunc" [ppArg e1]
ppPrimOp p BetaFunc  (e1 :* e2 :* End) =
    ppFun p "betaFunc" [ppArg e1, ppArg e2]
ppPrimOp p Integrate (e1 :* e2 :* e3 :* End) =
    ppFun p "integrate"
        [ ppArg e1
        , ppArg e2
        , ppArg e3 -- TODO: make into a binding form!
        ]
ppPrimOp p Summate (e1 :* e2 :* e3 :* End) =
    ppFun p "summate"
        [ ppArg e1
        , ppArg e2
        , ppArg e3 -- TODO: make into a binding form!
        ]
ppPrimOp p (Index   _) (e1 :* e2 :* End) = ppBinop "!" 9 LeftAssoc p e1 e2
ppPrimOp p (Size    _) (e1 :* End)       = ppFun p "size" [ppArg e1]
ppPrimOp p (Reduce  _) (e1 :* e2 :* e3 :* End) =
    ppFun p "reduce"
        [ ppArg e1 -- N.B., @e1@ uses lambdas rather than being a binding form!
        , ppArg e2
        , ppArg e3
        ]
ppPrimOp p (Equal   _) (e1 :* e2 :* End) = ppBinop "==" 4 NonAssoc   p e1 e2
ppPrimOp p (Less    _) (e1 :* e2 :* End) = ppBinop "<"  4 NonAssoc   p e1 e2
ppPrimOp p (NatPow  _) (e1 :* e2 :* End) = ppBinop "^"  8 RightAssoc p e1 e2
ppPrimOp p (Negate  _) (e1 :* End)       = ppFun p "negate" [ppArg e1]
ppPrimOp p (Abs     _) (e1 :* End)       = ppFun p "abs_"   [ppArg e1]
ppPrimOp p (Signum  _) (e1 :* End)       = ppFun p "signum" [ppArg e1]
ppPrimOp p (Recip   _) (e1 :* End)       = ppFun p "recip"  [ppArg e1]
ppPrimOp p (NatRoot _) (e1 :* e2 :* End) =
    -- TODO: make infix...
    -- N.B., argument order is swapped!
    ppFun p "thRootOf" [ppArg e2, ppArg e1]
ppPrimOp p (Erf _) (e1 :* End) = ppFun p "erf" [ppArg e1]
-- HACK: GHC can't figure out that there are no other type-safe cases
ppPrimOp _ _ _ = error "ppPrimOp: the impossible happened"


-- | Pretty-print a 'MeasureOp' @(:$)@ node in the AST.
ppMeasureOp
    :: (ABT abt, typs ~ UnLCs args, args ~ LCs typs)
    => Int -> MeasureOp typs a -> SArgs abt args -> Doc
ppMeasureOp p (Dirac _) (e1 :* End) =
    ppFun p "dirac" [ppArg e1]
ppMeasureOp p Lebesgue End =
    PP.text "lebesgue"
ppMeasureOp p Counting End =
    PP.text "counting"
ppMeasureOp p Categorical (e1 :* End) =
    ppFun p "categorical" [ppArg e1]
ppMeasureOp p Uniform (e1 :* e2 :* End) =
    ppFun p "uniform" [ppArg e1, ppArg e2]
ppMeasureOp p Normal (e1 :* e2 :* End) =
    ppFun p "normal" [ppArg e1, ppArg e2]
ppMeasureOp p Poisson (e1 :* End) =
    ppFun p "poisson" [ppArg e1]
ppMeasureOp p Gamma (e1 :* e2 :* End) =
    ppFun p "gamma" [ppArg e1, ppArg e2]
ppMeasureOp p Beta (e1 :* e2 :* End) =
    ppFun p "beta" [ppArg e1, ppArg e2]
ppMeasureOp p (DirichletProcess _) (e1 :* e2 :* End) =
    ppFun p "dp" [ppArg e1, ppArg e2]
ppMeasureOp p (Plate _) (e1 :* End) =
    ppFun p "plate" [ppArg e1]
ppMeasureOp p (Chain _ _) (e1 :* e2 :* End) =
    ppFun p "chain" [ppArg e1, ppArg e2]
-- HACK: GHC can't figure out that there are no other type-safe cases
ppMeasureOp _ _ _ = error "ppMeasureOp: the impossible happened"


instance Pretty Value where
    prettyPrec_ p (VNat   n) = ppFun p "nat_"  [PP.int (fromNat n)]
    prettyPrec_ p (VInt   i) = ppFun p "int_"  [PP.int i]
    prettyPrec_ p (VProb  l) = ppFun p "prob_" [PP.text (showsPrec 11 l "")]
        -- TODO: make it prettier! (e.g., don't use LogFloat in the AST)
    prettyPrec_ p (VReal  r) = ppFun p "real_" [PP.double r] -- TODO: make it prettier! (i.e., don't use Double in the AST)
    prettyPrec_ p (VDatum d) = prettyPrec_ p d


instance Pretty f => Pretty (Datum f) where
    prettyPrec_ p (Datum hint d)
        | Text.null hint =
            ppFun p "datum_"
                [error "TODO: prettyPrec_@Datum"]
        | otherwise = 
            ppFun p (Text.unpack hint)
                (foldMap11 ((:[]) . prettyPrec_ 11) d)


instance (ABT abt) => Pretty (Branch a abt) where
    prettyPrec_ p (Branch pat e) =
        ppFun p "Branch"
            [ PP.text (showsPrec 11 pat "") -- HACK: make prettier. Especially since we have the hints!
            , ppBinder e -- BUG: we can't actually use the HOAS API here, since we aren't using a Prelude-defined @branch@...
            ]

ppList :: [Doc] -> Doc
ppList = PP.brackets . PP.nest 1 . PP.fsep . PP.punctuate PP.comma

tryParens :: Bool -> Doc -> Doc
tryParens True  = PP.parens
tryParens False = id

ppTuple :: [Doc] -> Doc
ppTuple = PP.parens . PP.sep . PP.punctuate PP.comma

ppFun :: Int -> String -> [Doc] -> Doc
ppFun _ f [] = PP.text f
ppFun p f ds =
    tryParens (p > 9) (PP.text f <+> PP.nest (1 + length f) (PP.sep ds))

ppArg :: (ABT abt) => abt '[] a -> Doc
ppArg = prettyPrec 11


data Associativity = LeftAssoc | RightAssoc | NonAssoc

ppBinop
    :: (ABT abt)
    => String -> Int -> Associativity
    -> Int -> abt '[] a -> abt '[] b -> Doc
ppBinop op p0 assoc =
    let (p1,p2) =
            case assoc of
            LeftAssoc  -> (p0, 1 + p0)
            RightAssoc -> (1 + p0, p0)
            NonAssoc   -> (1 + p0, 1 + p0)
    in \p e1 e2 -> 
        tryParens (p > p0) $ PP.sep
            [ prettyPrec p1 e1
            , PP.text op
                <+> prettyPrec p2 e2
            ]

----------------------------------------------------------------
----------------------------------------------------------- fin.