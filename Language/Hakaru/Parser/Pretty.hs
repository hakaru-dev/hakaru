{-# LANGUAGE GADTs
           , KindSignatures
           , DataKinds
           , FlexibleContexts
           , UndecidableInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.11.17
-- |
-- Module      :  Language.Hakaru.Parser.Pretty
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
--
----------------------------------------------------------------
module Language.Hakaru.Parser.Pretty
    (
    -- * The user-facing API
      pretty
    , prettyPrec
    , prettyAssoc
    , prettyPrecAssoc

    -- * Helper functions (semi-public internal API)
    , ppVariable
    ) where

import           System.Console.ANSI
import           Text.PrettyPrint (Doc, (<>), (<+>))
import qualified Text.PrettyPrint as PP
import qualified Data.Foldable    as F
import           Data.Number.LogFloat
import qualified Data.Text        as Text
import qualified Data.Sequence    as Seq -- Because older versions of "Data.Foldable" do not export 'null' apparently...

import Language.Hakaru.Syntax.Nat      (fromNat)
import Language.Hakaru.Syntax.IClasses (fmap11, foldMap11)
import Language.Hakaru.Syntax.HClasses
import Language.Hakaru.Syntax.Coercion
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.ABT
----------------------------------------------------------------

-- | Pretty-print a term.
pretty :: (ABT AST abt) => abt '[] a -> Doc
pretty = prettyPrec 0


-- | Pretty-print a term at a given precendence level.
prettyPrec :: (ABT AST abt) => Int -> abt '[] a -> Doc
prettyPrec p = toDoc . prettyPrec_ p . LC_


-- | Pretty-print a variable\/term association pair.
prettyAssoc :: (ABT AST abt) => Assoc abt -> Doc
prettyAssoc = prettyPrecAssoc 0


-- | Pretty-print an association at a given precendence level.
prettyPrecAssoc :: (ABT AST abt) => Int -> Assoc abt -> Doc
prettyPrecAssoc p (Assoc x e) =
    toDoc $ ppFun p "Assoc"
        [ ppVariable x
        , prettyPrec 11 e
        ]

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
color c d = PP.text (setSGRCode [SetColor Foreground Dull c]) <>  d <> PP.text (setSGRCode [Reset])

-- | Pretty-print a variable.
ppVariable :: Variable (a :: Hakaru) -> Doc
ppVariable x = hint <> (PP.int . fromNat . varID) x
    where
    hint
        | Text.null (varHint x) = PP.char 'x'
        | otherwise             = (PP.text . Text.unpack . varHint) x


-- | Pretty-print Hakaru binders as a Haskell lambda, as per our HOAS API.
ppBinder :: (ABT AST abt) => abt xs a -> Docs
ppBinder e =
    case go [] (viewABT e) of
    ([],  body) -> body
    (vars,body) -> PP.char '\\' <> PP.sep vars <+> PP.text "-> " : body
    where
    go :: (ABT AST abt) => [Doc] -> View (AST abt) xs a -> ([Doc],Docs)
    go xs (Bind x v) = go (ppVariable x : xs) v
    go xs (Var  x)   = (reverse xs, [ppVariable x])
    go xs (Syn  t)   = (reverse xs, prettyPrec_ 0 (LC_ (syn t)))

ppBinder2 :: (ABT AST abt) => abt xs a -> ([Doc],Docs)
ppBinder2 e = go [] (viewABT e)
    where
    go :: (ABT AST abt) => [Doc] -> View (AST abt) xs a -> ([Doc],Docs)
    go xs (Bind x v) = go (ppVariable x : xs) v
    go xs (Var  x)   = (reverse xs, [ppVariable x])
    go xs (Syn  t)   = (reverse xs, prettyPrec_ 0 (LC_ (syn t)))


-- TODO: since switching to ABT2, this instance requires -XFlexibleContexts; we should fix that if we can
-- BUG: since switching to ABT2, this instance requires -XUndecidableInstances; must be fixed!
instance (ABT AST abt) => Pretty (LC_ abt) where
  prettyPrec_ p (LC_ e) =
    caseVarSyn e ((:[]) . ppVariable) $ \t -> 
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
                prettyNaryOp (Sum  _) = ("+ ",     6, Just "zero")
                prettyNaryOp (Prod _) = ("* ",     7, Just "one")
            in
            let (opName,opPrec,maybeIdentity) = prettyNaryOp o in
            if Seq.null es
            then
                case maybeIdentity of
                Just identity -> [PP.text identity]
                Nothing ->
                    ppFun p "syn"
                        [ toDoc $ ppFun 11 "NaryOp_"
                            [ PP.text (showsPrec 11 o "")
                            , PP.text "(Seq.fromList [])"
                            ]]
            else
                parens (p > opPrec)
                    . PP.punctuate (PP.space <> PP.text opName)
                    . map (prettyPrec opPrec)
                    $ F.toList es

        Value_ v      -> prettyPrec_ p v
        Empty_        -> [PP.text "empty"]
        Array_ e1 e2  ->
            ppFun p "array"
                [ toDoc $ ppArg e1
                , toDoc $ ppBinder e2
                ]
        Datum_ d      -> prettyPrec_ p (fmap11 LC_ d)
        Case_  e1 bs  ->
            -- TODO: should we also add hints to the 'Case_' constructor to know whether it came from 'if_', 'unpair', etc?
            ppFun p "syn"
                [ toDoc $ ppFun 11 "Case_"
                    [ toDoc $ ppArg e1
                    , toDoc $ ppList (map (toDoc . prettyPrec_ 0) bs)
                    ]]
        Superpose_ pes ->
            -- TODO: use the old PrettyPrint.hs's hack for when there's exactly one thing in the list; i.e., print as @weight w *> m@ with the appropriate do-notation indentation for @(*>)@ (or using 'pose' and @($)@)
            ppFun p "superpose"
                [ toDoc
                . ppList
                . map (\(e1,e2) -> ppTuple [pretty e1, pretty e2])
                $ pes
                ]
        Lub_ es ->
            ppFun p "syn"
                [ toDoc $ ppFun 11 "Lub_"
                    [ toDoc $ ppList (map pretty es) ]]


-- | Pretty-print @(:$)@ nodes in the AST.
ppSCon :: (ABT AST abt) => Int -> SCon args a -> SArgs abt args -> Docs
ppSCon p Lam_ (e1 :* End) =
    let (vars, body) = ppBinder2 e1 in
    [PP.text "fn" <+> toDoc vars <> PP.colon <+> (toDoc body)]
ppSCon p App_ (e1 :* e2 :* End) = ppArg e1 ++ parens True (ppArg e2)
ppSCon p Let_ (e1 :* e2 :* End) =
    let (vars, body) = ppBinder2 e2 in
    [toDoc vars <+> PP.equals <+> toDoc (ppArg e1)
           PP.$$ (toDoc body)]


ppSCon p Fix_       (e1 :* End) = ppFun p "fix"  [toDoc $ ppBinder e1]
ppSCon p (Ann_ typ) (e1 :* End) =
    ppFun p "ann_"
        [ PP.text (showsPrec 11 typ "") -- TODO: make this prettier. Add hints to the singletons?
        , toDoc $ ppArg e1
        ]
ppSCon p (PrimOp_     o) es          = ppPrimOp  p o es
ppSCon p (ArrayOp_    o) es          = ppArrayOp p o es
ppSCon p (CoerceTo_   c) (e1 :* End) =
    ppFun p ""
        [ PP.text (ppCoerce c) -- TODO: make this prettier. Add hints to the coercions?
        , toDoc $ ppArg e1
        ]
ppSCon p (UnsafeFrom_ c) (e1 :* End) =
    ppFun p ""
        [ PP.text (ppUnsafe c) -- TODO: make this prettier. Add hints to the coercions?
        , toDoc $ ppArg e1
        ]
ppSCon p (MeasureOp_ o) es       = ppMeasureOp p o es
ppSCon p Dirac (e1 :* End)       = ppApply1 p "dirac" e1
ppSCon p MBind (e1 :* e2 :* End) =
    let (vars, body) = ppBinder2 e2 in
    [toDoc vars <+> PP.text "<~" <+> toDoc (ppArg e1)
           PP.$$ (toDoc body)]

ppSCon p Expect (e1 :* e2 :* End) =
    -- N.B., for this to be read back in correctly, "Language.Hakaru.Expect" must be in scope as well as the prelude.
    parens (p > 0) $
        adjustHead
            (PP.text "expect" <+> toDoc (ppArg e1) <+> PP.char '$' <+>)
            (ppBinder e2)

ppSCon p Integrate (e1 :* e2 :* e3 :* End) =
    ppFun p "integrate"
        [ toDoc $ ppArg e1
        , toDoc $ ppArg e2
        , toDoc $ parens True (ppBinder e3)
        ]
ppSCon p Summate (e1 :* e2 :* e3 :* End) =
    ppFun p "summate"
        [ toDoc $ ppArg e1
        , toDoc $ ppArg e2
        , toDoc $ parens True (ppBinder e3)
        ]

-- HACK: GHC can't figure out that there are no other type-safe cases
ppSCon _ _ _ = error "ppSCon: the impossible happened"


ppCoerce :: Coercion a b -> String
ppCoerce (CCons (Signed HRing_Real) CNil) = "fromProb"
ppCoerce (CCons (Signed HRing_Int ) CNil) = "nat2int"
ppCoerce (CCons (Continuous HContinuous_Real ) CNil) = "fromInt"
ppCoerce (CCons (Continuous HContinuous_Prob  ) CNil) = "nat2prob"
ppCoerce (CCons (Signed HRing_Int) (CCons (Continuous HContinuous_Real) CNil)) = "nat2real"
ppCoerce c = "coerceTo_ " ++ showsPrec 11 c ""

ppUnsafe :: Coercion a b -> String
ppUnsafe (CCons (Signed HRing_Real) CNil) = "unsafeProb"
ppUnsafe (CCons (Signed HRing_Int ) CNil) = "unsafeNat"
ppUnsafe c = "unsafeFrom_ " ++ showsPrec 11 c ""

-- | Pretty-print a 'PrimOp' @(:$)@ node in the AST.
ppPrimOp
    :: (ABT AST abt, typs ~ UnLCs args, args ~ LCs typs)
    => Int -> PrimOp typs a -> SArgs abt args -> Docs
ppPrimOp p Not  (e1 :* End)       = ppApply1 p "not" e1
ppPrimOp p Impl (e1 :* e2 :* End) =
    -- TODO: make prettier
    ppFun p "syn"
        [ toDoc $ ppFun 11 "Impl"
            [ toDoc $ ppArg e1
            , toDoc $ ppArg e2
            ]]
ppPrimOp p Diff (e1 :* e2 :* End) =
    -- TODO: make prettier
    ppFun p "syn"
        [ toDoc $ ppFun 11 "Diff"
            [ toDoc $ ppArg e1
            , toDoc $ ppArg e2
            ]]
ppPrimOp p Nand (e1 :* e2 :* End) = ppApply2 p "nand" e1 e2 -- TODO: make infix...
ppPrimOp p Nor  (e1 :* e2 :* End) = ppApply2 p "nor" e1 e2 -- TODO: make infix...
ppPrimOp _ Pi        End               = [PP.text "pi"]
ppPrimOp p Sin       (e1 :* End)       = ppApply1 p "sin"   e1
ppPrimOp p Cos       (e1 :* End)       = ppApply1 p "cos"   e1
ppPrimOp p Tan       (e1 :* End)       = ppApply1 p "tan"   e1
ppPrimOp p Asin      (e1 :* End)       = ppApply1 p "asin"  e1
ppPrimOp p Acos      (e1 :* End)       = ppApply1 p "acos"  e1
ppPrimOp p Atan      (e1 :* End)       = ppApply1 p "atan"  e1
ppPrimOp p Sinh      (e1 :* End)       = ppApply1 p "sinh"  e1
ppPrimOp p Cosh      (e1 :* End)       = ppApply1 p "cosh"  e1
ppPrimOp p Tanh      (e1 :* End)       = ppApply1 p "tanh"  e1
ppPrimOp p Asinh     (e1 :* End)       = ppApply1 p "asinh" e1
ppPrimOp p Acosh     (e1 :* End)       = ppApply1 p "acosh" e1
ppPrimOp p Atanh     (e1 :* End)       = ppApply1 p "atanh" e1
ppPrimOp p RealPow   (e1 :* e2 :* End) = ppBinop "**" 8 RightAssoc p e1 e2
ppPrimOp p Exp       (e1 :* End)       = ppApply1 p "exp"   e1
ppPrimOp p Log       (e1 :* End)       = ppApply1 p "log"   e1
ppPrimOp _ Infinity         End        = [PP.text "infinity"]
ppPrimOp _ NegativeInfinity End        = [PP.text "negativeInfinity"]
ppPrimOp p GammaFunc (e1 :* End)       = ppApply1 p "gammaFunc" e1
ppPrimOp p BetaFunc  (e1 :* e2 :* End) = ppApply2 p "betaFunc" e1 e2

ppPrimOp p (Equal   _) (e1 :* e2 :* End) = ppBinop "==" 4 NonAssoc   p e1 e2
ppPrimOp p (Less    _) (e1 :* e2 :* End) = ppBinop "<"  4 NonAssoc   p e1 e2
ppPrimOp p (NatPow  _) (e1 :* e2 :* End) = ppBinop "^"  8 RightAssoc p e1 e2
ppPrimOp p (Negate  _) (e1 :* End)       = ppApply1 p "negate" e1
ppPrimOp p (Abs     _) (e1 :* End)       = ppApply1 p "abs_"   e1
ppPrimOp p (Signum  _) (e1 :* End)       = ppApply1 p "signum" e1
ppPrimOp p (Recip   _) (e1 :* End)       = ppApply1 p "recip"  e1
ppPrimOp p (NatRoot _) (e1 :* e2 :* End) =
    -- N.B., argument order is swapped!
    ppBinop "`thRootOf`" 9 LeftAssoc p e2 e1
ppPrimOp p (Erf _) (e1 :* End) = ppApply1 p "erf" e1
-- HACK: GHC can't figure out that there are no other type-safe cases
ppPrimOp _ _ _ = error "ppPrimOp: the impossible happened"


-- | Pretty-print a 'ArrayOp' @(:$)@ node in the AST.
ppArrayOp
    :: (ABT AST abt, typs ~ UnLCs args, args ~ LCs typs)
    => Int -> ArrayOp typs a -> SArgs abt args -> Docs
ppArrayOp p (Index   _) (e1 :* e2 :* End) = ppBinop "!" 9 LeftAssoc p e1 e2
ppArrayOp p (Size    _) (e1 :* End)       = ppApply1 p "size" e1
ppArrayOp p (Reduce  _) (e1 :* e2 :* e3 :* End) =
    ppFun p "reduce"
        [ toDoc $ ppArg e1 -- N.B., @e1@ uses lambdas rather than being a binding form!
        , toDoc $ ppArg e2
        , toDoc $ ppArg e3
        ]
ppArrayOp _ _ _ = error "ppArrayOp: the impossible happened"



-- | Pretty-print a 'MeasureOp' @(:$)@ node in the AST.
ppMeasureOp
    :: (ABT AST abt, typs ~ UnLCs args, args ~ LCs typs)
    => Int -> MeasureOp typs a -> SArgs abt args -> Docs
ppMeasureOp _ Lebesgue    End           = [PP.text "lebesgue"]
ppMeasureOp _ Counting    End           = [PP.text "counting"]
ppMeasureOp p Categorical (e1 :* End)   = ppApply1 p "categorical" e1
ppMeasureOp p Uniform (e1 :* e2 :* End) = ppApply2 p "uniform"     e1 e2
ppMeasureOp p Normal  (e1 :* e2 :* End) = ppApply2 p "normal"      e1 e2
ppMeasureOp p Poisson (e1 :* End)       = ppApply1 p "poisson"     e1
ppMeasureOp p Gamma   (e1 :* e2 :* End) = ppApply2 p "gamma"       e1 e2
ppMeasureOp p Beta    (e1 :* e2 :* End) = ppApply2 p "beta"        e1 e2
ppMeasureOp p (DirichletProcess _) (e1 :* e2 :* End) = ppApply2 p "dp" e1 e2
ppMeasureOp p (Plate _)   (e1 :* End)       = ppApply1 p "plate" e1
ppMeasureOp p (Chain _ _) (e1 :* e2 :* End) = ppApply2 p "chain" e1 e2
-- HACK: GHC can't figure out that there are no other type-safe cases
ppMeasureOp _ _ _ = error "ppMeasureOp: the impossible happened"


instance Pretty Value where
    prettyPrec_ _ (VNat   n) = [PP.int (fromNat n)]
    prettyPrec_ _ (VInt   i) = [PP.int i]
    prettyPrec_ _ (VProb  l) = [PP.text (showsPrec 11 (fromLogFloat l) "")]
        -- TODO: make it prettier! (e.g., don't use LogFloat in the AST)
    prettyPrec_ _ (VReal  r) = [PP.double r]
        -- TODO: make it prettier! (i.e., don't use Double in the AST)
    prettyPrec_ p (VDatum d) = prettyPrec_ p d


instance Pretty f => Pretty (Datum f) where
    prettyPrec_ p (Datum hint d)
        | Text.null hint =
            ppFun p "datum_"
                [error "TODO: prettyPrec_@Datum"]
        | otherwise = 
            ppFun p (Text.unpack hint)
                (foldMap11 ((:[]) . toDoc . prettyPrec_ 11) d)


-- HACK: need to pull this out in order to get polymorphic recursion over @xs@
ppPattern :: Int -> Pattern xs a -> Docs
ppPattern _ PWild = [PP.text "PWild"]
ppPattern _ PVar  = [PP.text "PVar"]
ppPattern p (PDatum hint d0)
    | Text.null hint = error "TODO: prettyPrec_@Pattern"
    | otherwise      = ppFun p (Text.unpack hint) (goCode d0)
    where
    goCode :: PDatumCode xss vars a -> Docs
    goCode (PInr d) = goCode   d
    goCode (PInl d) = goStruct d

    goStruct :: PDatumStruct xs vars a -> Docs
    goStruct PDone       = []
    goStruct (PEt d1 d2) = goFun d1 ++ goStruct d2

    goFun :: PDatumFun x vars a -> Docs
    goFun (PKonst d) = [toDoc $ ppPattern 11 d]
    goFun (PIdent d) = [toDoc $ ppPattern 11 d]


instance Pretty (Pattern xs) where
    prettyPrec_ = ppPattern


instance (ABT AST abt) => Pretty (Branch a abt) where
    prettyPrec_ p (Branch pat e) =
        ppFun p "Branch"
            [ toDoc $ prettyPrec_ 11 pat
            , PP.parens . toDoc $ ppBinder e -- BUG: we can't actually use the HOAS API here, since we aren't using a Prelude-defined @branch@...
            -- HACK: don't *always* print parens; pass down the precedence to 'ppBinder' to have them decide if they need to or not.
            ]

----------------------------------------------------------------
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
ppFun _ f ds = [PP.text f, PP.nest (1 + length f) (ppTuple ds)]

ppArg :: (ABT AST abt) => abt '[] a -> Docs
ppArg = prettyPrec_ 11 . LC_

ppApply1 :: (ABT AST abt) => Int -> String -> abt '[] a -> Docs
ppApply1 p f e1 = ppFun p f [toDoc $ ppArg e1]

ppApply2 :: (ABT AST abt) => Int -> String -> abt '[] a -> abt '[] b -> Docs
ppApply2 p f e1 e2 = ppFun p f [toDoc $ ppArg e1, toDoc $ ppArg e2]

{-
-- TODO: for when we update the representation of HReal\/HProb values to use rationals rather than Double\/LogFloat.
ppRational :: Int -> Rational -> Doc
ppRational p r
    | d == 1    = ppInteger n
    | otherwise = PP.cat [ppInteger n, PP.char '/' <> ppInteger d ]
    where
    ppInteger = PP.text . show
    d = denominator r
    n = numerator   r

-- If we decide to generalize the above to all Ratio, then we'd need something like:
showRatio :: (Show a, Integral a) => Int -> Ratio a -> ShowS
showRatio p r
    | num < 0    =
        showParen (p > 6)
            $ showChar '-'
            . showRatio 7 (-r)
    | denom == 1 = showsPrec p n
    | otherwise  =
        showParen (p > 7)
            $ showsPrec 8 n 
            . showChar '/' 
            . showsPrec 8 d
    where
    d = denominator r
    n = numerator   r
-}

data Associativity = LeftAssoc | RightAssoc | NonAssoc

ppBinop
    :: (ABT AST abt)
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
            , PP.text op
                <+> prettyPrec p2 e2
            ]

----------------------------------------------------------------
----------------------------------------------------------- fin.
