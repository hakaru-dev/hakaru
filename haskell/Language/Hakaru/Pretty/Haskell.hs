{-# LANGUAGE GADTs
           , OverloadedStrings
           , KindSignatures
           , DataKinds
           , FlexibleContexts
           , UndecidableInstances
           , LambdaCase
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.02.21
-- |
-- Module      :  Language.Hakaru.Pretty.Haskell
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
--
----------------------------------------------------------------
module Language.Hakaru.Pretty.Haskell
    (
    -- * The user-facing API
      pretty
    , prettyString
    , prettyPrec
    , prettyAssoc
    , prettyPrecAssoc
    , prettyType

    -- * Helper functions (semi-public internal API)
    , ppVariable
    , ppVariables
    , ppBinder
    , ppCoerceTo
    , ppUnsafeFrom
    , ppRatio
    , Associativity(..)
    , ppBinop
    , Pretty(..)
    ) where
import           Data.Ratio
import           Text.PrettyPrint (Doc, (<>), (<+>))
import qualified Text.PrettyPrint   as PP
import qualified Data.Foldable      as F
import qualified Data.List.NonEmpty as L
import qualified Data.Text          as Text
import qualified Data.Sequence      as Seq -- Because older versions of "Data.Foldable" do not export 'null' apparently...

import Data.Number.Nat                 (fromNat)
import Data.Number.Natural             (fromNatural)
import Language.Hakaru.Syntax.IClasses (fmap11, foldMap11, List1(..)
                                       ,Foldable21(..))
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Types.Sing
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.Reducer
import Language.Hakaru.Syntax.ABT
----------------------------------------------------------------

-- | Pretty-print a term.
pretty :: (ABT Term abt) => abt '[] a -> Doc
pretty = prettyPrec 0


prettyString :: (ABT Term abt)
           => Sing a
           -> abt '[] a
           -> Doc
prettyString typ ast =
  PP.text $ Text.unpack (Text.unlines $ header  ++ [ Text.pack (prettyProg "prog" typ ast)])

prettyProg :: (ABT Term abt)
           => String
           -> Sing a
           -> abt '[] a
           -> String
prettyProg name typ ast =
    PP.renderStyle PP.style
    (    PP.sep [PP.text (name ++ " ::"), PP.nest 2 (prettyType typ)]
     PP.$+$ PP.sep [PP.text (name ++ " =") , PP.nest 2 (pretty     ast)] )

-- | Pretty-print a term at a given precendence level.
prettyPrec :: (ABT Term abt) => Int -> abt '[] a -> Doc
prettyPrec p = toDoc . prettyPrec_ p . LC_


-- | Pretty-print a variable\/term association pair.
prettyAssoc :: (ABT Term abt) => Assoc (abt '[]) -> Doc
prettyAssoc = prettyPrecAssoc 0


-- | Pretty-print an association at a given precendence level.
prettyPrecAssoc :: (ABT Term abt) => Int -> Assoc (abt '[]) -> Doc
prettyPrecAssoc p (Assoc x e) =
    toDoc $ ppFun p "Assoc"
        [ ppVariable x
        , prettyPrec 11 e
        ]


-- | Pretty-print a Hakaru type as a Haskell type.
prettyType :: Sing (a :: Hakaru) -> Doc
prettyType SInt = PP.text "Int"
prettyType SNat = PP.text "Int"
prettyType SReal = PP.text "Double"
prettyType SProb = PP.text "Prob"
prettyType (SArray t) =
  let t' = PP.nest 2 (prettyType t) in
  PP.parens (PP.sep [PP.text "MayBoxVec", t', t'])
prettyType (SMeasure t) =
  PP.parens (PP.sep [PP.text "Measure", PP.nest 2 (prettyType t)])
prettyType (SFun t1 t2) =
  PP.parens (PP.sep [prettyType t1 <+> PP.text "->", prettyType t2])
prettyType (SData _ (SDone `SPlus` SVoid)) =
  PP.text "()"
prettyType (SData _ (SDone `SPlus` SDone `SPlus` SVoid)) =
  PP.text "Bool"
prettyType (SData _ (SDone `SPlus` (SKonst t `SEt` SDone) `SPlus` SVoid)) =
  PP.parens (PP.sep [PP.text "Maybe", PP.nest 2 (prettyType t)])
prettyType (SData _ ((SKonst t1 `SEt` SDone) `SPlus`
                     (SKonst t2 `SEt` SDone) `SPlus` SVoid)) =
  PP.parens (PP.sep [PP.text "Either", PP.nest 2 (prettyType t1),
                                       PP.nest 2 (prettyType t2)])
prettyType (SData _ ((SKonst t1 `SEt` SKonst t2 `SEt` SDone) `SPlus` SVoid)) =
  PP.parens (PP.sep [prettyType t1 <> PP.comma, prettyType t2])
prettyType s = error ("TODO: prettyType: " ++ show s)


----------------------------------------------------------------
class Pretty (f :: Hakaru -> *) where
    -- | A polymorphic variant if 'prettyPrec', for internal use.
    prettyPrec_ :: Int -> f a -> Docs

type Docs = [Doc]

-- So far as I can tell from the documentation, if the input is a singleton list then the result is the same as that singleton.
toDoc :: Docs -> Doc
toDoc = PP.sep


-- | Pretty-print a variable.
ppVariable :: Variable (a :: Hakaru) -> Doc
ppVariable x = hint <> (PP.int . fromNat . varID) x
    where
    hint
        | Text.null (varHint x) = PP.char 'x' -- We used to use '_' but...
        | otherwise             = (PP.text . Text.unpack . varHint) x

-- | Pretty-print a list of variables as a list of variables. N.B., the output is not valid Haskell code since it uses the special built-in list syntax rather than using the 'List1' constructors...
ppVariables :: List1 Variable (xs :: [Hakaru]) -> Docs
ppVariables = ppList . go
    where
    go :: List1 Variable (xs :: [Hakaru]) -> Docs
    go Nil1         = []
    go (Cons1 x xs) = ppVariable x : go xs


-- | Pretty-print Hakaru binders as a Haskell lambda, as per our HOAS API.
ppBinder :: (ABT Term abt) => abt xs a -> Docs
ppBinder e =
    case ppViewABT e of
    ([],  body) -> body
    (vars,body) -> PP.char '\\' <+> PP.sep vars <+> PP.text "->" : body

ppUncurryBinder :: (ABT Term abt) => abt xs a -> Docs
ppUncurryBinder e =
    case ppViewABT e of
    (vars,body) -> PP.char '\\' <+> unc vars <+> PP.text "->" : body
    where
    unc :: [Doc] -> Doc
    unc []     = PP.text "()"
    unc (x:xs) = PP.parens (x <> PP.comma <> unc xs)

ppViewABT :: (ABT Term abt) => abt xs a -> ([Doc], Docs)
ppViewABT e = go [] (viewABT e)
    where
    go :: (ABT Term abt) => [Doc] -> View (Term abt) xs a -> ([Doc],Docs)
    go xs (Syn  t)   = (reverse xs, prettyPrec_ 0 (LC_ (syn t)))
    go xs (Var  x)   = (reverse xs, [ppVariable x])
    go xs (Bind x v) =
        -- HACK: how can we avoid calling 'unviewABT' here?
        let x' = if True -- x `memberVarSet` freeVars (unviewABT v)
                 then ppVariable x
                 else PP.char '_'
        in go (x' : xs) v


-- TODO: since switching to ABT2, this instance requires -XFlexibleContexts; we should fix that if we can
-- BUG: since switching to ABT2, this instance requires -XUndecidableInstances; must be fixed!
instance (ABT Term abt) => Pretty (LC_ abt) where
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
                -- TODO: pretty print @(+ negate)@ as @(-)@ and @(* recip)@ as @(/)@
                prettyNaryOp (Sum  _) = ("+",     6, Just "zero")
                prettyNaryOp (Prod _) = ("*",     7, Just "one")
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

        Literal_ v    -> prettyPrec_ p v
        Empty_   _    -> [PP.text "empty"]
        Array_ e1 e2  ->
            ppFun 11 "array"
                [ ppArg e1 <+> PP.char '$'
                , toDoc $ ppBinder e2
                ]
        ArrayLiteral_ es -> ppFun 11 "arrayLit" (ppList $ map (prettyPrec 0) es)
        Datum_ d      -> prettyPrec_ p (fmap11 LC_ d)
        Case_  e1 bs  ->
            -- TODO: should we also add hints to the 'Case_' constructor to know whether it came from 'if_', 'unpair', etc?
             ppFun p "case_"
                 [ ppArg e1
                 , toDoc $ ppList (map (toDoc . prettyPrec_ 0) bs)
                 ]
        Bucket b e r  ->
            ppFun p "bucket"
            [ ppArg b
            , ppArg e
            , toDoc $ parens True (prettyPrec_ p r)
            ]

        Superpose_ pes ->
            case pes of
            (e1,e2) L.:| [] ->
                -- Or we could print it as @weight e1 *> e2@ excepting that has an extra redex in it compared to the AST itself.
                ppFun 11 "pose"
                    [ ppArg e1 <+> PP.char '$'
                    , ppArg e2
                    ]
            _ ->
                ppFun p "superpose"
                    [ toDoc
                    . ppList
                    . map (\(e1,e2) -> ppTuple [pretty e1, pretty e2])
                    $ L.toList pes
                    ]

        Reject_ _ -> [PP.text "reject"]

-- | Pretty-print @(:$)@ nodes in the AST.
ppSCon :: (ABT Term abt) => Int -> SCon args a -> SArgs abt args -> Docs
ppSCon p Lam_ = \(e1 :* End) ->
    parens (p > 0) $ adjustHead (PP.text "lam $" <+>) (ppBinder e1)
ppSCon p App_ = \(e1 :* e2 :* End) -> ppBinop "`app`" 9 LeftAssoc p e1 e2 -- BUG: this puts extraneous parentheses around e2 when it's a function application...
ppSCon p Let_ = \(e1 :* e2 :* End) ->
    parens (p > 0) $
        adjustHead
            (PP.text "let_" <+> ppArg e1 <+> PP.char '$' <+>)
            (ppBinder e2)
{-
ppSCon p (Ann_ typ) = \(e1 :* End) ->
    ppFun p "ann_"
        [ PP.text (showsPrec 11 typ "") -- TODO: make this prettier. Add hints to the singletons?
        , ppArg e1
        ]
-}
ppSCon p (PrimOp_     o) = \es          -> ppPrimOp     p o es
ppSCon p (ArrayOp_    o) = \es          -> ppArrayOp    p o es
ppSCon p (CoerceTo_   c) = \(e1 :* End) -> ppCoerceTo   p c e1
ppSCon p (UnsafeFrom_ c) = \(e1 :* End) -> ppUnsafeFrom p c e1
ppSCon p (MeasureOp_  o) = \es          -> ppMeasureOp  p o es
ppSCon p Dirac           = \(e1 :* End) -> ppApply1 p "dirac" e1
ppSCon p MBind = \(e1 :* e2 :* End) ->
    parens (p > 1) $
        adjustHead
            (prettyPrec 1 e1 <+> PP.text ">>=" <+>)
            (ppBinder e2)
ppSCon p (Transform_ t) = ppTransform p t
ppSCon p Integrate = \(e1 :* e2 :* e3 :* End) ->
    ppFun p "integrate"
        [ ppArg e1
        , ppArg e2
        , toDoc $ parens True (ppBinder e3)
        ]
ppSCon p (Summate _ _) = \(e1 :* e2 :* e3 :* End) ->
    ppFun p "summate"
        [ ppArg e1
        , ppArg e2
        , toDoc $ parens True (ppBinder e3)
        ]

ppSCon p (Product _ _) = \(e1 :* e2 :* e3 :* End) ->
    ppFun p "product"
        [ ppArg e1
        , ppArg e2
        , toDoc $ parens True (ppBinder e3)
        ]

ppSCon _ Plate = \(e1 :* e2 :* End) ->
    ppFun 11 "plate"
        [ ppArg e1 <+> PP.char '$'
        , toDoc $ ppBinder e2
        ]

ppSCon _ Chain = \(e1 :* e2 :* e3 :* End) ->
    ppFun 11 "chain"
        [ ppArg e1
        , ppArg e2 <+> PP.char '$'
        , toDoc $ ppBinder e3
        ]

ppTransform :: (ABT Term abt)
            => Int -> Transform args a -> SArgs abt args -> Docs
ppTransform p t es =
  case t of
     Expect ->
       case es of
         e1 :* e2 :* End ->
           parens (p > 0) $
              adjustHead
                (PP.text "expect" <+> ppArg e1 <+> PP.char '$' <+>)
                (ppBinder e2)
     _ -> ppApply p (transformName t) es

ppCoerceTo :: ABT Term abt => Int -> Coercion a b -> abt '[] a -> Docs
ppCoerceTo =
    -- BUG: this may not work quite right when the coercion isn't one of the special named ones...
    \p c e -> ppFun p (prettyShow c) [ppArg e]
    where
    prettyShow (CCons (Signed HRing_Real) CNil)           = "fromProb"
    prettyShow (CCons (Signed HRing_Int)  CNil)           = "nat2int"
    prettyShow (CCons (Continuous HContinuous_Real) CNil) = "fromInt"
    prettyShow (CCons (Continuous HContinuous_Prob) CNil) = "nat2prob"
    prettyShow (CCons (Continuous HContinuous_Prob)
        (CCons (Signed HRing_Real) CNil))                 = "nat2real"
    prettyShow (CCons (Signed HRing_Int)
        (CCons (Continuous HContinuous_Real) CNil))       = "nat2real"
    prettyShow c = "coerceTo_ " ++ showsPrec 11 c ""


ppUnsafeFrom :: ABT Term abt => Int -> Coercion a b -> abt '[] b -> Docs
ppUnsafeFrom =
    -- BUG: this may not work quite right when the coercion isn't one of the special named ones...
    \p c e -> ppFun p (prettyShow c) [ppArg e]
    where
    prettyShow (CCons (Signed HRing_Real) CNil) = "unsafeProb"
    prettyShow (CCons (Signed HRing_Int)  CNil) = "unsafeNat"
    prettyShow c = "unsafeFrom_ " ++ showsPrec 11 c ""


-- | Pretty-print a 'PrimOp' @(:$)@ node in the AST.
ppPrimOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => Int -> PrimOp typs a -> SArgs abt args -> Docs
ppPrimOp p Not  = \(e1 :* End)       -> ppApply1 p "not" e1
ppPrimOp p Impl = \(e1 :* e2 :* End) ->
    -- TODO: make prettier
    ppFun p "syn"
        [ toDoc $ ppFun 11 "Impl"
            [ ppArg e1
            , ppArg e2
            ]]
ppPrimOp p Diff = \(e1 :* e2 :* End) ->
    -- TODO: make prettier
    ppFun p "syn"
        [ toDoc $ ppFun 11 "Diff"
            [ ppArg e1
            , ppArg e2
            ]]
ppPrimOp p Nand = \(e1 :* e2 :* End)        -> ppApply2 p "nand" e1 e2 -- TODO: make infix...
ppPrimOp p Nor  = \(e1 :* e2 :* End)        -> ppApply2 p "nor" e1 e2 -- TODO: make infix...
ppPrimOp _ Pi        = \End                 -> [PP.text "pi"]
ppPrimOp p Sin       = \(e1 :* End)         -> ppApply1 p "sin"   e1
ppPrimOp p Cos       = \(e1 :* End)         -> ppApply1 p "cos"   e1
ppPrimOp p Tan       = \(e1 :* End)         -> ppApply1 p "tan"   e1
ppPrimOp p Asin      = \(e1 :* End)         -> ppApply1 p "asin"  e1
ppPrimOp p Acos      = \(e1 :* End)         -> ppApply1 p "acos"  e1
ppPrimOp p Atan      = \(e1 :* End)         -> ppApply1 p "atan"  e1
ppPrimOp p Sinh      = \(e1 :* End)         -> ppApply1 p "sinh"  e1
ppPrimOp p Cosh      = \(e1 :* End)         -> ppApply1 p "cosh"  e1
ppPrimOp p Tanh      = \(e1 :* End)         -> ppApply1 p "tanh"  e1
ppPrimOp p Asinh     = \(e1 :* End)         -> ppApply1 p "asinh" e1
ppPrimOp p Acosh     = \(e1 :* End)         -> ppApply1 p "acosh" e1
ppPrimOp p Atanh     = \(e1 :* End)         -> ppApply1 p "atanh" e1
ppPrimOp p RealPow   = \(e1 :* e2 :* End)   -> ppBinop "**" 8 RightAssoc p e1 e2
ppPrimOp p Choose    = \(e1 :* e2 :* End)   -> ppApply2 p "choose" e1 e2
ppPrimOp p Exp       = \(e1 :* End)         -> ppApply1 p "exp"   e1
ppPrimOp p Log       = \(e1 :* End)         -> ppApply1 p "log"   e1
ppPrimOp _ (Infinity _)     = \End          -> [PP.text "infinity"]
ppPrimOp p GammaFunc = \(e1 :* End)         -> ppApply1 p "gammaFunc" e1
ppPrimOp p BetaFunc  = \(e1 :* e2 :* End)   -> ppApply2 p "betaFunc" e1 e2
ppPrimOp p (Equal   _) = \(e1 :* e2 :* End) -> ppBinop "==" 4 NonAssoc   p e1 e2
ppPrimOp p (Less    _) = \(e1 :* e2 :* End) -> ppBinop "<"  4 NonAssoc   p e1 e2
ppPrimOp p (NatPow  _) = \(e1 :* e2 :* End) -> ppBinop "^"  8 RightAssoc p e1 e2
ppPrimOp p (Negate  _) = \(e1 :* End)       -> ppApply1 p "negate" e1
ppPrimOp p (Abs     _) = \(e1 :* End)       -> ppApply1 p "abs_"   e1
ppPrimOp p (Signum  _) = \(e1 :* End)       -> ppApply1 p "signum" e1
ppPrimOp p (Recip   _) = \(e1 :* End)       -> ppApply1 p "recip"  e1
ppPrimOp p (NatRoot _) = \(e1 :* e2 :* End) ->
    -- N.B., argument order is swapped!
    ppBinop "`thRootOf`" 9 LeftAssoc p e2 e1
ppPrimOp p (Erf _)     = \(e1 :* End)        -> ppApply1 p "erf"   e1
ppPrimOp p Floor       = \(e1 :* End)        -> ppApply1 p "floor" e1


-- | Pretty-print a 'ArrayOp' @(:$)@ node in the AST.
ppArrayOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => Int -> ArrayOp typs a -> SArgs abt args -> Docs
ppArrayOp p (Index   _) = \(e1 :* e2 :* End) ->
    ppBinop "!" 9 LeftAssoc p e1 e2
ppArrayOp p (Size    _) = \(e1 :* End) ->
    ppApply1 p "size" e1
ppArrayOp p (Reduce  _) = \(e1 :* e2 :* e3 :* End) ->
    ppFun p "reduce"
        [ ppArg e1 -- N.B., @e1@ uses lambdas rather than being a binding form!
        , ppArg e2
        , ppArg e3
        ]


-- | Pretty-print a 'MeasureOp' @(:$)@ node in the AST.
ppMeasureOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => Int -> MeasureOp typs a -> SArgs abt args -> Docs
ppMeasureOp p Lebesgue    = \(e1 :* e2 :* End) -> ppApply2 p "lebesgue" e1 e2
ppMeasureOp _ Counting    = \End           -> [PP.text "counting"]
ppMeasureOp p Categorical = \(e1 :* End)   -> ppApply1 p "categorical" e1
ppMeasureOp p Uniform = \(e1 :* e2 :* End) -> ppApply2 p "uniform"     e1 e2
ppMeasureOp p Normal  = \(e1 :* e2 :* End) -> ppApply2 p "normal"      e1 e2
ppMeasureOp p Poisson = \(e1 :* End)       -> ppApply1 p "poisson"     e1
ppMeasureOp p Gamma   = \(e1 :* e2 :* End) -> ppApply2 p "gamma"       e1 e2
ppMeasureOp p Beta    = \(e1 :* e2 :* End) -> ppApply2 p "beta"        e1 e2

instance Pretty Literal where
    prettyPrec_ p (LNat  n) = ppFun p "nat_"  [PP.integer (fromNatural n)]
    prettyPrec_ p (LInt  i) = ppFun p "int_"  [PP.integer i]
    prettyPrec_ p (LProb l) = ppFun p "prob_" [ppRatio 11 l]
    prettyPrec_ p (LReal r) = ppFun p "real_" [ppRatio 11 r]


instance Pretty f => Pretty (Datum f) where
    prettyPrec_ p (Datum hint _typ d)
        | Text.null hint =
            ppFun p "datum_"
                [error "TODO: prettyPrec_@Datum"]
        | otherwise =
          ppFun p "ann_"
            [ PP.parens . PP.text . show $ _typ
            , PP.parens . toDoc $ ppFun p (Text.unpack hint)
                (foldMap11 ((:[]) . toDoc . prettyPrec_ 11) d)
            ]

-- HACK: need to pull this out in order to get polymorphic recursion over @xs@
ppPattern :: Int -> Pattern xs a -> Docs
ppPattern _ PWild = [PP.text "PWild"]
ppPattern _ PVar  = [PP.text "PVar"]
ppPattern p (PDatum hint d0)
    | Text.null hint = error "TODO: prettyPrec_@Pattern"
    | otherwise      = ppFun p ("p" ++ Text.unpack hint) (goCode d0)
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


instance (ABT Term abt) => Pretty (Branch a abt) where
    prettyPrec_ p (Branch pat e) =
        ppFun p "branch"
            [ toDoc $ prettyPrec_ 11 pat
            , PP.parens . toDoc $ ppBinder e
            -- BUG: we can't actually use the HOAS API here, since we aren't using a Prelude-defined @branch@...
            -- HACK: don't *always* print parens; pass down the precedence to 'ppBinder' to
            --       have them decide if they need to or not.
            ]

instance (ABT Term abt) => Pretty (Reducer abt xs) where
    prettyPrec_ p (Red_Fanout r1 r2)  =
        ppFun p "r_fanout"
            [ toDoc $ prettyPrec_ 11 r1
            , toDoc $ prettyPrec_ 11 r2
            ]
    prettyPrec_ p (Red_Index n o e)   =
        ppFun p "r_index"
            [ toDoc $ parens True $ ppUncurryBinder n
            , toDoc $ parens True $ ppUncurryBinder o
            , toDoc $ prettyPrec_ 11 e
            ]
    prettyPrec_ p (Red_Split b r1 r2) =
        ppFun p "r_split"
            [ toDoc $ parens True (ppUncurryBinder b)
            , toDoc $ prettyPrec_ 11 r1
            , toDoc $ prettyPrec_ 11 r2
            ]
    prettyPrec_ p Red_Nop             =
        [ PP.text "r_nop" ]
    prettyPrec_ p (Red_Add _ e)       =
        ppFun p "r_add"
            [ toDoc $ parens True (ppUncurryBinder e)]

----------------------------------------------------------------
-- | For the \"@lam $ \x ->\n@\"  style layout.
adjustHead :: (Doc -> Doc) -> Docs -> Docs
adjustHead f []     = [f (toDoc [])]
adjustHead f (d:ds) = f d : ds

{- -- unused
-- | For the \"@lam (\x ->\n\t...)@\"  style layout.
nestTail :: Int -> Docs -> Docs
nestTail _ []     = []
nestTail n (d:ds) = [d, PP.nest n (toDoc ds)]
-}

parens :: Bool -> Docs -> Docs
parens True  ds = [PP.parens (PP.nest 1 (toDoc ds))]
parens False ds = ds

ppList :: [Doc] -> Docs
ppList = (:[]) . PP.brackets . PP.nest 1 . PP.fsep . PP.punctuate PP.comma

ppTuple :: [Doc] -> Doc
ppTuple = PP.parens . PP.sep . PP.punctuate PP.comma

ppFun :: Int -> String -> [Doc] -> Docs
ppFun _ f [] = [PP.text f]
ppFun p f ds =
    parens (p > 9) [PP.text f <+> PP.nest (1 + length f) (PP.sep ds)]

ppArg :: (ABT Term abt) => abt '[] a -> Doc
ppArg = prettyPrec 11

ppApply1 :: (ABT Term abt) => Int -> String -> abt '[] a -> Docs
ppApply1 p f e1 = ppFun p f [ppArg e1]

ppApply2
    :: (ABT Term abt) => Int -> String -> abt '[] a -> abt '[] b -> Docs
ppApply2 p f e1 e2 = ppFun p f [ppArg e1, ppArg e2]

ppApply
    :: (ABT Term abt) => Int -> String -> SArgs abt as -> Docs
ppApply p f es = ppFun p f $ foldMap21 ppBinder es

-- | Something prettier than 'PP.rational'. This works correctly
-- for both 'Rational' and 'NonNegativeRational', though it may not
-- work for other @a@ types.
--
-- N.B., the resulting string assumes prefix negation and the
-- 'Fractional' @(/)@ operator are both in scope.
ppRatio :: (Show a, Integral a) => Int -> Ratio a -> Doc
ppRatio p r
    | d == 1    = ppShowS $ showsPrec p n
    | n < 0     =
        ppShowS
        . showParen (p > 7)
            $ showChar '-' -- TODO: is this guaranteed valid no matter @a@?
            . showsPrec 8 (negate n)
            . showChar '/'
            . showsPrec 8 d
    | otherwise =
        ppShowS
        . showParen (p > 7)
            $ showsPrec 8 n
            . showChar '/'
            . showsPrec 8 d
    where
    d = denominator r
    n = numerator   r

    ppShowS s = PP.text (s [])

    {-
    -- TODO: we might prefer to use something like:
    PP.cat [ppIntegral n, PP.char '/' <> ppIntegral d ]
    where ppIntegral = PP.text . show
    -}


data Associativity = LeftAssoc | RightAssoc | NonAssoc

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
            , PP.text op
                <+> prettyPrec p2 e2
            ]

header :: [Text.Text]
header  =
  [ "{-# LANGUAGE DataKinds, NegativeLiterals #-}"
  , "module Prog where"
  , ""
  , "import           Data.Number.LogFloat (LogFloat)"
  , "import           Prelude hiding (product, exp, log, (**), pi)"
  , "import           Language.Hakaru.Runtime.LogFloatPrelude"
  , "import           Language.Hakaru.Runtime.CmdLine"
  , "import           Language.Hakaru.Types.Sing"
  , "import qualified System.Random.MWC                as MWC"
  , "import           Control.Monad"
  , "import           System.Environment (getArgs)"
  , "" ]

----------------------------------------------------------------
----------------------------------------------------------- fin.
