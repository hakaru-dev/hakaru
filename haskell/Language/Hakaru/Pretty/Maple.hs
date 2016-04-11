{-# LANGUAGE MultiParamTypeClasses
           , OverloadedStrings
           , FlexibleInstances
           , FlexibleContexts
           , ScopedTypeVariables
           , GADTs
           , TypeFamilies
           , DataKinds
           , TypeOperators
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}

module Language.Hakaru.Pretty.Maple (Maple(..), pretty, mapleType) where

import           Data.Number.Nat     (fromNat)
-- import Data.Number.Natural (fromNatural)
import           Data.Sequence (Seq)
import qualified Data.Foldable                   as F
import qualified Data.List.NonEmpty              as L


-- import Language.Hakaru.Types.Coercion
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.IClasses

-- import Control.Monad (liftM, liftM2)
-- import Control.Monad.Trans.State.Strict (State, evalState, state)
import Data.List (intercalate)

import qualified Data.Text as Text
-- import           Data.Number.LogFloat
import           Data.Ratio

newtype Maple (a :: Hakaru) = Maple {unMaple :: String}

pretty :: (ABT Term abt) => abt '[] a -> String
pretty = mapleAST . LC_

app1 :: (ABT Term abt) => String -> abt '[] a -> String
app1 fn x = fn ++ "(" ++ arg x ++ ")"

app2 :: (ABT Term abt) => String -> abt '[] a -> abt '[] b -> String
app2 fn x y = fn ++ "(" ++ arg x ++ ", " ++ arg y ++ ")"

app3 :: (ABT Term abt) =>
        String -> abt '[] a -> abt '[] b -> abt '[] c -> String
app3 fn x y z =
    fn ++ "(" ++ arg x ++ ", " ++ arg y ++ ", " ++ arg z ++ ")"

meq :: (ABT Term abt) => abt '[] a -> abt '[] b -> String
meq x y = arg x ++ "=" ++ arg y

parens :: String -> String
parens a = "(" ++ a ++ ")"

commaSep :: Seq String -> String
commaSep = F.foldr1 (\a b -> a ++ " , " ++ b)

mapleAST :: (ABT Term abt) => LC_ abt a -> String
mapleAST (LC_ e) =
    caseVarSyn e var1 $ \t ->
        case t of
        o :$ es        -> mapleSCon o  es
        NaryOp_ op es  -> mapleNary op es
        Literal_ v     -> mapleLiteral v
        Array_ e1 e2   -> 
            caseBind e2 $ \x e2' ->
                app3 "ary" e1 (var x) e2'
        Datum_ (Datum "true"  _typ (Inl Done)      ) -> "true"
        Datum_ (Datum "false" _typ (Inr (Inl Done))) -> "false"
        Datum_ d       -> mapleDatum d
        Case_  e'  bs  -> "case(" ++ arg e' ++ "," ++
                            "Branches(" ++
                              intercalate ", " (map mapleBranch bs) ++ "))"
        Superpose_ pms ->
            "Msum(" ++ intercalate ", " (map wmtom (L.toList pms)) ++ ")"
        Reject_ _      -> "Msum()"

uniqID :: Variable (a :: Hakaru) -> String
uniqID = show . fromNat . varID

var1 :: Variable (a :: Hakaru) -> String
var1 x | Text.null (varHint x) = 'x' : uniqID x 
       | otherwise = Text.unpack (varHint x)

list1vars :: List1 Variable (vars :: [Hakaru]) -> [String]
list1vars Nil1         = []
list1vars (Cons1 x xs) = var1 x : list1vars xs

mapleSCon :: (ABT Term abt) => SCon args a -> SArgs abt args -> String
mapleSCon Lam_     (e1 :* End)       =
    caseBind e1 $ \x e1' ->
        "lam(" ++ (var1 x)                  ++ ", " ++
                  (mapleType . varType $ x) ++ ", " ++
                   arg e1'                  ++ ")"
mapleSCon App_     (e1 :* e2 :* End) = app2 "app" e1 e2
mapleSCon Let_     (e1 :* e2 :* End) =
    caseBind e2 $ \x e2' ->
        "eval(" ++ arg e2' ++ ", " ++  (var x `meq` e1) ++ ")"
mapleSCon (CoerceTo_   _) (e :* End) = arg e
mapleSCon (UnsafeFrom_ _) (e :* End) = arg e
mapleSCon (PrimOp_    o) es          = maplePrimOp o es
mapleSCon (ArrayOp_   o) es          = mapleArrayOp o es
mapleSCon (MeasureOp_ o) es          = mapleMeasureOp o es
mapleSCon Dirac (e1 :* End)          = app1 "Ret" e1
mapleSCon MBind (e1 :* e2 :* End)    =
    caseBind e2 $ \x e2' ->
        app3 "Bind"  e1 (var x) e2'
mapleSCon Plate (e1 :* e2 :* End)    =
    caseBind e2 $ \x e2' ->
        app3 "Plate" e1 (var x) e2'
mapleSCon Integrate (e1 :* e2 :* e3 :* End) =
    caseBind e3 $ \x e3' ->
        "int(" ++ arg e3' ++ ", ["
               ++ var1 x  ++ "="
               ++ arg e1  ++ ".." 
               ++ arg e2  ++ "])" 

mapleNary :: (ABT Term abt) => NaryOp a -> Seq (abt '[] a) -> String
mapleNary And      es = "And" ++ (parens . commaSep $ fmap arg es)
mapleNary (Sum  _) es = parens $ F.foldr1 (\a b -> a ++ " + " ++ b)
                                 (fmap arg es)
mapleNary (Prod _) es = parens $ F.foldr1 (\a b -> a ++ " * " ++ b)
                                 (fmap arg es)
mapleNary (Min _)  es = "min" ++ (parens . commaSep $ fmap arg es)
mapleNary (Max _)  es = "max" ++ (parens . commaSep $ fmap arg es)
mapleNary _        _  = "TODO: mapleNary:"

mapleDatum :: (ABT Term abt)
           => Datum (abt '[]) t -> String
mapleDatum (Datum hint _ d) = "Datum(" ++ Text.unpack hint
                                       ++ ", " ++ mapleDatumCode d
                                       ++ ")"
mapleDatumCode :: (ABT Term abt)
               => DatumCode xss (abt '[]) a -> String
mapleDatumCode (Inr d) = "Inr(" ++ mapleDatumCode   d ++ ")"
mapleDatumCode (Inl d) = "Inl(" ++ mapleDatumStruct d ++ ")"

mapleDatumStruct :: (ABT Term abt)
                 => DatumStruct xs (abt '[]) a -> String
mapleDatumStruct (Et d1 d2) = "Et(" ++ mapleDatumFun d1 ++ ", "
                                    ++ mapleDatumStruct d2 ++ ")"
mapleDatumStruct Done       = "Done"

mapleDatumFun :: (ABT Term abt)
              => DatumFun x (abt '[]) a -> String
mapleDatumFun (Konst a) = app1 "Konst" a
mapleDatumFun (Ident a) = app1 "Ident" a

mapleBranch :: (ABT Term abt) => Branch a abt b -> String
mapleBranch (Branch pat e) = let (vars, e') = caseBinds e
                                 (v', _) = maplePattern (list1vars vars) pat
                             in "Branch(" ++ v' ++
                                      "," ++ arg e' ++ ")"

maplePattern :: [String] -> Pattern xs a -> (String, [String])
maplePattern vs     PWild = ("PWild", vs)
maplePattern (v:vs) PVar  = ("PVar(" ++ v ++ ")", vs)
maplePattern vars (PDatum hint d) = let (v', res) = maplePDatumCode vars d
                                    in ("PDatum(" ++ Text.unpack hint ++
                                        "," ++ v'  ++ ")", res)

maplePDatumCode :: [String] -> PDatumCode xss vars a -> (String, [String])
maplePDatumCode vars (PInr x) = let (v', res) = maplePDatumCode vars x
                                in ("PInr(" ++ v' ++ ")", res)
maplePDatumCode vars (PInl x) = let (v', res) = maplePDatumStruct vars x
                                in ("PInl(" ++ v' ++ ")", res)

maplePDatumStruct :: [String] -> PDatumStruct xs vars a -> (String, [String])
maplePDatumStruct vars (PEt x y) = let (v',  res)  = maplePDatumFun vars x
                                       (v'', res') = maplePDatumStruct res y
                                   in ("PEt(" ++ v' ++ "," ++ v'' ++ ")", res')
maplePDatumStruct vars PDone     = ("PDone", vars)

maplePDatumFun :: [String] -> PDatumFun x vars a -> (String, [String])
maplePDatumFun vars (PKonst pat) = let (v, res) = maplePattern vars pat
                                   in ("PKonst(" ++ v ++ ")", res)
maplePDatumFun vars (PIdent pat) = let (v, res) = maplePattern vars pat
                                   in ("PIdent(" ++ v ++ ")", res)

arg :: (ABT Term abt) => abt '[] a -> String
arg = mapleAST . LC_

wmtom :: (ABT Term abt) => (abt '[] 'HProb, abt '[] ('HMeasure a)) -> String
wmtom (w, m) = app2 "Weight" w m

maplePrimOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => PrimOp typs a -> SArgs abt args -> String
maplePrimOp Pi               End               = "Pi"
maplePrimOp Cos              (e1 :* End)       = app1 "cos" e1
maplePrimOp RealPow          (e1 :* e2 :* End) =
    parens (arg e1 ++ " ^ " ++ arg e2)
maplePrimOp Exp              (e1 :* End)       = app1 "exp"  e1
maplePrimOp Log              (e1 :* End)       = app1 "log"  e1
maplePrimOp Infinity         End               = "infinity"
maplePrimOp NegativeInfinity End               = "-infinity"
maplePrimOp GammaFunc        (e1 :* End)       = app1 "GAMMA" e1
maplePrimOp BetaFunc         (e1 :* e2 :* End) = app2 "Beta" e1 e2
maplePrimOp (Equal _)        (e1 :* e2 :* End) = parens $ arg e1 ++ " = " ++ arg e2
maplePrimOp (Less _)         (e1 :* e2 :* End) = arg e1 ++ " < " ++ arg e2
maplePrimOp (NatPow _)       (e1 :* e2 :* End) =
    parens (arg e1 ++ " ^ " ++ arg e2)
maplePrimOp (Negate _)       (e1 :* End)       =
    parens (app1 "-" e1)
maplePrimOp (Recip   _)      (e1 :* End)       =
    app1 "1/"   e1
maplePrimOp (NatRoot _)      (e1 :* e2 :* End) =
    app2 "root" e1 e2
maplePrimOp x                _                 =
    error ("maplePrimOp: TODO: " ++ show x)

mapleArrayOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => ArrayOp typs a -> SArgs abt args -> String
mapleArrayOp (Index _) (e1 :* e2 :* End) = app2 "idx" e1 e2
mapleArrayOp (Size  _) (e1 :* End)       = app1 "size" e1
mapleArrayOp _         _                 = error "mapleArrayOp: TODO: Reduce"

mapleMeasureOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => MeasureOp typs a -> SArgs abt args -> String
mapleMeasureOp Lebesgue End               = "Lebesgue()"
mapleMeasureOp Counting End               = "Counting()"
mapleMeasureOp Uniform  (e1 :* e2 :* End) = app2 "Uniform"  e1 e2
mapleMeasureOp Normal   (e1 :* e2 :* End) = app2 "Gaussian" e1 e2
mapleMeasureOp Poisson  (e1 :* End)       = app1 "PoissonD" e1
mapleMeasureOp Gamma    (e1 :* e2 :* End) = app2 "GammaD"   e1 e2
mapleMeasureOp Beta     (e1 :* e2 :* End) = app2 "BetaD"    e1 e2

mapleType :: Sing (a :: Hakaru) -> String
mapleType SNat         = "HInt(Bound(`>=`,0))"
mapleType SInt         = "HInt()"
mapleType SProb        = "HReal(Bound(`>=`,0))"
mapleType SReal        = "HReal()"
mapleType (SFun a b)   = "HFunction(" ++ mapleType a ++ "," ++ mapleType b ++ ")"
mapleType (SArray a)   = "HArray("    ++ mapleType a ++ ")"
mapleType (SMeasure a) = "HMeasure("  ++ mapleType a ++ ")"
-- Special case pair
mapleType (SData _ (SPlus x SVoid))
    = "HData(DatumStruct(pair," ++ mapleTypeDStruct x ++ "))"
-- Special case bool
mapleType (SData _ (SPlus SDone (SPlus SDone SVoid)))
    = "HData(DatumStruct(true,[]),DatumStruct(false,[]))"
mapleType x = error ("TODO: mapleType" ++ show x)

mapleTypeDStruct :: Sing (a :: [HakaruFun]) -> String
mapleTypeDStruct SDone      = "[]"
mapleTypeDStruct (SEt x xs) = "[" ++ mapleTypeDFun x ++ ", op("
                                  ++ mapleTypeDStruct xs
                                  ++ ")]"

mapleTypeDFun :: Sing (a :: HakaruFun) -> String
mapleTypeDFun (SKonst a) = "Konst(" ++ mapleType a ++ ")"
mapleTypeDFun SIdent     = "Ident"

mapleLiteral :: Literal a -> String
mapleLiteral (LNat  v) = show v
mapleLiteral (LInt  v) = show v
mapleLiteral (LProb v) = showRational v
mapleLiteral (LReal v) = showRational v

showRational :: (Integral a, Show a) => Ratio a -> String
showRational a =
    "("++ show (numerator a) ++ "/" ++ show (denominator a) ++ ")"
