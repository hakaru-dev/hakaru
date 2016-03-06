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

module Language.Hakaru.Pretty.Maple (Maple(..), pretty) where

import           Data.Number.Nat     (fromNat)
-- import Data.Number.Natural (fromNatural)
import           Data.Sequence (Seq)
import qualified Data.Foldable                   as F

-- import Language.Hakaru.Types.Coercion
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.ABT

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

mapleAST :: (ABT Term abt) => LC_ abt a -> String
mapleAST (LC_ e) =
    caseVarSyn e var1 $ \t ->
        case t of
        o :$ es        -> mapleSCon o  es
        NaryOp_ op es  -> mapleNary op es
        Literal_ v     -> mapleLiteral v
        -- Special case pair
        Datum_ (Datum "pair" _typ (Inl (Et (Konst a) (Et (Konst b) Done)))) ->
            app2 "Pair" a b
        Datum_ (Datum "true" _typ (Inl Done)) -> "True"
        Datum_ d       -> error "TODO: Add mapleAST{Datum}"
        Case_ e bs     -> "Case(" ++ arg e ++ "," ++
                            "Branches(" ++
                              intercalate ", " (map mapleBranch bs) ++ "))"
        Superpose_ pms ->
            "Msum(" ++ intercalate ", " (map wmtom pms) ++ ")"

uniqID :: Variable (a :: Hakaru) -> String
uniqID = show . fromNat . varID

var1 :: Variable (a :: Hakaru) -> String
var1 x | Text.null (varHint x) = 'x' : uniqID x 
       | otherwise = Text.unpack (varHint x)

mapleSCon :: (ABT Term abt) => SCon args a -> SArgs abt args -> String
mapleSCon Let_     (e1 :* e2 :* End) =
    caseBind e2 $ \x e2' ->
        "eval(" ++ arg e2' ++ ", " ++  (var x `meq` e1) ++ ")"
mapleSCon (CoerceTo_   _) (e :* End) = mapleAST (LC_ e)
mapleSCon (UnsafeFrom_ _) (e :* End) = mapleAST (LC_ e)
mapleSCon (PrimOp_    o) es          = maplePrimOp o es
mapleSCon (MeasureOp_ o) es          = mapleMeasureOp o es
mapleSCon Dirac (e1 :* End)          = app1 "Ret" e1
mapleSCon MBind (e1 :* e2 :* End)    =
    caseBind e2 $ \x e2' ->
        app3 "Bind" e1 (var x) e2'

mapleNary :: (ABT Term abt) => NaryOp a -> Seq (abt '[] a) -> String
mapleNary (Sum  _) es = F.foldr1 (\a b -> a ++ " + " ++ b)
                        (fmap arg es)
mapleNary (Prod _) es = F.foldr1 (\a b -> a ++ " * " ++ b)
                        (fmap arg es)
mapleNary _        _  = "TODO: mapleNary:"

mapleBranch :: (ABT Term abt) => Branch a abt b -> String
mapleBranch (Branch pat e) = "Branch(" ++ maplePattern pat ++
                              "," ++ (arg . snd . caseBinds $ e) ++ ")"

maplePattern :: Pattern xs a -> String
maplePattern PWild = "PWild"
maplePattern PVar  = "PVar"
maplePattern (PDatum hint d) = "PDatum(" ++ Text.unpack hint ++
                               "," ++ maplePDatumCode d ++ ")"

maplePDatumCode :: PDatumCode xss vars a -> String
maplePDatumCode (PInr x) = "PInr(" ++ maplePDatumCode x ++ ")"
maplePDatumCode (PInl x) = "PInl(" ++ maplePDatumStruct x ++ ")"

maplePDatumStruct :: PDatumStruct xs vars a -> String
maplePDatumStruct (PEt x y) = "PEt(" ++ maplePDatumFun x ++ ","
                              ++ maplePDatumStruct y ++ ")"
maplePDatumStruct PDone     = "PDone"

maplePDatumFun :: PDatumFun x vars a -> String
maplePDatumFun (PKonst pat) = "PKonst(" ++ maplePattern pat ++ ")"
maplePDatumFun (PIdent pat) = "PIdent(" ++ maplePattern pat ++ ")"

arg :: (ABT Term abt) => abt '[] a -> String
arg = mapleAST . LC_

wmtom :: (ABT Term abt) => (abt '[] 'HProb, abt '[] ('HMeasure a)) -> String
wmtom (w, m) = app2 "Weight" w m

maplePrimOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => PrimOp typs a -> SArgs abt args -> String
maplePrimOp Pi          End               = "Pi"
maplePrimOp Exp         (e1 :* End)       = 
    app1 "exp"  e1
maplePrimOp (NatPow _)  (e1 :* e2 :* End) =
    arg e1 ++ " ^ " ++ arg e2
maplePrimOp (Negate _)  (e1 :* End)       =
    parens (app1 "-" e1)
maplePrimOp (Recip   _) (e1 :* End)       =
    app1 "1/"   e1
maplePrimOp (NatRoot _) (e1 :* e2 :* End) =
    app2 "root" e1 e2
maplePrimOp x   _                         =
    error ("maplePrimOp: TODO: " ++ show x)

mapleMeasureOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => MeasureOp typs a -> SArgs abt args -> String
mapleMeasureOp Lebesgue End               = "Lebesgue()"
mapleMeasureOp Counting End               = "Counting()"
mapleMeasureOp Uniform  (e1 :* e2 :* End) = app2 "Uniform"  e1 e2
mapleMeasureOp Normal   (e1 :* e2 :* End) = app2 "Gaussian" e1 e2
mapleMeasureOp Gamma    (e1 :* e2 :* End) = app2 "GammaD"   e1 e2
mapleMeasureOp Beta     (e1 :* e2 :* End) = app2 "BetaD"    e1 e2

mapleType :: Sing (a :: Hakaru) -> String
mapleType SNat         = "Nat"
mapleType SInt         = "Int"
mapleType SProb        = "Prob"
mapleType SReal        = "Real"
mapleType (SFun a b)   = "Arrow(" ++ mapleType a ++ "," ++ mapleType b ++ ")"
mapleType (SArray a)   = "Array(" ++ mapleType a ++ ")"
mapleType (SMeasure a) = "Measure(" ++ mapleType a ++ ")"
-- Special case pair
mapleType (SData _ (SPlus (SEt (SKonst a)
                           (SEt (SKonst b)
                            SDone))
                    SVoid))
    = "Pair(" ++ mapleType a ++ "," ++ mapleType b ++ ")"
-- Special case bool
mapleType (SData _ (SPlus SDone (SPlus SDone SVoid)))
    = "Bool"

mapleLiteral :: Literal a -> String
mapleLiteral (LNat  v) = show v
mapleLiteral (LInt  v) = show v
mapleLiteral (LProb v) = showRational v
mapleLiteral (LReal v) = showRational v

showRational :: (Integral a, Show a) => Ratio a -> String
showRational a =
    "("++ show (numerator a) ++ "/" ++ show (denominator a) ++ ")"
