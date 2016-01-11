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

module Language.Hakaru.Pretty.Maple (Maple(..), runMaple) where

import Data.Number.Nat     (fromNat)
-- import Data.Number.Natural (fromNatural)
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

runMaple :: (ABT Term abt) => abt '[] a -> String
runMaple = mapleAST . LC_

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

mapleAST :: (ABT Term abt) => LC_ abt a -> String
mapleAST (LC_ e) =
    caseVarSyn e var1 $ \t ->
        case t of
        o :$ es        -> mapleSCon o es
        Literal_ v     -> mapleLiteral v
        -- Special case pair
        Datum_ (Datum "pair" (Inl (Et (Konst a) (Et (Konst b) Done)))) ->
            app2 "Pair" a b
        Datum_ (Datum "true" (Inl Done)) -> "True"
        Datum_ d       -> error "TODO: Add mapleAST{Datum}"
        Superpose_ pms ->
            "Msum(" ++ intercalate ", " (map wmtom pms) ++ ")"

uniqID :: Variable (a :: Hakaru) -> String
uniqID = show . fromNat . varID

var1 :: Variable (a :: Hakaru) -> String
var1 x | Text.null (varHint x) = 'x' : uniqID x 
       | otherwise = Text.unpack (varHint x) ++ uniqID x 

mapleSCon :: (ABT Term abt) => SCon args a -> SArgs abt args -> String
mapleSCon Let_     (e1 :* e2 :* End) =
    caseBind e2 $ \x e2' ->
        "eval(" ++ arg e2' ++ ", " ++  (var x `meq` e1) ++ ")"
mapleSCon (CoerceTo_   _) (e :* End) = mapleAST (LC_ e)
mapleSCon (UnsafeFrom_ _) (e :* End) = mapleAST (LC_ e)
mapleSCon (Ann_ a)        (e :* End) = "Ann("  ++ mapleType a ++ "," ++ arg e ++ ")"
mapleSCon (MeasureOp_ o) es          = mapleMeasureOp o es
mapleSCon Dirac (e1 :* End)          = app1 "Ret" e1
mapleSCon MBind (e1 :* e2 :* End)    =
    caseBind e2 $ \x e2' ->
        app3 "Bind" e1 (var x) e2'

arg :: (ABT Term abt) => abt '[] a -> String
arg = mapleAST . LC_

wmtom :: (ABT Term abt) => (abt '[] 'HProb, abt '[] ('HMeasure a)) -> String
wmtom (w, m) = app2 "Weight" w m

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
