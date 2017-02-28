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
module Language.Hakaru.Pretty.Full where

import System.IO (stderr)
import Data.Text (Text)
import           Data.Sequence       (Seq)

import Data.Text as Text
import Data.Number.Nat (fromNat)
import Data.Text.IO as IO
import Language.Hakaru.Command (parseAndInfer)
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.AST.Transforms
import Language.Hakaru.Syntax.TypeCheck
import Language.Hakaru.Syntax.TypeOf
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Types.Sing
import Text.PrettyPrint (Doc, (<>), (<+>))
import Text.PrettyPrint as PP

pretty :: (ABT Term abt) => abt '[] a -> Doc
pretty a = PP.brackets  (caseVarSyn a prettyVariable prettyTerm <+> PP.colon <+> prettyType (typeOf a))

prettyTerm :: (ABT Term abt) => Term abt a -> Doc
prettyTerm (o :$ es) = PP.parens $ prettySCons o es
prettyTerm (NaryOp_ op es) = PP.parens $ prettyNary op es
prettyTerm (Literal_ v) = prettyLiteral v
prettyTerm (Array_ e1 e2) = PP.parens $ (PP.text "array") <+>
                            (caseBind e2 $ \x e2' ->
                                             PP.parens (prettyVariable x <+> pretty e1) <+>
                                             pretty e2')
prettyTerm (Case_ e1 bs) = PP.parens $ PP.text "match" <+> pretty e1 <+> 
                           Prelude.foldl (<+>) PP.empty (prettyBranch <$> bs)
prettyTerm x = PP.text "TODO"

prettyBranch :: (ABT Term abt) => Branch a abt b -> Doc
prettyBranch (Branch (PDatum hint _) e) = PP.parens $ (PP.text . Text.unpack $ hint) <+>
                                          (prettyView . viewABT $ e)

prettyView :: (ABT Term abt) => View (Term abt) xs a -> Doc
prettyView (Bind x v) = PP.text "bindTODO"
prettyView (Var x) = PP.text "varTODO"
prettyView (Syn t) = pretty (syn t)
prettyView _ = PP.text "TODO"

prettyLiteral :: Literal a -> Doc
prettyLiteral (LNat v) = PP.text .show $ v

prettyVariable :: Variable (a :: Hakaru) -> Doc
prettyVariable x | Text.null (varHint x) = PP.text "_" <> (PP.int . fromNat .varID) x
                 | otherwise = (PP.text . Text.unpack . varHint) x

prettySCons :: (ABT Term abt) => SCon args a -> SArgs abt args -> Doc
prettySCons Lam_ (e1 :* End) = caseBind e1 $ \x e1' ->
  PP.text "fn" <+> prettyVariable x  <+> (prettyType $ typeOf e1')
  <+> pretty e1'
prettySCons (PrimOp_ o) es = prettyPrimOp o es
prettySCons (ArrayOp_ o) es = prettyArrayOp o es
prettySCons (CoerceTo_ o) (e1 :* End) = PP.text (pCoerce o) <+> pretty e1
prettySCons (Summate _ _) (e1 :* e2 :* e3 :* End) =
  caseBind e3 $ \x e3' -> PP.text "summate" <+>
                          PP.parens (prettyVariable x <+> pretty e1 <+> pretty e2) <+>
                          pretty e3' 
prettySCons (Product _ _) (e1 :* e2 :* e3 :* End) =
  caseBind e3 $ \x e3' -> PP.text "product" <+>
                          PP.parens (prettyVariable x <+> pretty e1 <+> pretty e2) <+>
                          pretty e3'
-- prettySCons App_ (e1 :* e2 :* End) = PP.text "app TODO"
-- prettySCons Let_ (e1 :* e2 :* End) = PP.text "let TODO"
-- prettySCons (UnsafeFrom_ o) es = PP.empty
-- prettySCons (MeasureOp_ o) es = PP.empty
-- prettySCons Dirac es = PP.empty
-- prettySCons MBind es = PP.empty
-- prettySCons Plate es = PP.empty
-- prettySCons Chain es = PP.empty
-- prettySCons Integrate es = PP.empty
-- prettySCons Expect es = PP.empty
-- prettySCons Observe es = PP.empty

pCoerce :: Coercion a b -> String
pCoerce (CCons (Signed HRing_Real) CNil)           = "prob2real"
pCoerce (CCons (Signed HRing_Int)  CNil)           = "nat2int"
pCoerce (CCons (Continuous HContinuous_Real) CNil) = "int2real"
pCoerce (CCons (Continuous HContinuous_Prob) CNil) = "nat2prob"
pCoerce (CCons (Continuous HContinuous_Prob)
         (CCons (Signed HRing_Real) CNil))                 = "nat2real"
pCoerce (CCons (Signed HRing_Int)
         (CCons (Continuous HContinuous_Real) CNil))       = "nat2real"
  

prettyNary :: (ABT Term abt) => NaryOp a -> Seq (abt '[] a) -> Doc
prettyNary And      es = PP.text "and" <+> foldMap pretty es
prettyNary Or      es = PP.text "or" <+> foldMap pretty es
prettyNary Xor      es = PP.text "xor" <+> foldMap pretty es
prettyNary (Sum  _) es = PP.text "+" <+> foldMap pretty es
prettyNary (Prod  _) es = PP.text "*" <+> foldMap pretty es
prettyNary (Min  _) es = PP.text "min" <+> foldMap pretty es
prettyNary (Max  _) es = PP.text "max" <+> foldMap pretty es

prettyType :: Sing (a :: Hakaru) -> Doc
prettyType SNat = PP.text "nat"
prettyType SInt = PP.text "int"
prettyType SProb = PP.text "prob"
prettyType SReal = PP.text "real"
prettyType (SArray a) = PP.parens $ PP.text "array" <+> prettyType a
prettyType (SMeasure a) = PP.parens $ PP.text "measure" <+> prettyType a
prettyType (SFun a b) = PP.parens $ prettyType a <+> PP.text "->" <+> prettyType b
prettyType (SData _ _) = PP.text "data-type"


prettyPrimOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => PrimOp typs a -> SArgs abt args -> Doc
prettyPrimOp Not              (e1 :* End)       = PP.text "not" <+> pretty e1
prettyPrimOp Pi               End               = PP.text "pi"
prettyPrimOp Cos              (e1 :* End)       = PP.text "cos" <+> pretty e1
prettyPrimOp RealPow          (e1 :* e2 :* End) = PP.text "realpow" <+> pretty e1 <+> pretty e2
prettyPrimOp Exp              (e1 :* End)       = PP.text "exp"  <+> pretty e1
prettyPrimOp Log              (e1 :* End)       = PP.text "log"  <+> pretty e1
prettyPrimOp (Infinity  _)    End               = PP.text "infinity"
prettyPrimOp GammaFunc        (e1 :* End)       = PP.text "gamma" <+> pretty e1
prettyPrimOp BetaFunc         (e1 :* e2 :* End) = PP.text "beta" <+> pretty e1 <+> pretty e2
prettyPrimOp (Equal _)        (e1 :* e2 :* End) = PP.text "==" <+> pretty e1 <+> pretty e2
prettyPrimOp (Less _)         (e1 :* e2 :* End) = PP.text "<" <+> pretty e1 <+> pretty e2
prettyPrimOp (NatPow _)       (e1 :* e2 :* End) = PP.text "natpow" <+> pretty e1 <+> pretty e2
prettyPrimOp (Negate _)       (e1 :* End)       = PP.text "negate" <+> pretty e1
prettyPrimOp (Abs _)          (e1 :* End)       = PP.text "abs"  <+> pretty e1
prettyPrimOp (Recip   _)      (e1 :* End)       = PP.text "recip" <+> pretty e1
prettyPrimOp (NatRoot _)      (e1 :* e2 :* End) = PP.text "root" <+> pretty e1 <+> pretty e2
prettyPrimOp x                _                 =
    error $ "TODO: prettyPrimOp{" ++ show x ++ "}"

prettyArrayOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => ArrayOp typs a -> SArgs abt args -> Doc
prettyArrayOp (Index _) (e1 :* e2 :* End) = PP.text "index" <+> pretty e1 <+> pretty e2
prettyArrayOp (Size  _) (e1 :* End)       = PP.text "size" <+> pretty e1
prettyArrayOp _         _                 = error "TODO: prettyArrayOp{Reduce}"

prettyFile :: [Char] -> IO ()
prettyFile fname = do
  fileText <- IO.readFile fname
  runPretty fileText

runPretty :: Text -> IO ()
runPretty prog =
    case parseAndInfer prog of
    Left  err              -> IO.hPutStrLn stderr err
    Right (TypedAST _ ast) -> print . pretty . expandTransformations $ ast
