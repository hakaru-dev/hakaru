{-# LANGUAGE MultiParamTypeClasses
           , OverloadedStrings
           , FlexibleInstances
           , FlexibleContexts
           , ScopedTypeVariables
           , CPP
           , GADTs
           , TypeFamilies
           , DataKinds
           , TypeOperators
           #-}


{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.04.28
-- |
-- Module      :  Language.Hakaru.Pretty.Maple
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- TODO: given as the constructed strings will just be printed,
-- it'd reduce memory pressure a lot to replace our use of 'ShowS'
-- with a similar builder type for 'Text.Text' (or, if the character
-- encoding is fixed\/known, a builder type for @ByteString@).
----------------------------------------------------------------
module Language.Hakaru.Pretty.Maple (pretty, mapleType) where

import qualified Data.Text           as Text
import           Data.Ratio
import           Data.Number.Nat     (fromNat)
import           Data.Sequence       (Seq)
import qualified Data.Foldable       as F
import qualified Data.List.NonEmpty  as L
import           Control.Monad.State (MonadState(..), State, runState)
import           Data.Maybe          (isJust)

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..), (<$>))
#endif

import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Expect
----------------------------------------------------------------

pretty :: (ABT Term abt) => abt '[] a -> String
pretty = ($[]) . mapleAST . LC_

app1 :: (ABT Term abt) => String -> abt '[] a -> ShowS
app1 fn x = op1 fn (arg x)
{-# INLINE app1 #-}

app2 :: (ABT Term abt) => String -> abt '[] a -> abt '[] b -> ShowS
app2 fn x y = op2 fn (arg x) (arg y)
{-# INLINE app2 #-}

app3 :: (ABT Term abt)
    => String -> abt '[] a -> abt '[] b -> abt '[] c -> ShowS
app3 fn x y z = op3 fn (arg x) (arg y) (arg z)
{-# INLINE app3 #-}

appN :: (ABT Term abt, Functor f, F.Foldable f)
    => String -> f (abt '[] a) -> ShowS
appN fn xs = opN fn (arg <$> xs)
{-# INLINE appN #-}

op1 ::  String -> ShowS -> ShowS
op1 fn x = showString fn . parens x
{-# INLINE op1 #-}

op2 :: String -> ShowS -> ShowS -> ShowS
op2 fn x y = showString fn . parens (x . showString ", " . y)
{-# INLINE op2 #-}

op3 :: String -> ShowS -> ShowS -> ShowS -> ShowS
op3 fn x y z
    = showString fn
    . parens
        ( x
        . showString ", "
        . y
        . showString ", "
        . z
        )
{-# INLINE op3 #-}

opN :: F.Foldable f => String -> f ShowS -> ShowS
opN fn xs = showString fn . parens (commaSep xs)
{-# INLINE opN #-}

meq :: (ABT Term abt) => abt '[] a -> abt '[] b -> ShowS
meq x y = arg x . showChar '=' . parens (arg y)
{-# INLINE meq #-}

parens :: ShowS -> ShowS
parens a = showChar '(' . a . showChar ')'
{-# INLINE parens #-}

brackets :: ShowS -> ShowS
brackets a = showChar '[' . a . showChar ']'
{-# INLINE brackets #-}

intercalate :: F.Foldable f => ShowS -> f ShowS -> ShowS
intercalate sep = F.foldr1 (\a b -> a . sep . b)
{-# INLINE intercalate #-}

commaSep :: F.Foldable f => f ShowS -> ShowS
commaSep = intercalate (showString ", ")
{-# INLINE commaSep #-}

mapleAST :: (ABT Term abt) => LC_ abt a -> ShowS
mapleAST (LC_ e) =
    caseVarSyn e var1 $ \t ->
        case t of
        o :$ es          -> mapleSCon o  es
        NaryOp_ op es    -> mapleNary op es
        Literal_ v       -> mapleLiteral v
        Empty_ _         -> brackets id
        Array_ e1 e2     ->
            caseBind e2 $ \x e2' ->
                app3 "ary" e1 (var x) e2'
        ArrayLiteral_ es -> brackets (commaSep (fmap arg es))
        Datum_ (Datum "true"  _typ (Inl Done)      ) -> showString "true"
        Datum_ (Datum "false" _typ (Inr (Inl Done))) -> showString "false"
        Datum_ d         -> mapleDatum d
        Case_  e'  bs    ->
            op2 "case" (arg e') (opN "Branches" (mapleBranch <$> bs))
        Superpose_ pms   ->
            opN "Msum" (uncurry (app2 "Weight") <$> L.toList pms)
        Reject_ _        -> showString "Msum()"


mapleLiteral :: Literal a -> ShowS
mapleLiteral (LNat  v) = shows v
mapleLiteral (LInt  v) = parens (shows v)
mapleLiteral (LProb v) = showsRational v
mapleLiteral (LReal v) = showsRational v

showsRational :: (Integral a, Show a) => Ratio a -> ShowS
showsRational a =
    parens
        ( shows (numerator a)
        . showChar '/'
        . shows (denominator a)
        )


var1 :: Variable (a :: Hakaru) -> ShowS
var1 x | Text.null (varHint x) = showChar 'x' . (shows . fromNat . varID) x
       | otherwise             = quoteName . Text.unpack . varHint $ x

quoteName :: String -> ShowS
quoteName s =
  foldr1 (.) $ map showString
    ["`", concatMap quoteChar s, "`"]
      where quoteChar '`'  = "\\`"
            quoteChar '\\' = "\\\\"
            quoteChar c    = [c]

list1vars :: List1 Variable (vars :: [Hakaru]) -> [String]
list1vars Nil1         = []
list1vars (Cons1 x xs) = var1 x [] : list1vars xs

mapleSCon :: (ABT Term abt) => SCon args a -> SArgs abt args -> ShowS
mapleSCon Lam_ = \(e1 :* End) ->
    caseBind e1 $ \x e1' ->
        op3 "lam" (var1 x) (mapleType $ varType x) (arg e1')
mapleSCon App_ = \(e1 :* e2 :* End) -> app2 "app" e1 e2
mapleSCon Let_ = \(e1 :* e2 :* End) ->
    caseBind e2 $ \x e2' ->
        op2 "eval" (arg e2') (var x `meq` e1)
mapleSCon (CoerceTo_   _) = \(e :* End) -> arg e
mapleSCon (UnsafeFrom_ _) = \(e :* End) -> arg e
mapleSCon (PrimOp_    o) = \es          -> maplePrimOp    o es
mapleSCon (ArrayOp_   o) = \es          -> mapleArrayOp   o es
mapleSCon (MeasureOp_ o) = \es          -> mapleMeasureOp o es
mapleSCon Dirac          = \(e1 :* End) -> app1 "Ret" e1
mapleSCon MBind          = \(e1 :* e2 :* End) ->
    caseBind e2 $ \x e2' ->
        app3 "Bind"  e1 (var x) e2'
mapleSCon Plate = \(e1 :* e2 :* End) ->
    caseBind e2 $ \x e2' ->
        app3 "Plate" e1 (var x) e2'
mapleSCon Chain = \(e1 :* e2 :* e3 :* End) ->
    error "TODO: mapleSCon{Chain}"
mapleSCon Integrate = \(e1 :* e2 :* e3 :* End) ->
    caseBind e3 $ \x e3' ->
        showString "Int("
        . arg e3'
        . showString ", ["
        . var1 x
        . showChar '='
        . arg e1
        . showString ".."
        . arg e2
        . showString "])"
mapleSCon (Summate _ _) = \(e1 :* e2 :* e3 :* End) ->
    caseBind e3 $ \x e3' ->
        showString "Sum("
        . arg e3'
        . showString ", "
        . var1 x
        . showChar '='
        . arg e1
        . showString "..("
        . arg e2
        . showString ")-1)"
mapleSCon (Product _ _) = \(e1 :* e2 :* e3 :* End) ->
    caseBind e3 $ \x e3' ->
        showString "Product("
        . arg e3'
        . showString ", "
        . var1 x
        . showChar '='
        . arg e1
        . showString "..("
        . arg e2
        . showString ")-1)"

mapleSCon (Transform_ t) = \_ -> error $
    concat [ "mapleSCon{", show t, "}"
           , ": Maple doesn't recognize transforms; expand them first" ]


mapleNary :: (ABT Term abt) => NaryOp a -> Seq (abt '[] a) -> ShowS
mapleNary And      = appN "And"
mapleNary Or       = appN "Or"
mapleNary (Sum  _) = parens . intercalate (showString " + ") . fmap arg
mapleNary (Prod _) = parens . intercalate (showString " * ") . fmap arg
mapleNary (Min _)  = appN "min"
mapleNary (Max _)  = appN "max"
mapleNary op       = error $ "TODO: mapleNary{" ++ show op ++ "}"


mapleDatum :: (ABT Term abt) => Datum (abt '[]) t -> ShowS
mapleDatum (Datum hint _ d) =
    op2 "Datum"
        (showString (Text.unpack hint))
        (mapleDatumCode d)

mapleDatumCode :: (ABT Term abt) => DatumCode xss (abt '[]) a -> ShowS
mapleDatumCode (Inr d) = op1 "Inr" (mapleDatumCode   d)
mapleDatumCode (Inl d) = op1 "Inl" (mapleDatumStruct d)

mapleDatumStruct :: (ABT Term abt) => DatumStruct xs (abt '[]) a -> ShowS
mapleDatumStruct Done       = showString "Done"
mapleDatumStruct (Et d1 d2) =
    op2 "Et" (mapleDatumFun d1) (mapleDatumStruct d2)

mapleDatumFun :: (ABT Term abt) => DatumFun x (abt '[]) a -> ShowS
mapleDatumFun (Konst a) = app1 "Konst" a
mapleDatumFun (Ident a) = app1 "Ident" a


-- TODO: if we really wanted we could create an indexed variant of
-- 'State' to keep track of the length of the list of variables,
-- to guarantee the two error cases can never occur.
mapleBranch :: (ABT Term abt) => Branch a abt b -> ShowS
mapleBranch (Branch pat e) =
    let (vars, e')    = caseBinds e
        (pat', vars') = runState (maplePattern pat) (list1vars vars)
    in
    case vars' of
    _:_ -> error "mapleBranch: didn't use all the variable names"
    []  -> op2 "Branch" pat' (arg e')

maplePattern :: Pattern xs a -> State [String] ShowS
maplePattern PWild = return $ showString "PWild"
maplePattern PVar  = do
    vs <- get
    case vs of
        []    -> error "maplePattern: ran out of variable names"
        v:vs' -> do
            put vs'
            return $ op1 "PVar" (showString v)
maplePattern (PDatum hint pat) =
    op2 "PDatum" (showString $ Text.unpack hint) <$> maplePDatumCode pat

maplePDatumCode :: PDatumCode xss vars a -> State [String] ShowS
maplePDatumCode (PInr pat) = op1 "PInr" <$> maplePDatumCode pat
maplePDatumCode (PInl pat) = op1 "PInl" <$> maplePDatumStruct pat

maplePDatumStruct :: PDatumStruct xs vars a -> State [String] ShowS
maplePDatumStruct PDone           = return $ showString "PDone"
maplePDatumStruct (PEt pat1 pat2) =
    op2 "PEt"
        <$> maplePDatumFun    pat1
        <*> maplePDatumStruct pat2

maplePDatumFun :: PDatumFun x vars a -> State [String] ShowS
maplePDatumFun (PKonst pat) = op1 "PKonst" <$> maplePattern pat
maplePDatumFun (PIdent pat) = op1 "PIdent" <$> maplePattern pat


arg :: (ABT Term abt) => abt '[] a -> ShowS
arg = mapleAST . LC_


maplePrimOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => PrimOp typs a -> SArgs abt args -> ShowS
maplePrimOp Not              (e1 :* End)       = app1 "Not" e1
maplePrimOp Pi               End               = showString "Pi"
maplePrimOp Cos              (e1 :* End)       = app1 "cos" e1
maplePrimOp Sin              (e1 :* End)       = app1 "sin" e1
maplePrimOp Tan              (e1 :* End)       = app1 "tan" e1
maplePrimOp RealPow          (e1 :* e2 :* End) =
    parens (arg e1 . showString " ^ " . arg e2)
maplePrimOp Choose           (e1 :* e2 :* End) = app2 "binomial" e1 e2
maplePrimOp Exp              (e1 :* End)       = app1 "exp"  e1
maplePrimOp Log              (e1 :* End)       = app1 "log"  e1
maplePrimOp (Infinity  _)    End               = showString "infinity"
maplePrimOp GammaFunc        (e1 :* End)       = app1 "GAMMA" e1
maplePrimOp BetaFunc         (e1 :* e2 :* End) = app2 "Beta" e1 e2
maplePrimOp (Equal _)        (e1 :* e2 :* End) =
    parens (arg e1 . showString " = " . arg e2)
maplePrimOp (Less _)         (e1 :* e2 :* End) =
    arg e1 . showString " < " . arg e2
maplePrimOp (NatPow _)       (e1 :* e2 :* End) =
    parens (arg e1 . showString " ^ " . arg e2)
maplePrimOp (Negate _)       (e1 :* End)       = parens (app1 "-" e1)
maplePrimOp (Abs _)          (e1 :* End)       = app1 "abs"  e1
maplePrimOp (Recip   _)      (e1 :* End)       = app1 "1/"   e1
maplePrimOp (NatRoot _)      (e1 :* e2 :* End) = app2 "root" e1 e2
maplePrimOp Floor            (e1 :* End)       = app1 "floor"  e1
maplePrimOp x                _                 =
    error $ "TODO: maplePrimOp{" ++ show x ++ "}"

mapleArrayOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => ArrayOp typs a -> SArgs abt args -> ShowS
mapleArrayOp (Index _) (e1 :* e2 :* End) = app2 "idx"  e1 e2
mapleArrayOp (Size  _) (e1 :* End)       = app1 "size" e1
mapleArrayOp _         _                 = error "TODO: mapleArrayOp{Reduce}"

mapleMeasureOp
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => MeasureOp typs a -> SArgs abt args -> ShowS
mapleMeasureOp Lebesgue    = \(e1 :* e2 :* End) -> app2 "Lebesgue" e1 e2
mapleMeasureOp Counting    = \End               -> showString "Counting(-infinity,infinity)"
mapleMeasureOp Categorical = \(e1 :* End)       -> app1 "Categorical" e1
mapleMeasureOp Uniform     = \(e1 :* e2 :* End) -> app2 "Uniform"  e1 e2
mapleMeasureOp Normal      = \(e1 :* e2 :* End) -> app2 "Gaussian" e1 e2
mapleMeasureOp Poisson     = \(e1 :* End)       -> app1 "PoissonD" e1
mapleMeasureOp Gamma       = \(e1 :* e2 :* End) -> app2 "GammaD"   e1 e2
mapleMeasureOp Beta        = \(e1 :* e2 :* End) -> app2 "BetaD"    e1 e2


----------------------------------------------------------------
mapleType :: Sing (a :: Hakaru) -> ShowS
mapleType SNat         = showString "HInt(Bound(`>=`,0))"
mapleType SInt         = showString "HInt()"
mapleType SProb        = showString "HReal(Bound(`>=`,0))"
mapleType SReal        = showString "HReal()"
mapleType (SFun a b)   = op2 "HFunction" (mapleType a) (mapleType b)
mapleType (SArray a)   = op1 "HArray"    (mapleType a)
mapleType (SMeasure a) = op1 "HMeasure"  (mapleType a)
-- Special case pair
mapleType (SData (STyCon c `STyApp` _ `STyApp` _) (SPlus x SVoid))
    | isJust (jmEq1 c sSymbol_Pair)
    = showString "HData(DatumStruct(pair,["
    . mapleTypeDStruct x
    . showString "]))"
-- Special case unit
mapleType (SData (STyCon c) (SPlus SDone SVoid))
    | isJust (jmEq1 c sSymbol_Unit)
    = showString "HData(DatumStruct(unit,[]))"
-- Special case bool
mapleType (SData (STyCon c) (SPlus SDone (SPlus SDone SVoid)))
    | isJust (jmEq1 c sSymbol_Bool)
    = showString "HData(DatumStruct(true,[]),DatumStruct(false,[]))"
mapleType x = error $ "TODO: mapleType{" ++ show x ++ "}"

mapleTypeDStruct :: Sing (a :: [HakaruFun]) -> ShowS
mapleTypeDStruct SDone      = showString "NULL"
mapleTypeDStruct (SEt x xs) =
      mapleTypeDFun x
    . showString ","
    . mapleTypeDStruct xs

mapleTypeDFun :: Sing (a :: HakaruFun) -> ShowS
mapleTypeDFun (SKonst a) = op1 "Konst" (mapleType a)
mapleTypeDFun SIdent     = showString "Ident"

----------------------------------------------------------------
----------------------------------------------------------- fin.
