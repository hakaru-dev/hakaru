{-# LANGUAGE CPP
           , OverloadedStrings
           , DataKinds
           , KindSignatures
           , GADTs
           , LambdaCase
           , PolyKinds
           , RankNTypes
           #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Language.Hakaru.Parser.SymbolResolve
    (
      resolveAST, resolveAST', makeName, fromVarSet
    ) where

import Data.Text hiding (concat, map, maximum, foldr1, singleton)
#if __GLASGOW_HASKELL__ < 710
import Data.Functor                     ((<$>))
import Control.Applicative              ((<*>))
#endif
import Control.Monad.Trans.State.Strict (State, state, evalState)
import Control.Monad (join)

import qualified Data.Number.Nat                 as N
import qualified Data.IntMap                     as IM
import           Data.Foldable                   as F
import           Data.Ratio
import           Data.Proxy                      (KProxy(..))
import           Data.List.NonEmpty              as L (NonEmpty(..), fromList)
import           Language.Hakaru.Types.Sing
import           Language.Hakaru.Types.Coercion
import           Language.Hakaru.Types.DataKind  hiding (Symbol)
import           Language.Hakaru.Types.HClasses
import qualified Language.Hakaru.Syntax.AST      as T
import           Language.Hakaru.Syntax.ABT      hiding (fromVarSet)
import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Syntax.Variable ()
import qualified Language.Hakaru.Parser.AST   as U
import           Language.Hakaru.Evaluation.Coalesce (coalesce)
import qualified Language.Hakaru.Syntax.Prelude  as P

data Symbol a
    = TLam (a -> Symbol a)
    | TNeu a

data Symbol' a
    = TLam' ([a] -> a)
    | TNeu' a

singleton :: a -> L.NonEmpty a
singleton x = x :| []

primPat :: [(Text, Symbol' U.Pattern)]
primPat =
    [ ("left",    TLam' $ \ [a] ->
        U.PDatum "left" . U.PInl $
            U.PKonst a `U.PEt` U.PDone)
    , ("right",   TLam' $ \ [b] ->
        U.PDatum "right" . U.PInr . U.PInl $
            U.PKonst b `U.PEt` U.PDone)
    , ("true",    TNeu' . U.PDatum "true"  . U.PInl $ U.PDone)
    , ("false",   TNeu' . U.PDatum "false" . U.PInr . U.PInl $ U.PDone)
    , ("unit",    TNeu' . U.PDatum "unit"  . U.PInl $ U.PDone)
    , ("pair",    TLam' $ \es -> F.foldr1 pairPat es)
    , ("just",    TLam' $ \ [a] ->
        U.PDatum "just" . U.PInr . U.PInl $
            U.PKonst a `U.PEt` U.PDone)
    , ("nothing", TLam' $ \ [] ->
        U.PDatum "nothing" . U.PInl $ U.PDone)
    ]

pairPat :: U.Pattern -> U.Pattern -> U.Pattern
pairPat a b =
    U.PDatum "pair" .  U.PInl $
    U.PKonst a `U.PEt` U.PKonst b `U.PEt` U.PDone

primTypes :: [(Text, Symbol' U.SSing)]
primTypes =
    [ ("nat",     TNeu' $ U.SSing SNat)
    , ("int",     TNeu' $ U.SSing SInt)
    , ("prob",    TNeu' $ U.SSing SProb)
    , ("real",    TNeu' $ U.SSing SReal)
    , ("unit",    TNeu' $ U.SSing sUnit)
    , ("bool",    TNeu' $ U.SSing sBool)
    , ("array",   TLam' $ \ [U.SSing a] -> U.SSing $ SArray a)
    , ("measure", TLam' $ \ [U.SSing a] -> U.SSing $ SMeasure a)
    , ("either",  TLam' $ \ [U.SSing a, U.SSing b] -> U.SSing $ sEither a b)
    , ("pair",    TLam' $ \ [U.SSing a, U.SSing b] -> U.SSing $ sPair a b)
    , ("maybe",   TLam' $ \ [U.SSing a] -> U.SSing $ sMaybe a)
    ]

t2 :: (U.AST -> U.AST -> U.AST) -> Symbol U.AST
t2 f = TLam $ \a -> TLam $ \b -> TNeu (f a b)

t3 :: (U.AST -> U.AST -> U.AST -> U.AST) -> Symbol U.AST
t3 f = TLam $ \a -> TLam $ \b -> TLam $ \c -> TNeu (f a b c)

type SymbolTable = [(Text, Symbol U.AST)]

primTable :: SymbolTable
primTable =
    [-- Datatype constructors
     ("left",        primLeft)
    ,("right",       primRight)
    ,("just",        primJust)
    ,("nothing",     primNothing)
    ,("true",        TNeu $ true_)
    ,("false",       TNeu $ false_)
     -- Coercions
    ,("int2nat",     primUnsafe cNat2Int)  -- unsafe, wrong direction
    ,("int2real",    primCoerce cInt2Real)
    ,("prob2real",   primCoerce cProb2Real)
    ,("real2prob",   primUnsafe cProb2Real) -- unsafe, wrong direction
    ,("nat2real",    primCoerce cNat2Real)
    ,("nat2prob",    primCoerce cNat2Prob)
    ,("nat2int",     primCoerce cNat2Int)
     -- Measures
    ,("lebesgue",    primMeasure2 (U.SomeOp T.Lebesgue))
    ,("counting",    TNeu $ syn $ U.MeasureOp_ (U.SomeOp T.Counting) [])
    ,("uniform",     primMeasure2 (U.SomeOp T.Uniform))
    ,("normal",      primMeasure2 (U.SomeOp T.Normal))
    ,("poisson",     primMeasure1 (U.SomeOp T.Poisson))
    ,("gamma",       primMeasure2 (U.SomeOp T.Gamma))
    ,("beta",        primMeasure2 (U.SomeOp T.Beta))
    ,("categorical", primMeasure1 (U.SomeOp T.Categorical))
    ,("factor",      primFactor)
    ,("weight",      primWeight)
    ,("dirac",       TLam $ TNeu . syn . U.Dirac_)
    ,("reject",      TNeu $ syn U.Reject_)
    -- PrimOps
    ,("not",         primPrimOp1 U.Not)
    ,("impl",        primPrimOp2 U.Impl)
    ,("diff",        primPrimOp2 U.Diff)
    ,("nand",        primPrimOp2 U.Nand)
    ,("nor",         primPrimOp2 U.Nor)
    ,("pi",          primPrimOp0 U.Pi)
    ,("**",          primPrimOp2 U.RealPow)
    ,("choose",      primPrimOp2 U.Choose)
    ,("cos",         primPrimOp1 U.Cos)
    ,("exp",         primPrimOp1 U.Exp)
    ,("log",         primPrimOp1 U.Log)
    ,("inf",         primPrimOp0 U.Infinity)
    ,("gammaFunc",   primPrimOp1 U.GammaFunc)
    ,("betaFunc",    primPrimOp2 U.BetaFunc)
    ,("equal",       primPrimOp2 U.Equal)
    ,("less",        primPrimOp2 U.Less)
    ,("negate",      primPrimOp1 U.Negate)
    ,("abs",         primPrimOp1 U.Abs)
    ,("signum",      primPrimOp1 U.Signum)
    ,("recip",       primPrimOp1 U.Recip)
    ,("^",           primPrimOp2 U.NatPow)
    ,("natroot",     primPrimOp2 U.NatRoot)
    ,("sqrt",        TLam $ \x -> TNeu . syn $ U.PrimOp_ U.NatRoot [x, two])
    ,("erf",         primPrimOp1 U.Erf)
    ,("sin",         primPrimOp1 U.Sin)
    ,("cos",         primPrimOp1 U.Cos)
    ,("tan",         primPrimOp1 U.Tan)
    ,("asin",        primPrimOp1 U.Asin)
    ,("acos",        primPrimOp1 U.Acos)
    ,("atan",        primPrimOp1 U.Atan)
    ,("sinh",        primPrimOp1 U.Sinh)
    ,("cosh",        primPrimOp1 U.Cosh)
    ,("tanh",        primPrimOp1 U.Tanh)
    ,("asinh",       primPrimOp1 U.Asinh)
    ,("acosh",       primPrimOp1 U.Acosh)
    ,("atanh",       primPrimOp1 U.Atanh)
    ,("floor",       primPrimOp1 U.Floor)
    -- ArrayOps
    ,("size",        TLam $ \x -> TNeu . syn $ U.ArrayOp_ U.Size [x])
    ,("reduce",      t3 $ \x y z -> syn $ U.ArrayOp_ U.Reduce [x, y, z])
    -- NaryOps
    ,("xor",         t2 $ \x y -> syn $ U.NaryOp_ U.Xor [x, y])
    ,("iff",         t2 $ \x y -> syn $ U.NaryOp_ U.Iff [x, y])
    ,("min",         t2 $ \x y -> syn $ U.NaryOp_ U.Min [x, y])
    ,("max",         t2 $ \x y -> syn $ U.NaryOp_ U.Max [x, y])

    -- Macros
    ,("weibull",     TNeu $ syn $ U.InjTyped $
                     P.lam $ \x -> P.lam $ \y -> P.weibull x y)
    ]

primPrimOp0, primPrimOp1, primPrimOp2 :: U.PrimOp -> Symbol U.AST
primPrimOp0 a = TNeu . syn $ U.PrimOp_ a []
primPrimOp1 a = TLam $ \x -> TNeu . syn $ U.PrimOp_ a [x]
primPrimOp2 a = t2 $ \x y ->        syn $ U.PrimOp_ a [x, y]

primMeasure1 :: U.SomeOp T.MeasureOp -> Symbol U.AST
primMeasure1 m = TLam $ \x -> TNeu . syn $ U.MeasureOp_ m [x]

primMeasure2 :: U.SomeOp T.MeasureOp -> Symbol U.AST
primMeasure2 m = t2 $ \x y -> syn $ U.MeasureOp_ m [x, y]

primCoerce :: Coercion a b -> Symbol U.AST
primCoerce c = TLam $ TNeu . syn . U.CoerceTo_  (Some2 c)

primUnsafe :: Coercion a b -> Symbol U.AST
primUnsafe c = TLam $ TNeu . syn . U.UnsafeTo_  (Some2 c)

cProb2Real :: Coercion 'HProb 'HReal
cProb2Real = signed

cNat2Prob :: Coercion 'HNat 'HProb
cNat2Prob = continuous

cNat2Int  :: Coercion 'HNat 'HInt
cNat2Int  = signed

cInt2Real  :: Coercion 'HInt 'HReal
cInt2Real  = continuous

cNat2Real :: Coercion 'HNat 'HReal
cNat2Real = CCons (Signed HRing_Int) continuous

unit_ :: U.AST
unit_ =
    syn $ U.Ann_ (U.SSing sUnit)
                 (syn $ U.Datum_ (U.Datum "unit" . U.Inl $ U.Done))

true_, false_ :: U.AST
true_  =
    syn $ U.Ann_ (U.SSing sBool)
                 (syn $ U.Datum_ . U.Datum "true"  . U.Inl $ U.Done)

false_ =
    syn $ U.Ann_ (U.SSing sBool)
                 (syn $ U.Datum_ . U.Datum "false" . U.Inr . U.Inl $ U.Done)

unsafeFrom_ :: U.AST -> U.AST
unsafeFrom_ = syn . U.UnsafeTo_ (Some2 $ CCons (Signed HRing_Real) CNil)

primLeft, primRight :: Symbol U.AST
primLeft =
    TLam $ TNeu . syn . U.Datum_ .
        U.Datum "left" . U.Inl . (`U.Et` U.Done) . U.Konst
primRight =
    TLam $ TNeu . syn . U.Datum_ .
        U.Datum "right" . U.Inr . U.Inl . (`U.Et` U.Done) . U.Konst

primJust, primNothing :: Symbol U.AST
primJust =
    TLam $ TNeu . syn . U.Datum_ .
        U.Datum "just" . U.Inr . U.Inl . (`U.Et` U.Done) . U.Konst
primNothing =
    TNeu . syn . U.Datum_ .
        U.Datum "nothing" . U.Inl $ U.Done

primWeight, primFactor :: Symbol U.AST
primWeight = t2 $ \w m -> syn $ U.Superpose_ (singleton (w, m))
primFactor = TLam $ \w -> TNeu . syn . U.Superpose_ $
              singleton (w, syn $ U.Dirac_ unit_)

two :: U.AST
two = syn . U.Literal_ . U.val . U.Nat $ 2

gensym :: Text -> State Int U.Name
gensym s = state $ \i -> (U.Name (N.unsafeNat i) s, i + 1)

mkSym  :: U.Name -> Symbol U.AST
mkSym (U.Name i t) = TNeu $ var (Variable t i U.SU)

insertSymbol :: U.Name -> SymbolTable -> SymbolTable
insertSymbol n@(U.Name _ name) sym = (name, mkSym n) : sym

insertSymbols :: [U.Name] -> SymbolTable -> SymbolTable
insertSymbols []     sym = sym
insertSymbols (n:ns) sym = insertSymbols ns (insertSymbol n sym)


resolveBinder
    :: SymbolTable
    -> Text
    -> U.AST' Text
    -> U.AST' Text
    -> (Symbol U.AST
        -> U.AST' (Symbol U.AST)
        -> U.AST' (Symbol U.AST)
        -> U.AST' (Symbol U.AST))
    -> State Int (U.AST' (Symbol U.AST))
resolveBinder symbols name e1 e2 f = do
    name' <- gensym name
    f (mkSym name')
        <$> symbolResolution symbols e1
        <*> symbolResolution (insertSymbol name' symbols) e2

resolveTransform
    :: SymbolTable
    -> U.Transform'
    -> U.SArgs' Text
    -> State Int (U.AST' (Symbol U.AST))
resolveTransform symbols tr (U.SArgs' es) =
    U.Transform tr . U.SArgs' <$> mapM go es where
      go :: ([Text], U.AST' Text)
         -> State Int ([Symbol U.AST], U.AST' (Symbol U.AST))
      go (nms,x) = do
        nms' <- mapM gensym nms
        (,) (map mkSym nms') <$>
            symbolResolution (insertSymbols nms' symbols) x

-- TODO: clean up by merging the @Reader (SymbolTable)@ and @State Int@ monads
-- | Figure out symbols and types.
symbolResolution
    :: SymbolTable
    -> U.AST' Text
    -> State Int (U.AST' (Symbol U.AST))
symbolResolution symbols ast =
    case ast of
    U.Var name ->
        case lookup name symbols of
        Nothing -> (U.Var . mkSym) <$> gensym name
        Just a  -> return $ U.Var a

    U.Lam name typ x -> do
        name' <- gensym name
        U.Lam (mkSym name') typ
            <$> symbolResolution (insertSymbol name' symbols) x

    U.App f x -> U.App
        <$> symbolResolution symbols f
        <*> symbolResolution symbols x

    U.Let name e1 e2    -> resolveBinder symbols name e1 e2 U.Let
    U.If e1 e2 e3       -> U.If
        <$> symbolResolution symbols e1
        <*> symbolResolution symbols e2
        <*> symbolResolution symbols e3

    U.Ann e typ         -> (`U.Ann` typ) <$> symbolResolution symbols e
    U.Infinity'         -> return $ U.Infinity'
    U.ULiteral v        -> return $ U.ULiteral v

    U.Integrate  name e1 e2 e3 -> do
        name' <- gensym name
        U.Integrate (mkSym name')
            <$> symbolResolution symbols e1
            <*> symbolResolution symbols e2
            <*> symbolResolution (insertSymbol name' symbols) e3

    U.Summate    name e1 e2 e3 -> do
        name' <- gensym name
        U.Summate (mkSym name')
            <$> symbolResolution symbols e1
            <*> symbolResolution symbols e2
            <*> symbolResolution (insertSymbol name' symbols) e3

    U.Product    name e1 e2 e3 -> do
        name' <- gensym name
        U.Product (mkSym name')
            <$> symbolResolution symbols e1
            <*> symbolResolution symbols e2
            <*> symbolResolution (insertSymbol name' symbols) e3

    U.Bucket     name e1 e2 e3 -> do
        name' <- gensym name
        U.Bucket (mkSym name')
            <$> symbolResolution symbols e1
            <*> symbolResolution symbols e2
            <*> symbolResolutionReducer (insertSymbol name' symbols) e3

    U.NaryOp op es      -> U.NaryOp op
        <$> mapM (symbolResolution symbols) es

    U.Unit              -> return $ U.Unit
    U.Pair e1 e2        -> U.Pair
        <$> symbolResolution symbols e1
        <*> symbolResolution symbols e2

    U.Array name e1 e2  -> resolveBinder symbols name e1 e2 U.Array

    U.ArrayLiteral es   -> U.ArrayLiteral <$> mapM (symbolResolution symbols) es

    U.Index a i -> U.Index
        <$> symbolResolution symbols a
        <*> symbolResolution symbols i

    U.Case e1 bs -> U.Case
        <$> symbolResolution symbols e1
        <*> mapM (symbolResolveBranch symbols) bs

    U.Bind   name e1 e2    -> resolveBinder symbols name e1 e2 U.Bind
    U.Plate  name e1 e2    -> resolveBinder symbols name e1 e2 U.Plate
    U.Transform tr es      -> resolveTransform symbols tr es
    U.Chain  name e1 e2 e3 -> do
        name' <- gensym name
        U.Chain (mkSym name')
            <$> symbolResolution symbols e1
            <*> symbolResolution symbols e2
            <*> symbolResolution (insertSymbol name' symbols) e3

    U.Msum es -> U.Msum <$> mapM (symbolResolution symbols) es

    U.Data name tvars typ e -> error $ ("TODO: symbolResolution{U.Data} " ++
                                        show name  ++ " with " ++
                                        show tvars ++ ":" ++ show typ)
    U.WithMeta a meta -> U.WithMeta
        <$> symbolResolution symbols a
        <*> return meta

symbolResolutionReducer
    :: SymbolTable
    -> U.Reducer' Text
    -> State Int (U.Reducer' (Symbol U.AST))
symbolResolutionReducer symbols ast =
    case ast of
    U.R_Fanout e1 e2        -> U.R_Fanout
                               <$> symbolResolutionReducer symbols e1
                               <*> symbolResolutionReducer symbols e2

    U.R_Index name e1 e2 e3 -> do
      name' <- gensym name
      U.R_Index (mkSym name')
           <$> symbolResolution symbols e1
           <*> symbolResolution symbols e2
           <*> symbolResolutionReducer (insertSymbol name' symbols) e3
    U.R_Split e1 e2 e3      -> U.R_Split
                               <$> symbolResolution symbols e1
                               <*> symbolResolutionReducer symbols e2
                               <*> symbolResolutionReducer symbols e3
    U.R_Nop                 -> return U.R_Nop
    U.R_Add   e1            -> U.R_Add <$> symbolResolution symbols e1


symbolResolveBranch
    :: SymbolTable
    -> U.Branch' Text
    -> State Int (U.Branch' (Symbol U.AST))
symbolResolveBranch symbols (U.Branch' pat ast) = do
    (pat', names) <- symbolResolvePat pat
    ast' <- symbolResolution (insertSymbols names symbols) ast
    return $ U.Branch'' pat' ast'
symbolResolveBranch _ _ =
    error "TODO: symbolResolveBranch{U.Branch''}"


symbolResolvePat
    :: U.Pattern' Text
    -> State Int (U.Pattern' U.Name, [U.Name])
symbolResolvePat (U.PVar' "true") =
    return (U.PData' (U.DV "true" []), [])
symbolResolvePat (U.PVar' "false") =
    return (U.PData' (U.DV "false" []), [])
symbolResolvePat (U.PVar' name)  = do
    name' <- gensym name
    return (U.PVar' name', [name'])
symbolResolvePat U.PWild' =
    return (U.PWild', [])
symbolResolvePat (U.PData' (U.DV name args)) = do
    args' <- mapM symbolResolvePat args
    let (args'', names) = unzip args'
    return $ (U.PData' (U.DV name args''), F.concat names)


-- | Make AST and give unique names for variables.
--
-- The logic here is to do normalization by evaluation for our
-- primitives. App inspects its first argument to see if it should
-- do something special. Otherwise App behaves as normal.
normAST :: U.AST' (Symbol U.AST) -> U.AST' (Symbol U.AST)
normAST ast =
    case ast of
    U.Var a           -> U.Var a
    U.Lam name typ f  -> U.Lam name typ (normAST f)
    U.App f x ->
        let x' = normAST x
            f' = normAST f in
        case U.withoutMeta f' of
        U.Var (TLam f)      -> U.Var $ f (makeAST x')
        _                   -> U.App f' x'

    U.Let name e1 e2          -> U.Let name (normAST e1) (normAST e2)
    U.If e1 e2 e3             -> U.If (normAST e1) (normAST e2) (normAST e3)
    U.Ann e typ1              -> U.Ann (normAST e) typ1
    U.Infinity'               -> U.Infinity'
    U.Integrate name e1 e2 e3 -> U.Integrate name (normAST e1) (normAST e2) (normAST e3)
    U.Summate   name e1 e2 e3 -> U.Summate   name (normAST e1) (normAST e2) (normAST e3)
    U.Product   name e1 e2 e3 -> U.Product   name (normAST e1) (normAST e2) (normAST e3)
    U.Bucket    name e1 e2 e3 -> U.Bucket    name (normAST e1) (normAST e2) (redNorm e3)
    U.ULiteral v              -> U.ULiteral v
    U.NaryOp op es            -> U.NaryOp op (map normAST es)
    U.Unit                    -> U.Unit
    U.Pair e1 e2              -> U.Pair (normAST e1) (normAST e2)
    U.Array  name e1 e2       -> U.Array name (normAST e1) (normAST e2)
    U.ArrayLiteral   es       -> U.ArrayLiteral (map normAST es)
    U.Index       e1 e2       -> U.Index (normAST e1) (normAST e2)
    U.Case        e1 e2       -> U.Case  (normAST e1) (map branchNorm e2)
    U.Bind   name e1 e2       -> U.Bind   name (normAST e1) (normAST e2)
    U.Plate  name e1 e2       -> U.Plate  name (normAST e1) (normAST e2)
    U.Chain  name e1 e2 e3    -> U.Chain  name (normAST e1) (normAST e2) (normAST e3)
    U.Transform tr es         -> U.Transform tr (normSArgs es)
    U.Msum es                 -> U.Msum (map normAST es)
    U.Data name tvars typs e  -> U.Data name tvars typs e
     -- do we need to norm here? what if we try to define `true` which is already a constructor
    U.WithMeta a meta         -> U.WithMeta (normAST a) meta

normSArgs :: U.SArgs' (Symbol U.AST) -> U.SArgs' (Symbol U.AST)
normSArgs (U.SArgs' es) = U.SArgs' $ map (fmap normAST) es

branchNorm :: U.Branch' (Symbol U.AST) -> U.Branch' (Symbol U.AST)
branchNorm (U.Branch'  pat e2') = U.Branch'  pat (normAST e2')
branchNorm (U.Branch'' pat e2') = U.Branch'' pat (normAST e2')

redNorm :: U.Reducer' (Symbol U.AST) -> U.Reducer' (Symbol U.AST)
redNorm ast =
    case ast of
     U.R_Fanout e1 e2         ->
         U.R_Fanout (redNorm e1) (redNorm e2)
     U.R_Index  name e1 e2 e3 ->
         U.R_Index name (normAST e1) (normAST e2) (redNorm e3)
     U.R_Split e1 e2 e3       ->
         U.R_Split (normAST e1) (redNorm e2) (redNorm e3)
     U.R_Nop                  -> U.R_Nop
     U.R_Add   e1             -> U.R_Add (normAST e1)

collapseSuperposes :: [U.AST] -> U.AST
collapseSuperposes es = syn $ U.Superpose_ (fromList $ F.concatMap go es)
    where
    go :: U.AST -> [(U.AST, U.AST)]
    go e = caseVarSyn e (\x -> [(prob_ 1, var x)]) $ \t ->
              case t of
              U.Superpose_ es' -> F.toList es'
              _                -> [(prob_ 1, e)]

    prob_ :: Ratio Integer -> U.AST
    prob_ = syn . U.Literal_ . U.val . U.Prob

makeType :: U.TypeAST' -> U.SSing
makeType (U.TypeVar t) =
    case lookup t primTypes of
    Just (TNeu' t') -> t'
    _               -> error $ "Type " ++ show t ++ " is not a primitive"
makeType (U.TypeFun f x) =
    case (makeType f, makeType x) of
    (U.SSing f', U.SSing x') -> U.SSing $ SFun f' x'
makeType (U.TypeApp f args) =
    case lookup f primTypes of
    Just (TLam' f') -> f' (map makeType args)
    _               -> error $ "Type " ++ show f ++ " is not a primitive"


makePattern :: U.Pattern' U.Name -> U.Pattern
makePattern U.PWild'        = U.PWild
makePattern (U.PVar' name)  =
    case lookup (U.hintID name) primPat of
    Just (TLam' _)  -> error "TODO{makePattern:PVar:TLam}"
    Just (TNeu' p') -> p'
    Nothing         -> U.PVar name
makePattern (U.PData' (U.DV name args)) =
    case lookup name primPat of
    Just (TLam' f') -> f' (map makePattern args)
    Just (TNeu' p') -> p'
    Nothing -> error $ "Data constructor " ++ show name ++ " not found"

makeBranch :: U.Branch' (Symbol U.AST) -> U.Branch
makeBranch (U.Branch'' pat ast) = U.Branch_ (makePattern pat) (makeAST ast)
makeBranch (U.Branch'  _   _)   = error "branch was not symbol resolved"

makeTrue, makeFalse :: U.AST' (Symbol U.AST) -> U.Branch
makeTrue  e =
    U.Branch_ (makePattern (U.PData' (U.DV "true"  []))) (makeAST e)
makeFalse e =
    U.Branch_ (makePattern (U.PData' (U.DV "false" []))) (makeAST e)

makeReducerAST
    :: Variable 'U.U
    -> U.Reducer' (Symbol U.AST)
    -> List1 Variable xs
    -> U.Reducer xs U.U_ABT 'U.U
makeReducerAST i r1 bs =
    case r1 of
    U.R_Fanout r2 r3       -> U.R_Fanout_
                              (makeReducerAST i r2 bs)
                              (makeReducerAST i r3 bs)
    U.R_Index  b  e1 e2 r1 -> withName "U.R_Index" b $ \b' ->
                                U.R_Index_
                                b' -- HACK: This shouldn't be needed here
                                (binds_ bs (makeAST e1))
                                (bind i (binds_ bs (makeAST e2)))
                                (makeReducerAST i r1 (Cons1 b' bs))
    U.R_Split  e1 r2 r3    -> U.R_Split_
                              (bind i (binds_ bs (makeAST e1)))
                              (makeReducerAST i r2 bs)
                              (makeReducerAST i r3 bs)
    U.R_Nop                -> U.R_Nop_
    U.R_Add e1             -> U.R_Add_ (bind i (binds_ bs (makeAST e1)))

makeAST :: U.AST' (Symbol U.AST) -> U.AST
makeAST ast =
    case ast of
    -- TODO: Add to Symbol datatype: gensymed names and types
    -- for primitives (type for arg on lam, return type in neu)
    U.Var (TLam _) ->
        error "makeAST: Passed primitive with wrong number of arguments"
    U.Var (TNeu e) -> e
    U.Lam s typ e1 ->
        withName "U.Lam" s $ \name ->
            syn $ U.Lam_ (makeType typ) (bind name $ makeAST e1)
    U.App e1 e2 ->
        syn $ U.App_ (makeAST e1) (makeAST e2)
    U.Let s e1 e2 ->
        withName "U.Let" s $ \name ->
            syn $ U.Let_ (makeAST e1) (bind name $ makeAST e2)
    U.If e1 e2 e3 ->
        syn $ U.Case_ (makeAST e1) [(makeTrue e2), (makeFalse e3)]
    U.Ann e typ       -> syn $ U.Ann_ (makeType typ) (makeAST e)
    U.Infinity'       -> syn $ U.PrimOp_ U.Infinity []
    U.ULiteral v      -> syn $ U.Literal_  (U.val v)
    U.NaryOp op es    -> syn $ U.NaryOp_ op (map makeAST es)
    U.Unit            -> unit_
    U.Pair e1 e2      -> syn $ U.Pair_ (makeAST e1) (makeAST e2)
    U.Array s e1 e2 ->
        withName "U.Array" s $ \name ->
            syn $ U.Array_ (makeAST e1) (bind name $ makeAST e2)
    U.ArrayLiteral es -> syn $ U.ArrayLiteral_ (map makeAST es)
    U.Index e1 e2     -> syn $ U.ArrayOp_ U.Index_ [(makeAST e1), (makeAST e2)]
    U.Case e bs       -> syn $ U.Case_ (makeAST e) (map makeBranch bs)
    U.Bind s e1 e2 ->
        withName "U.Bind" s $ \name ->
            syn $ U.MBind_ (makeAST e1) (bind name $ makeAST e2)
    U.Plate s e1 e2 ->
        withName "U.Plate" s $ \name ->
            syn $ U.Plate_ (makeAST e1) (bind name $ makeAST e2)
    U.Chain s e1 e2 e3 ->
        withName "U.Chain" s $ \name ->
            syn $ U.Chain_ (makeAST e1) (makeAST e2) (bind name $ makeAST e3)
    U.Integrate s e1 e2 e3 ->
        withName "U.Integrate" s $ \name ->
            syn $ U.Integrate_ (makeAST e1) (makeAST e2) (bind name $ makeAST e3)
    U.Summate s e1 e2 e3 ->
        withName "U.Summate" s $ \name ->
            syn $ U.Summate_ (makeAST e1) (makeAST e2) (bind name $ makeAST e3)
    U.Product s e1 e2 e3 ->
        withName "U.Product" s $ \name ->
            syn $ U.Product_ (makeAST e1) (makeAST e2) (bind name $ makeAST e3)
    U.Bucket s e1 e2 e3 ->
        withName "U.Bucket"  s $ \name ->
            syn $ U.Bucket_ (makeAST e1) (makeAST e2) (makeReducerAST name e3 Nil1)
    U.Transform tr es -> makeTransform tr es
    U.Msum es -> collapseSuperposes (map makeAST es)
    U.Data name tvars typs e -> error "TODO: makeAST{U.Data}" 
    U.WithMeta a meta -> withMetadata meta (makeAST a)

makeTransform :: U.Transform' -> U.SArgs' (Symbol U.AST) -> U.AST
makeTransform tru esu =
  case typedTransform tru of
    Some2 tr ->
      let wrongArgsErr = error $ "Wrong number of arguments passed to " ++
                                 T.transformName tr
          res = U.Transform_ tr <$> matchSArgs (transformArgs tr) esu
      in maybe wrongArgsErr syn res

type SVarsSpine = (List1 (Lift1 ()) :: [k] -> *)
type SArgsSpine = (List1 (PointwiseP SVarsSpine (Lift1 ())) :: [([k],k1)] -> *)

transformArgs :: T.Transform xs a -> SArgsSpine xs
transformArgs t =
  let arg0 = PwP Nil1 (Lift1 ())
      arg1 = PwP (Cons1 (Lift1 ()) Nil1) (Lift1 ())
  in case t of
     -- TODO: can SingI be generalized to allow things which aren't `Sing's
     -- so these right hand sides can become `sing'?
       T.Observe   -> Cons1 arg0 $ Cons1 arg0 Nil1
       T.MH        -> Cons1 arg0 $ Cons1 arg0 Nil1
       T.MCMC      -> Cons1 arg0 $ Cons1 arg0 Nil1
       T.Disint k  -> Cons1 arg0 Nil1
       T.Summarize -> Cons1 arg0 Nil1
       T.Simplify  -> Cons1 arg0 Nil1
       T.Reparam   -> Cons1 arg0 Nil1
       T.Expect    -> Cons1 arg0 $ Cons1 arg1 Nil1

matchSArgs :: SArgsSpine xs -> U.SArgs' (Symbol U.AST)
           -> Maybe (U.SArgs U.U_ABT xs)
matchSArgs sp (U.SArgs' es) =
  case (sp, es) of
    ( Nil1, [] ) -> Just U.End
    ( Cons1 (PwP vs _) sp', (vs',e0):es' )
      -> join $ matchSVars vs vs' e0 $ \vsu e0' ->
           (U.:*) (vsu, e0') <$> matchSArgs sp' (U.SArgs' es')
    _ -> Nothing

matchSVars :: SVarsSpine vs -> [Symbol U.AST] -> U.AST' (Symbol U.AST)
           -> (forall vsu . List2 U.ToUntyped vs vsu
                         -> U.U_ABT vsu 'U.U
                         -> r)
           -> Maybe r
matchSVars vs nms e k =
  case (vs, nms) of
    (Nil1       , []     ) -> Just $ k Nil2 (makeAST e)
    (Cons1 v vs', nm:nms') ->
      matchSVars vs' nms' e $ \vsu e' ->
        withName "U.SArgs" nm $ \nm' ->
          k (Cons2 U.ToU vsu) (bind nm' e')
    _ -> Nothing

typedTransform :: U.Transform' -> Some2 T.Transform
typedTransform = \case
  U.Observe   -> Some2 T.Observe
  U.MH        -> Some2 T.MH
  U.MCMC      -> Some2 T.MCMC
  U.Disint k  -> Some2 $ T.Disint k
  U.Summarize -> Some2 T.Summarize
  U.Simplify  -> Some2 T.Simplify
  U.Reparam   -> Some2 T.Reparam
  U.Expect    -> Some2 T.Expect

withName :: String -> Symbol U.AST -> (Variable 'U.U -> r) -> r
withName fun s k =
    case s of
    TNeu e -> caseVarSyn e k (error $ "makeAST: bad " ++ fun)
    _      -> error $ "makeAST: bad " ++ fun

resolveAST :: U.AST' Text -> U.AST
resolveAST ast =
    coalesce .
    makeAST  .
    normAST $
    evalState (symbolResolution primTable ast) 0

resolveAST'
    :: N.Nat
    -> [U.Name]
    -> U.AST' Text
    -> U.AST
resolveAST' nextVar syms ast =
    coalesce .
    makeAST  .
    normAST  $
    evalState (symbolResolution
        (insertSymbols syms primTable) ast)
        (N.fromNat $ nextVarID_ syms)
    where
    nextVarID_ [] = nextVar
    nextVarID_ xs = max nextVar . (1+) . F.maximum $ map U.nameID xs

makeName :: SomeVariable ('KProxy :: KProxy Hakaru) -> U.Name
makeName (SomeVariable (Variable hint vID _)) = U.Name vID hint

fromVarSet :: VarSet ('KProxy :: KProxy Hakaru) -> [U.Name]
fromVarSet (VarSet xs) = map makeName (IM.elems xs)
