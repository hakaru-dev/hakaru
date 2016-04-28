{-# LANGUAGE CPP
           , OverloadedStrings
           , DataKinds
           , KindSignatures
           , GADTs
           #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Language.Hakaru.Parser.SymbolResolve where

import Data.Text hiding (concat, map, maximum, foldr1)
#if __GLASGOW_HASKELL__ < 710
import Data.Functor                     ((<$>))
import Control.Applicative              ((<*>))
#endif
import Control.Monad.Trans.State.Strict (State, state, evalState)

import qualified Data.Number.Nat                 as N
import qualified Data.IntMap                     as IM
import           Data.Foldable                   as F
import           Data.Ratio
import           Data.Proxy                      (KProxy(..))
import           Language.Hakaru.Types.Sing
import           Language.Hakaru.Types.Coercion
import           Language.Hakaru.Types.DataKind  hiding (Symbol)
import           Language.Hakaru.Types.HClasses
import qualified Language.Hakaru.Syntax.AST      as T
import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Syntax.Variable
import qualified Language.Hakaru.Parser.AST      as U

data Symbol a
    = TLam (a -> Symbol a)
    | TNeu a

data Symbol' a
    = TLam' ([a] -> a)
    | TNeu' a

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
    , ("pair",    TLam' $ \es -> F.foldr1 pairPat es)
    , ("just",    TLam' $ \ [a] ->
        U.PDatum "just" . U.PInr . U.PInl $
            U.PKonst a `U.PEt` U.PDone)
    , ("nothing", TLam' $ \ [] ->
        U.PDatum "nothing" . U.PInl $ U.PDone)
    ]

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

type SymbolTable a = [(Text, Symbol U.AST)]

primTable :: SymbolTable a
primTable =
    [-- Datatype constructors
     ("left",        primLeft)
    ,("right",       primRight)
    ,("true",        TNeu $ true_)
    ,("false",       TNeu $ false_)
     -- Coercions
    ,("fromInt",     primCoerce cFromInt)
    ,("fromProb",    primCoerce cFromProb)
    ,("unsafeProb",  primUnsafe cFromProb)
    ,("nat2real",    primCoerce cNat2Real)
    ,("nat2prob",    primCoerce cNat2Prob)
     -- Measures
    ,("lebesgue",    TNeu $ U.MeasureOp_ (U.SealedOp T.Lebesgue) [])
    ,("counting",    TNeu $ U.MeasureOp_ (U.SealedOp T.Counting) [])
    ,("uniform",     primMeasure2 (U.SealedOp T.Uniform))
    ,("normal",      primMeasure2 (U.SealedOp T.Normal))
    ,("poisson",     primMeasure1 (U.SealedOp T.Poisson))
    ,("gamma",       primMeasure2 (U.SealedOp T.Gamma))
    ,("beta",        primMeasure2 (U.SealedOp T.Beta))
    ,("categorical", primMeasure1 (U.SealedOp T.Categorical))
    ,("bern",        primBern)
    ,("factor",      primFactor)
    ,("weight",      primWeight)
    ,("dirac",       TLam $ TNeu . U.Dirac_)
    ,("reject",      TNeu $ U.Reject_)    
    -- PrimOps
    ,("not",         primPrimOp1 U.Not)
    ,("pi",          TNeu $ U.PrimOp_ U.Pi [])
    ,("**",          primPrimOp2 U.RealPow)
    ,("cos",         primPrimOp1 U.Cos)
    ,("exp",         primPrimOp1 U.Exp)
    ,("log",         primPrimOp1 U.Log)
    ,("gammaFunc",   primPrimOp1 U.GammaFunc)
    ,("betaFunc",    primPrimOp2 U.BetaFunc)
    ,("equal",       primPrimOp2 U.Equal)
    ,("less",        primPrimOp2 U.Less)
    ,("negate",      primPrimOp1 U.Negate)
    ,("recip",       primPrimOp1 U.Recip)
    ,("^",           primPrimOp2 U.NatPow)
    ,("natroot",     primPrimOp2 U.NatRoot)
    ,("erf",         primPrimOp1 U.Erf)
    -- ArrayOps
    ,("size",        TLam $ \x -> TNeu $ U.ArrayOp_ U.Size [x])
    ,("reduce",      t3 $ \x y z -> U.ArrayOp_ U.Reduce [x, y, z])
    -- NaryOps
    ,("min",         t2 $ \x y -> U.NaryOp_ U.Min [x, y])
    ,("max",         t2 $ \x y -> U.NaryOp_ U.Max [x, y])
    ]

primPrimOp1, primPrimOp2 :: U.PrimOp -> Symbol U.AST
primPrimOp1 a = TLam $ \x -> TNeu $ U.PrimOp_ a [x]
primPrimOp2 a = t2 $ \x y -> U.PrimOp_ a [x, y]

primMeasure1 :: U.SealedOp T.MeasureOp -> Symbol U.AST
primMeasure1 m = TLam $ \x -> TNeu $ U.MeasureOp_ m [x]

primMeasure2 :: U.SealedOp T.MeasureOp -> Symbol U.AST
primMeasure2 m = t2 $ \x y -> U.MeasureOp_ m [x, y]

primCoerce :: Coercion a b -> Symbol U.AST
primCoerce c = TLam $ TNeu . U.CoerceTo_  (Some2 c)

primUnsafe :: Coercion a b -> Symbol U.AST
primUnsafe c = TLam $ TNeu . U.UnsafeTo_  (Some2 c)

cFromProb :: Coercion 'HProb 'HReal
cFromProb = signed

cNat2Prob :: Coercion 'HNat 'HProb
cNat2Prob = continuous

cNat2Int  :: Coercion 'HNat 'HInt
cNat2Int  = signed

cFromInt  :: Coercion 'HInt 'HReal
cFromInt  = continuous

cNat2Real :: Coercion 'HNat 'HReal
cNat2Real = CCons (Signed HRing_Int) continuous

unit_ :: U.AST
unit_ =
    U.Ann_ (U.Datum_ (U.Datum "unit" . U.Inl $ U.Done))
         (U.SSing sUnit)

true_, false_ :: U.AST
true_  =
    U.Ann_ (U.Datum_ . U.Datum "true"  . U.Inl $ U.Done)
        (U.SSing sBool)
false_ =
    U.Ann_ (U.Datum_ . U.Datum "false" . U.Inr . U.Inl $ U.Done)
        (U.SSing sBool)

unsafeFrom_ :: U.AST -> U.AST
unsafeFrom_ = U.UnsafeTo_ (Some2 $ CCons (Signed HRing_Real) CNil)

primLeft, primRight :: Symbol U.AST
primLeft =
    TLam $ TNeu . U.Datum_ .
        U.Datum "left" . U.Inl . (`U.Et` U.Done) . U.Konst
primRight =
    TLam $ TNeu . U.Datum_ .
        U.Datum "right" . U.Inr . U.Inl . (`U.Et` U.Done) . U.Konst

primWeight, primFactor, primBern :: Symbol U.AST
primWeight = t2 $ \w m -> U.Superpose_ [(w, m)]
primFactor = TLam $ \w -> TNeu $
              U.Superpose_ [(w, U.Dirac_ unit_)]
primBern   =
    TLam $ \p -> TNeu (U.Superpose_
        [ (p, U.Dirac_ true_)
        , (unsafeFrom_ $ U.NaryOp_ U.Sum
            [ U.Literal_ (Some1 $ T.LReal 1.0)
            , U.PrimOp_ U.Negate [p]
            ]
            , U.Dirac_ false_)
        ])

gensym :: Text -> State Int U.Name
gensym s = state $ \i -> (U.Name (N.unsafeNat i) s, i + 1)

mkSym  :: U.Name -> Symbol U.AST
mkSym = TNeu . U.Var_

insertSymbol :: U.Name -> SymbolTable a -> SymbolTable a
insertSymbol n@(U.Name _ name) sym = (name, mkSym n) : sym

insertSymbols :: [U.Name] -> SymbolTable a -> SymbolTable a
insertSymbols []     sym = sym
insertSymbols (n:ns) sym = insertSymbols ns (insertSymbol n sym)


resolveBinder
    :: SymbolTable a
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
    

-- TODO: clean up by merging the @Reader (SymbolTable a)@ and @State Int@ monads
-- | Figure out symbols and types.
symbolResolution
    :: SymbolTable a
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
    U.NegInfinity'      -> return $ U.NegInfinity'
    U.ULiteral v        -> return $ U.ULiteral v

    U.Integrate  name e1 e2 e3 -> do       
        name' <- gensym name
        U.Integrate (mkSym name')
            <$> symbolResolution symbols e1
            <*> symbolResolution symbols e2
            <*> symbolResolution (insertSymbol name' symbols) e3     

    U.NaryOp op es      -> U.NaryOp op
        <$> mapM (symbolResolution symbols) es

    U.Unit              -> return $ U.Unit
    U.Empty             -> return $ U.Empty
    U.Pair e1 e2        -> U.Pair
        <$> symbolResolution symbols e1
        <*> symbolResolution symbols e2

    U.Array name e1 e2  -> resolveBinder symbols name e1 e2 U.Array

    U.Index a i -> U.Index
        <$> symbolResolution symbols a
        <*> symbolResolution symbols i

    U.Case e1 bs -> U.Case
        <$> symbolResolution symbols e1
        <*> mapM (symbolResolveBranch symbols) bs

    U.Dirac  e1            -> U.Dirac <$> symbolResolution symbols e1
    U.Bind   name e1 e2    -> resolveBinder symbols name e1 e2 U.Bind
    U.Plate  name e1 e2    -> resolveBinder symbols name e1 e2 U.Plate
    U.Expect name e1 e2    -> resolveBinder symbols name e1 e2 U.Expect
    U.Chain  name e1 e2 e3 -> do       
        name' <- gensym name
        U.Chain (mkSym name')
            <$> symbolResolution symbols e1
            <*> symbolResolution symbols e2
            <*> symbolResolution (insertSymbol name' symbols) e3     

    U.Msum es -> U.Msum <$> mapM (symbolResolution symbols) es

    U.Data   _name _typ -> error "TODO: symbolResolution{U.Data}"
    U.WithMeta _a _meta -> error "TODO: symbolResolution{U.WithMeta}"


symbolResolveBranch
    :: SymbolTable a
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
    U.App (U.Var t) x ->
        case t of
        TLam f -> U.Var $ f (makeAST $ normAST x)
        TNeu _ -> U.App (U.Var t) (normAST x)

    U.App f x ->
        case normAST f of
        v@(U.Var _) -> normAST (U.App v x)
        f'          -> U.App f' x

    U.Let name e1 e2          -> U.Let name (normAST e1) (normAST e2)
    U.If e1 e2 e3             -> U.If (normAST e1) (normAST e2) (normAST e3)
    U.Ann e typ1              -> U.Ann (normAST e) typ1
    U.Infinity'               -> U.Infinity'
    U.NegInfinity'            -> U.NegInfinity'
    U.Integrate name e1 e2 e3 -> U.Integrate name (normAST e1) (normAST e2) (normAST e3)
    U.ULiteral v              -> U.ULiteral v
    U.NaryOp op es            -> U.NaryOp op (map normAST es)
    U.Unit                    -> U.Unit
    U.Empty                   -> U.Empty
    U.Pair e1 e2              -> U.Pair (normAST e1) (normAST e2)
    U.Array  name e1 e2       -> U.Array name (normAST e1) (normAST e2)
    U.Index       e1 e2       -> U.Index (normAST e1) (normAST e2)    
    U.Case        e1 e2       -> U.Case  (normAST e1) (map branchNorm e2)
    U.Dirac       e1          -> U.Dirac (normAST e1)
    U.Bind   name e1 e2       -> U.Bind   name (normAST e1) (normAST e2)
    U.Plate  name e1 e2       -> U.Plate  name (normAST e1) (normAST e2)
    U.Chain  name e1 e2 e3    -> U.Chain  name (normAST e1) (normAST e2) (normAST e3)
    U.Expect name e1 e2       -> U.Expect name (normAST e1) (normAST e2)
    U.Msum es                 -> U.Msum (map normAST es)
    U.Data name typ           -> U.Data name typ
    U.WithMeta a meta         -> U.WithMeta (normAST a) meta

branchNorm :: U.Branch' (Symbol U.AST) -> U.Branch' (Symbol U.AST)
branchNorm (U.Branch'  pat e2') = U.Branch'  pat (normAST e2')
branchNorm (U.Branch'' pat e2') = U.Branch'' pat (normAST e2')

collapseSuperposes :: [U.AST] -> U.AST
collapseSuperposes es = U.Superpose_ (F.concatMap go es)
    where
    go :: U.AST -> [(U.AST, U.AST)]
    go (U.Superpose_ es') = es'
    go e'                 = [(prob_ 1, e')]

    prob_ :: Ratio Integer -> U.AST
    prob_ = U.Literal_ . U.val . U.Prob

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
makeBranch (U.Branch'' pat ast) = U.Branch (makePattern pat) (makeAST ast)
makeBranch (U.Branch'  _   _)   = error "branch was not symbol resolved"

makeTrue, makeFalse :: U.AST' (Symbol U.AST) -> U.Branch
makeTrue  e =
    U.Branch (makePattern (U.PData' (U.DV "true"  []))) (makeAST e)
makeFalse e =
    U.Branch (makePattern (U.PData' (U.DV "false" []))) (makeAST e)
        
        
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
            U.Lam_ name (makeType typ) (makeAST e1)
    U.App e1 e2 ->
        U.App_ (makeAST e1) (makeAST e2)
    U.Let s e1 e2 ->
        withName "U.Let" s $ \name ->
            U.Let_ name (makeAST e1) (makeAST e2)
    U.If e1 e2 e3 ->
        U.Case_ (makeAST e1) [(makeTrue e2), (makeFalse e3)]
    U.Ann e typ       -> U.Ann_ (makeAST e) (makeType typ)
    U.Infinity'       -> U.PrimOp_ U.Infinity []
    U.NegInfinity'    -> U.PrimOp_ U.NegativeInfinity []
    U.ULiteral v      -> U.Literal_  (U.val v)
    U.NaryOp op es    -> U.NaryOp_ op (map makeAST es)
    U.Unit            -> unit_
    U.Empty           -> U.Empty_
    U.Pair e1 e2      -> U.Pair_ (makeAST e1) (makeAST e2)
    U.Array s e1 e2 ->
        withName "U.Array" s $ \name ->
            U.Array_ (makeAST e1) name (makeAST e2)
    U.Index e1 e2     -> U.ArrayOp_ U.Index_ [(makeAST e1), (makeAST e2)]
    U.Case e bs       -> U.Case_ (makeAST e) (map makeBranch bs)
    U.Dirac e1        -> U.Dirac_ (makeAST e1)
    U.Bind s e1 e2 ->
        withName "U.Bind" s $ \name ->
            U.MBind_ name (makeAST e1) (makeAST e2)
    U.Plate s e1 e2 ->
        withName "U.Plate" s $ \name ->
            U.Plate_ name (makeAST e1) (makeAST e2)
    U.Chain s e1 e2 e3 ->
        withName "U.Chain" s $ \name ->
            U.Chain_ name (makeAST e1) (makeAST e2) (makeAST e3)
    U.Integrate s e1 e2 e3 ->
        withName "U.Integrate" s $ \name ->
            U.Integrate_ name (makeAST e1) (makeAST e2) (makeAST e3)
    U.Expect s e1 e2 ->
        withName "U.Expect" s $ \name ->
            U.Expect_ name (makeAST e1) (makeAST e2)
    U.Msum es -> collapseSuperposes (map makeAST es)
    
    U.Data   _name _typ -> error "TODO: makeAST{U.Data}"
    U.WithMeta _a _meta -> error "TODO: makeAST{U.WithMeta}"

    where
    withName :: [Char] -> Symbol U.AST -> (U.Name -> r) -> r
    withName fun s k =
        case s of
        TNeu (U.Var_ name) -> k name
        _                  -> error $ "makeAST: bad " ++ fun

resolveAST :: U.AST' Text -> U.AST
resolveAST ast =
    makeAST . normAST $ evalState (symbolResolution primTable ast) 0

resolveAST'
    :: [U.Name]
    -> U.AST' Text
    -> U.AST
resolveAST' syms ast =
    makeAST .
    normAST $
    evalState (symbolResolution
        (insertSymbols syms primTable) ast)
        (nextVarID syms)
    where
    nextVarID [] = N.fromNat 0
    nextVarID xs = N.fromNat . (1+) . F.maximum $ map U.nameID xs

makeName :: SomeVariable ('KProxy :: KProxy Hakaru) -> U.Name
makeName (SomeVariable (Variable hint vID _)) = U.Name vID hint

fromVarSet :: VarSet ('KProxy :: KProxy Hakaru) -> [U.Name]
fromVarSet (VarSet xs) = map makeName (IM.elems xs)
