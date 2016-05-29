{-# LANGUAGE GADTs
           , DataKinds
           , PolyKinds
           , ExistentialQuantification
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}

module Language.Hakaru.Parser.AST where

import qualified Data.Number.Nat     as N
import qualified Data.Number.Natural as N
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Syntax.AST
    (Literal(..), MeasureOp(..), LCs(), UnLCs ())
import Language.Hakaru.Syntax.IClasses

import Data.Text
import Text.Parsec (SourcePos)

-- N.B., because we're not using the ABT's trick for implementing a HOAS API, we can make the identifier strict.
data Name = Name {-# UNPACK #-}!N.Nat {-# UNPACK #-}!Text
    deriving (Read, Show, Eq, Ord)

nameID :: Name -> N.Nat
nameID (Name i _) = i

hintID :: Name -> Text
hintID (Name _ t) = t

----------------------------------------------------------------
----------------------------------------------------------------

type Name' = Text

data Branch' a
    = Branch'  (Pattern' Name') (AST' a)
    | Branch'' (Pattern' Name)  (AST' a)
    deriving (Eq, Show)

data Pattern' a
    = PVar'  a
    | PWild'
    | PData' (PDatum a)
    deriving (Eq, Show)

data PDatum a = DV Name' [Pattern' a]
    deriving (Eq, Show)

-- Meta stores start and end position for AST in source code
data Meta = Meta !SourcePos !SourcePos
    deriving (Eq, Show)

data Literal'
    = Nat  Integer
    | Int  Integer
    | Prob Rational
    | Real Rational
    deriving (Eq, Show)

data NaryOp
    = And | Or   | Xor
    | Iff | Min  | Max 
    | Sum | Prod
    deriving (Eq, Show)

data ArrayOp = Index_ | Size | Reduce

data TypeAST'
    = TypeVar Name'
    | TypeApp Name'    [TypeAST']
    | TypeFun TypeAST' TypeAST'
    deriving (Eq, Show)

data AST' a
    = Var a
    | Lam a TypeAST' (AST' a) 
    | App (AST' a) (AST' a)
    | Let a    (AST' a) (AST' a)
    | If  (AST' a) (AST' a) (AST' a)
    | Ann (AST' a) TypeAST'
    | Infinity'
    | NegInfinity'
    | ULiteral Literal'
    | NaryOp NaryOp [AST' a]
    | Unit
    | Empty
    | Pair (AST' a) (AST' a)
    | Array a (AST' a) (AST' a)
    | Index (AST' a) (AST' a)
    | Case  (AST' a) [(Branch' a)] -- match
    | Dirac (AST' a)
    | Bind  a  (AST' a) (AST' a)
    | Plate a  (AST' a) (AST' a)
    | Chain a  (AST' a) (AST' a) (AST' a)
    | Integrate a (AST' a) (AST' a) (AST' a)
    | Summate   a (AST' a) (AST' a) (AST' a)
    | Expect a (AST' a) (AST' a)
    | Observe  (AST' a) (AST' a)
    | Msum  [AST' a]
    | Data  a [TypeAST']
    | WithMeta (AST' a) Meta
    deriving (Eq, Show)

----------------------------------------------------------------
----------------------------------------------------------------

val :: Literal' -> Some1 Literal
val (Nat  n) = Some1 $ LNat  (N.unsafeNatural n)
val (Int  n) = Some1 $ LInt  n
val (Prob n) = Some1 $ LProb (N.unsafeNonNegativeRational n)
val (Real n) = Some1 $ LReal n

data PrimOp
    = Not | Impl | Diff   | Nand | Nor
    | Pi
    | Sin        | Cos    | Tan
    | Asin       | Acos   | Atan
    | Sinh       | Cosh   | Tanh
    | Asinh      | Acosh  | Atanh
    | RealPow    | NatPow
    | Exp        | Log
    | Infinity   | NegativeInfinity
    | GammaFunc  | BetaFunc
    | Equal      | Less
    | Negate     | Recip
    | Abs        | Signum | NatRoot | Erf
    deriving (Eq, Show)

data SealedOp op where
    SealedOp
        :: (typs ~ UnLCs args, args ~ LCs typs)
        => !(op typs a)
        -> SealedOp op

data SSing =
    forall (a :: Hakaru). SSing !(Sing a)

data Branch = Branch Pattern AST

data Pattern
    = PWild
    | PVar Name
    | PDatum Text PCode

data PFun
    = PKonst Pattern
    | PIdent Pattern

data PStruct
    = PEt PFun PStruct
    | PDone

data PCode
    = PInr PCode
    | PInl PStruct

infixr 7 `Et`, `PEt`

data DFun
    = Konst AST
    | Ident AST

data DStruct
    = Et DFun DStruct
    | Done

data DCode
    = Inr DCode
    | Inl DStruct

data Datum = Datum Text DCode

data AST
    = Var_        Name
    | Lam_        Name SSing AST
    | App_        AST        AST
    | Let_        Name       AST AST
    | Ann_        AST SSing
    | CoerceTo_   (Some2 Coercion) AST
    | UnsafeTo_   (Some2 Coercion) AST
    | PrimOp_     PrimOp  [AST]
    | ArrayOp_    ArrayOp [AST]
    | NaryOp_     NaryOp  [AST]
    | Literal_    (Some1 Literal)
    | Empty_
    | Pair_       AST AST
    | Array_      AST Name AST
    | Datum_      Datum 
    | Case_       AST [Branch]
    | MeasureOp_  (SealedOp MeasureOp) [AST]
    | Dirac_      AST
    | MBind_      Name    AST AST
    | Plate_      Name    AST AST
    | Chain_      Name    AST AST AST
    | Integrate_  Name    AST AST AST
    | Summate_    Name    AST AST AST
    | Expect_     Name    AST AST
    | Observe_            AST AST
    | Superpose_  [(AST, AST)]
    | Reject_

----------------------------------------------------------------
---------------------------------------------------------- fin.
