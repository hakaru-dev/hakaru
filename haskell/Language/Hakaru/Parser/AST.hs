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
    (PrimOp(..), Literal(..), ArrayOp(..),
     MeasureOp(..), LCs(), UnLCs ())
import Language.Hakaru.Syntax.Variable (Variable(..))
import Language.Hakaru.Syntax.IClasses

import Data.Text
import Text.Parsec (SourcePos)

-- N.B., because we're not using the ABT's trick for implementing a HOAS API, we can make the identifier strict.
data Name = Name {-# UNPACK #-}!N.Nat {-# UNPACK #-}!Text
    deriving (Read, Show, Eq, Ord)

makeVar :: Name -> Sing a -> Variable a
makeVar name typ =
    Variable (hintID name) (nameID name) typ

nameID :: Name -> N.Nat
nameID (Name i _) = i

hintID :: Name -> Text
hintID (Name _ t) = t

data SealedOp op where
    SealedOp
        :: (typs ~ UnLCs args, args ~ LCs typs)
        => !(op typs a)
        -> SealedOp op

data SSing =
    forall (a :: Hakaru). SSing !(Sing a)

type Name' = Text

data Branch' a
    = Branch'  (Pattern' Text) (AST' a)
    | Branch'' (Pattern' Name) (AST' a)
    deriving (Eq, Show)

data Pattern' a
    = PVar'  a
    | PWild'
    | PData' (PDatum a)
    deriving (Eq, Show)

data PDatum a = DV Text [Pattern' a]
    deriving (Eq, Show)

-- Meta stores start and end position for AST in source code
data Meta = Meta !SourcePos !SourcePos
    deriving (Eq, Show)

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

data Literal'
    = Nat  Int
    | Int  Int
    | Prob Double
    | Real Double
    deriving (Eq, Show)

data NaryOp'
    = And' | Or' | Xor'
    | Iff' | Min'| Max' 
    | Sum' | Prod'
    deriving (Eq, Show)

val :: Literal' -> Some1 Literal
val (Nat  n) = Some1 $ LNat  (N.unsafeNatural $ fromIntegral n) -- TODO: clean up
val (Int  n) = Some1 $ LInt  (fromIntegral n) -- TODO: clean up
val (Prob n) = Some1 $ LProb (N.unsafeNonNegativeRational $ toRational n) -- BUG: parse a Rational in the first place!
val (Real n) = Some1 $ LReal (toRational   n) -- BUG: parse a Rational in the first place!

data TypeAST'
    = TypeVar Text
    | TypeApp Text [TypeAST']
    | TypeFun TypeAST' TypeAST'
    deriving (Eq, Show)

data AST' a
    = Var a
    | Lam a    (AST' a) 
    | App (AST' a) (AST' a)
    | Let a    (AST' a) (AST' a)
    | If  (AST' a) (AST' a) (AST' a)
    | Ann (AST' a) TypeAST'
    | Infinity
    | NegInfinity
    | ULiteral Literal'
    | NaryOp NaryOp' (AST' a) (AST' a)
    | Empty
    | Array a (AST' a) (AST' a)
    | Case  (AST' a) [(Branch' a)] -- match
    | Dirac (AST' a)
    | Bind  a (AST' a) (AST' a)
    | Expect a (AST' a) (AST' a)
    | Data  a [TypeAST']
    | WithMeta (AST' a) Meta
    deriving (Eq, Show)

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

data AST
    = Var_        Name
    | Lam_        Name      AST
    | App_        AST       AST
    | Let_        Name      AST AST
    | Ann_        AST SSing
    | CoerceTo_   (Some2 Coercion) AST
    | UnsafeTo_   (Some2 Coercion) AST
    | PrimOp_     (SealedOp PrimOp)  [AST]
    | ArrayOp_    (SealedOp ArrayOp) [AST]
    | NaryOp_     NaryOp'  [AST]
    | Literal_    (Some1 Literal)
    | Empty_
    | Array_      AST Name AST -- not sure should binding form
    | Datum_      Datum 
    | Case_       AST [Branch]
    | MeasureOp_  (SealedOp MeasureOp) [AST]
    | Dirac_      AST
    | MBind_      Name    AST AST
    | Expect_     Name    AST AST
    | Superpose_  [(AST, AST)]
