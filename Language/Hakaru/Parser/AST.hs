{-# LANGUAGE RankNTypes,
             GADTs,
             Rank2Types,
             DataKinds,
             PolyKinds,
             ExistentialQuantification,
             StandaloneDeriving #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}

module Language.Hakaru.Parser.AST where

import qualified Language.Hakaru.Syntax.Nat as N
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Coercion
import Language.Hakaru.Syntax.AST    (PrimOp(..),
                                      Value(..),
                                      MeasureOp(..),
                                      LCs(),
                                      UnLCs ())
import Language.Hakaru.Syntax.Variable (Variable(..))
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.IClasses

import Data.Text
import qualified Data.Number.LogFloat as LF
import Text.Parsec (SourcePos)

-- N.B., because we're not using the ABT's trick for implementing a HOAS API, we can make the identifier strict.
data Name = Name {-# UNPACK #-}!N.Nat {-# UNPACK #-}!Text
    deriving (Read, Show, Eq, Ord)

makeVar :: Name ->  Sing a -> Variable a
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

data SSing where 
     SSing :: forall (a :: Hakaru). Sing a -> SSing

type Name' = Text

data Branch'  a =
     Branch'  (Pattern' Text) (AST' a)
   | Branch'' (Pattern' Name) (AST' a)
   deriving (Eq, Show)

data Pattern' a =
     PVar'  a
   | PWild'
   | PData' (PDatum a)
   deriving (Eq, Show)

data PDatum a = DV Text [a] deriving (Eq, Show)

-- Meta stores start and end position for AST in source code
newtype Meta = Meta (SourcePos, SourcePos) deriving (Eq, Show)

infixr 7 `Et`, `PEt`

data DFun a where
     Konst :: AST a -> DFun a
     Ident :: AST a -> DFun a

data DStruct a where
     Et   :: DFun a -> DStruct a -> DStruct a
     Done :: DStruct a

data DCode a where
     Inr ::  DCode a   -> DCode a
     Inl ::  DStruct a -> DCode a

data Datum a = Datum Text (DCode a)

data Value' =
     Nat  Int
   | Int  Int
   | Prob Double
   | Real Double
   | Datum''
 deriving (Eq, Show)

data NaryOp' =
     And' | Or' | Xor'
   | Iff' | Min'| Max' 
   | Sum' | Prod'
 deriving (Eq, Show)

val :: Value' -> Some1 Value
val (Nat  n) = Some1 $ VNat (N.unsafeNat n)
val (Int  n) = Some1 $ VInt n
val (Prob n) = Some1 $ VProb (LF.logFloat n)
val (Real n) = Some1 $ VReal n

data TypeAST' =
     TypeVar Text
   | TypeApp Text [TypeAST']
   | TypeFun TypeAST' TypeAST'
 deriving (Eq, Show)

data AST' a =
     Var a
   | Lam a    (AST' a) 
   | App (AST' a) (AST' a)
   | Let a    (AST' a) (AST' a)
   | If  (AST' a) (AST' a) (AST' a)
   | Ann (AST' a) TypeAST'
   | Infinity
   | NegInfinity
   | UValue Value'
   | NaryOp NaryOp' (AST' a) (AST' a)
   | Empty
   | Case  (AST' a) [(Branch' a)] -- match
   | Dirac (AST' a)
   | Bind  a (AST' a) (AST' a)
   | Data  a [TypeAST']
   | WithMeta (AST' a) Meta

data Branch a = Branch Pattern (AST a)

data Pattern where
     PWild  :: Pattern
     PVar   :: Name -> Pattern
     PDatum :: Text -> PCode -> Pattern

data PFun where
     PKonst :: Pattern -> PFun
     PIdent :: Pattern -> PFun

data PStruct where
     PEt   :: PFun -> PStruct -> PStruct
     PDone :: PStruct

data PCode where
     PInr ::  PCode   -> PCode
     PInl ::  PStruct -> PCode

data AST a =
     Var_        Name
   | Lam_        Name    (AST a)
   | App_        (AST a) (AST a)
   | Fix_        Name    (AST a)
   | Let_        Name    (AST a) (AST a)
   | Ann_        (AST a) SSing
   | CoerceTo_   (Some2 Coercion) (AST a)
   | UnsafeTo_   (Some2 Coercion) (AST a)
   | PrimOp_     (SealedOp PrimOp) [AST a]
   | NaryOp_     NaryOp'  [AST a]
   | Value_      (Some1 Value)
   | Empty_
   | Array_      (AST a) Name (AST a) -- not sure should binding form
   | Datum_      (Datum a)
   | Case_       (AST a) [Branch a]
   | MeasureOp_  (SealedOp MeasureOp) [AST a]
   | Dirac_      (AST a)
   | MBind_      Name    (AST a) (AST a)
   | Expect_     Name    (AST a) (AST a)
   | Superpose_  [(AST a, AST a)]
   | Lub_        (AST a)


deriving instance Eq a => Eq (AST' a)
deriving instance Show a => Show (AST' a)
