{-# LANGUAGE RankNTypes,
             GADTs,
             Rank2Types,
             DataKinds,
             PolyKinds,
             ExistentialQuantification,
             StandaloneDeriving #-}
module Language.Hakaru.Parser.AST where

import qualified Language.Hakaru.Syntax.Nat as N
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Coercion
import Language.Hakaru.Syntax.AST    (PrimOp(..),
                                      NaryOp(..),
                                      Value(..),
                                      MeasureOp(..),
                                      LCs(..),
                                      UnLCs (..))
import Language.Hakaru.Syntax.Sing
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

data SealedOp op where
     SealedOp
      :: (typs ~ UnLCs args, args ~ LCs typs)
      => !(Sing args)
      -> !(op typs a)
      -> SealedOp op

type Name' = Text

data Branch'  a =
     Branch' (Pattern' a) (AST' a)
     deriving (Eq, Show)

data Pattern' a =
     PVar'  a
   | PWild'
   | PData' (Datum' a)
   deriving (Eq, Show)

-- Meta stores start and end position for AST in source code
newtype Meta = Meta (SourcePos, SourcePos) deriving (Eq, Show)

data Datum' a = DV a [a] deriving (Eq, Show)

data Value' =
     Nat  Int
   | Int  Int
   | Prob Double
   | Real Double
   | Datum (Datum' Name')
 deriving (Eq)

data Symbol' =
     Fix
   | True' | False'
   | CoerceTo
   | UnsafeFrom 
   | PrimOp
   | NaryOp
   | Array
   | Empty'
   | MeasureOp'
   | MBind
   | Plus

type SymbolTable = [(Text, Symbol')]

data TypeAST' a =
     TypeVar a
   | TypeApp (TypeAST' a) (TypeAST' a)
   | TypeFun (TypeAST' a) (TypeAST' a)

data AST' a =
     Var a
   | Lam Name'    (AST' a) 
   | App (AST' a) (AST' a)
   | Let Name'    (AST' a) (AST' a)
   | If  (AST' a) (AST' a) (AST' a)
   | Ann (AST' a) (TypeAST' a)
   | UValue Value'
   | Empty
   | Case  (AST' a) [(Branch' a)] -- match
   | Bind  Name' (AST' a) (AST' a)
   | Data  Name' [TypeAST' a]
   | WithMeta (AST' a) Meta

data PrimOp' =
     Not'        
   | Impl'       
   | Diff'       
   | Nand'  | Nor'        
   | Pi'        
   | Sin'   | Cos'   | Tan'        
   | Asin'  | Acos'  | Atan'       
   | Sinh'  | Cosh'  | Tanh'       
   | Asinh' | Acosh' | Atanh'      
   | RealPow'    
   | Exp'   | Log'        
   | Infinity'  | NegativeInfinity'
   | GammaFunc' | BetaFunc' 
   | Integrate' | Summate'  
   | Index'    
   | Size'     
   | Reduce'   
   | Equal'     | Less'     
   | NatPow'   
   | Negate'   
   | Abs'      
   | Signum'   
   | Recip'    
   | NatRoot'  
   | Erf'      

data NaryOp' =
     And'
   | Or'
   | Xor'
   | Iff'
   | Min' 
   | Max' 
   | Sum' 
   | Prod'

data MeasureOp_ =
     Lebesgue'
   | Counting'
   | Categorical'
   | Uniform'    
   | Normal'     
   | Poisson'    
   | Gamma'      
   | Beta'       
   | DP'         
   | Plate'      
   | Chain'      

data Branch a = Branch (Pattern a) (AST a)
data Pattern a =
     PVar (AST a)
   | PWild
   | PData [AST a]

data AST a =
     Var_        Name
   | Lam_        Name    (AST a)
   | App_        (AST a) (AST a)
   | Fix_        Name    (AST a)
   | Let_        Name    (AST a) (AST a)
   | Ann_        (AST a) Hakaru
   | CoerceTo_   (Sealed2 Coercion) (AST a)
   | UnsafeFrom_ (Sealed2 Coercion) (AST a)
   | PrimOp_     (SealedOp PrimOp) [AST a]
   | NaryOp_     (Sealed1 NaryOp)  [AST a]
   | Value_      (Sealed1 Value)
   | Empty_
   | Array_      (AST a) (AST a)
   | Datum_      (AST a)
   | Case_       (AST a) [Branch a]
   | MeasureOp_  (SealedOp MeasureOp) [AST a]
   | MBind_      Name    (AST a) (AST a)
   | Superpose_  (AST a)
   | Lub_        (AST a)


deriving instance Eq a => Eq (AST' a)
deriving instance Show a => Show (AST' a)
deriving instance Eq a => Eq (TypeAST' a)
deriving instance Show a => Show (TypeAST' a)
deriving instance Show Value'
