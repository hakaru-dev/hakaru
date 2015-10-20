{-# LANGUAGE RankNTypes, GADTs, ExistentialQuantification, StandaloneDeriving #-}
module Language.Hakaru.Parser.AST where

import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.AST()
import Data.Text
import Text.Parsec (SourcePos)

type Name = Text

-- data Branch' a = Branch' Pattern' (AST' a)

-- Meta stores start and end position for AST in source code
newtype Meta = Meta (SourcePos, SourcePos) deriving (Eq, Show)

data Sop = Sop [[Sop]] | V Value'
data Value' =
     Nat  Integer
   | Int  Integer
   | Prob Double
   | Real Double
 -- | Datum Sop
 deriving (Eq)

data Symbol' =
     Fix
   | CoerceTo
   | UnsafeFrom 
   | PrimOp
   | NaryOp
   | Datum
   | Array
   | Empty'
   | MeasureOp
   | MBind
   | Plus

type SymbolTable = [(Text, Symbol')]

data AST' a =
     Var Name
   | Op a
   | Lam Name (AST' a) 
   | App (AST' a) (AST' a)
   | Let Name (AST' a) (AST' a)
   | If (AST' a) (AST' a) (AST' a)
   | Ann (AST' a) (AST' a)
   -- These should probably be in their own TypeAST
   | TypeApp (AST' a) (AST' a)
   | TypeFun (AST' a) (AST' a)
   | TypeOp  a
   | TypeVar Name

   | Value Value'
   | Empty
--    | Case  (AST' a) [(Branch' a)] -- match
   | Bind  Name (AST' a) (AST' a)
--    | Data Sop
   | WithMeta (AST' a) Meta

data PrimOp' a =
     Not'        (AST a)
   | Impl'       (AST a) (AST a)
   | Diff'       (AST a) (AST a)
   | Nand'       (AST a) (AST a)
   | Nor'        (AST a) (AST a)
   | Pi'        
   | Sin'        (AST a)
   | Cos'        (AST a)
   | Tan'        (AST a)
   | Asin'       (AST a)
   | Acos'       (AST a)
   | Atan'       (AST a)
   | Sinh'       (AST a)
   | Cosh'       (AST a)
   | Tanh'       (AST a)
   | Asinh'      (AST a)
   | Acosh'      (AST a)
   | Atanh'      (AST a)
   | RealPow'    (AST a) (AST a)
   | Exp'        (AST a)
   | Log'        (AST a)
   | Infinity'
   | NegativeInfinity'
   | GammaFunc' (AST a)
   | BetaFunc'  (AST a)
   | Integrate' (AST a) (AST a) (AST a)
   | Summate'   (AST a) (AST a) (AST a)
   | Index'     (AST a) (AST a)
   | Size'      (AST a)
   | Reduce'    (AST a) (AST a)
   | Equal'     (AST a) (AST a)
   | Less'      (AST a) (AST a)
   | NatPow'    (AST a) (AST a)
   | Negate'    (AST a)
   | Abs'       (AST a)
   | Signum'    (AST a)
   | Recip'     (AST a)
   | NatRoot'   (AST a) (AST a)
   | Erf'       (AST a)

data NaryOp' =
     And'
   | Or'
   | Xor'
   | Iff'
   | Min' 
   | Max' 
   | Sum' 
   | Prod'

data MeasureOp' a =
     Lebesgue'
   | Counting'
   | Categorical' (AST a)
   | Uniform'     (AST a) (AST a)
   | Normal'      (AST a) (AST a)
   | Poisson'     (AST a) (AST a)
   | Gamma'       (AST a) (AST a)
   | Beta'        (AST a) (AST a)
   | DP'          (AST a) (AST a)
   | Plate'       (AST a)
   | Chain'       (AST a) (AST a)

data AST a =        
     Lam_        (AST a) (AST a)
   | Fix_        (AST a)
   | Let_        (AST a) (AST a) (AST a)
   | Ann_        (AST a) (AST a)
   | CoerceTo_   (AST a) (AST a)
   | UnsafeFrom_ (AST a) (AST a)
   | PrimOp_     (AST a) (AST a)
   | NaryOp_     NaryOp' (AST a) (AST a)
   | Value_      (AST a)
   | Empty_
   | Array_      (AST a) (AST a)
   | Datum_      (AST a)
   | Case_       (AST a) (AST a)
   | MeasureOp_  (MeasureOp' a)
   | MBind_      (AST a) (AST a) (AST a)
   | Superpose_  (AST a)
   | Lub_        (AST a)


deriving instance Eq a => Eq (AST' a)
deriving instance Show a => Show (AST' a)
deriving instance Show Value'
