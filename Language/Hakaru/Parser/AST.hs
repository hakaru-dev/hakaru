{-# LANGUAGE RankNTypes, GADTs, ExistentialQuantification, StandaloneDeriving #-}
module Language.Hakaru.Parser.AST where

import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.AST (SCon, PrimOp, NaryOp)
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

data Op' =
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
   | Lub

data AST' a =
     Var Name
   | Op a -- Op Text?
   | Lam Name (AST' a) 
   | App (AST' a) (AST' a)
   | Let Name (AST' a) (AST' a)
--    | Ann (AST' a) Hakaru
   | Value Value'
   | Empty
--    | Case  (AST' a) [(Branch' a)] -- match
   | Bind  Name (AST' a) (AST' a)
--    | Data Sop

deriving instance Eq a => Eq (AST' a)
deriving instance Show a => Show (AST' a)
deriving instance Show Value'
