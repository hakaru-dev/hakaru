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
   | Lub

type SymbolTable = [(Text, Symbol')]

data AST' a =
     Var Name
   | Op a
   | Lam Name (AST' a) 
   | App (AST' a) (AST' a)
   | Let Name (AST' a) (AST' a)
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

data AST a = Unimplmented a

deriving instance Eq a => Eq (AST' a)
deriving instance Show a => Show (AST' a)
deriving instance Show Value'


-- figure out symbols and types
symbolResolution :: SymbolTable -> AST' Text -> AST' Symbol
symbolResolution = undefined

makeAST :: AST' Symbol' -> AST Symbol'
makeAST = undefined
