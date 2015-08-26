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
     Nat  Integer Meta
   | Int  Integer Meta
   | Prob Double  Meta
   | Real Double  Meta
 deriving (Eq, Show)

data AST' a =
     Var Name
   | Op a
   | Lam Name (AST' a) 
   | App (AST' a) (AST' a)
   | Let Name (AST' a) (AST' a)
--    | Ann (AST' a) Hakaru
   | Value Value'
   | Empty
--    | Case  (AST' a) [(Branch' a)]
   | Bind  Name (AST' a) (AST' a)
--    | Superpose [((AST' a), (AST' a))]
--    | Data Sop
 deriving (Eq, Show)
