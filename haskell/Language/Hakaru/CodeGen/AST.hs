--------------------------------------------------------------------------------
--                                                                 2016.09.08
-- |
-- Module      :  Language.Hakaru.CodeGen.AST
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  zsulliva@indiana.edu
-- Stability   :  experimental
-- Portability :  GHC-only
--
--   An AST for the C Family and preprocessor
-- Much of this is based on Manuel M T Chakravarty and Benedikt
-- Hubar's "language-c" package
--
--------------------------------------------------------------------------------

module Language.Hakaru.CodeGen.AST
  ( Preprocessor(..), Ident(..), CAST(..), CExtDecl(..), CFunDef(..)

  -- declaration constructors
  , CDecl(..), CDeclr(..), CDeclSpec(..), CStorageSpec(..), CTypeQual(..)
  , CDirectDeclr(..), CTypeSpec(..), CSUSpec(..), CSUTag(..), CEnum(..)
  , CInit(..), CPartDesig(..), CFunSpec(..), CPtrDeclr(..)

  -- statements and expression constructors
  , CStat(..), CCompoundBlockItem(..), CExpr(..), CConst(..), CUnaryOp(..)
  , CBinaryOp(..), CAssignOp(..)

  -- infix and smart constructors
  , (.>.), (.<.), (.==.), (.||.), (.&&.), (.*.), (./.), (.-.), (.+.), (.=.)
  , (.+=.),(.*=.), (.<=.), (.>=.)
  , indirect, address, intE, floatE, stringE, mkUnary
  , exp, expm1, log, log1p, sqrt, rand
  ) where

import Prelude hiding (exp,log,sqrt)


-- very rough AST for preprocessor
data Preprocessor
  = PPDefine  String String
  | PPInclude String
  | PPUndef   String
  | PPIf      String
  | PPIfDef   String
  | PPIfNDef  String
  | PPElse    String
  | PPElif    String
  | PPEndif   String
  | PPError   String
  | PPPragma  [String]
  deriving (Show, Eq, Ord)


data Ident
 = Ident String
 deriving (Show, Eq, Ord)


--------------------------------------------------------------------------------
-- Top Level
--------------------------------------------------------------------------------

data CAST
  = CAST [CExtDecl]
  deriving (Show, Eq, Ord)


data CExtDecl
  = CDeclExt    CDecl
  | CFunDefExt  CFunDef
  | CCommentExt String
  | CPPExt      Preprocessor
  deriving (Show, Eq, Ord)

data CFunDef
  = CFunDef [CDeclSpec] CDeclr [CDecl] CStat
  deriving (Show, Eq, Ord)

--------------------------------------------------------------------------------
-- CDeclarations

data CDecl
  = CDecl [CDeclSpec] [(CDeclr, Maybe CInit)]
  deriving (Show, Eq, Ord)

------------
-- specifiers

data CDeclSpec
  = CStorageSpec CStorageSpec
  | CTypeSpec    CTypeSpec
  | CTypeQual    CTypeQual
  | CFunSpec     CFunSpec
  deriving (Show, Eq, Ord)

data CFunSpec = Inline
  deriving (Show, Eq, Ord)

data CStorageSpec
  = CTypeDef
  | CExtern
  | CStatic
  | CAuto
  | CRegister
  deriving (Show, Eq, Ord)

data CTypeQual
  = CConstQual
  | CVolatQual
  deriving (Show, Eq, Ord)

data CTypeSpec
  = CVoid
  | CChar
  | CShort
  | CInt
  | CLong
  | CFloat
  | CDouble
  | CSigned
  | CUnsigned
  | CSUType      CSUSpec
  | CTypeDefType Ident
  | CEnumType    CEnum
  deriving (Show, Eq, Ord)

data CSUSpec
  = CSUSpec CSUTag (Maybe Ident) [CDecl]
  deriving (Show, Eq, Ord)

data CSUTag
  = CStructTag
  | CUnionTag
  deriving (Show, Eq, Ord)

data CEnum
  = CEnum (Maybe Ident) [(Ident, Maybe CExpr)]
  deriving (Show, Eq, Ord)

-----------
-- declarators

data CDeclr
  = CDeclr (Maybe CPtrDeclr) [CDirectDeclr]
  deriving (Show, Eq, Ord)

data CPtrDeclr = CPtrDeclr [CTypeQual]
  deriving (Show, Eq, Ord)

-- this is incomplete
data CDirectDeclr
  = CDDeclrIdent Ident
  | CDDeclrArr   CDirectDeclr CExpr
  | CDDeclrFun   CDirectDeclr [CTypeSpec]
  deriving (Show, Eq, Ord)

-----------
-- initializers
data CInit
  = CInitExpr CExpr
  | CInitList [([CPartDesig], CInit)]
  deriving (Show, Eq, Ord)

data CPartDesig
  = CArrDesig    CExpr
  | CMemberDesig CExpr
  deriving (Show, Eq, Ord)

--------------------------------------------------------------------------------
-- CStatments

data CStat
  = CLabel    Ident CStat
  | CGoto     Ident
  | CSwitch   CExpr CStat
  | CCase     CExpr CStat
  | CDefault  CStat
  | CExpr     (Maybe CExpr)
  | CCompound [CCompoundBlockItem]
  | CIf       CExpr CStat (Maybe CStat)
  | CWhile    CExpr CStat Bool
  | CFor      (Maybe CExpr) (Maybe CExpr) (Maybe CExpr) CStat
  | CCont
  | CBreak
  | CReturn   (Maybe CExpr)
  | CComment  String
  | CPPStat   Preprocessor
  deriving (Show, Eq, Ord)

data CCompoundBlockItem
  = CBlockStat CStat
  | CBlockDecl CDecl
  deriving (Show, Eq, Ord)

--------------------------------------------------------------------------------
-- CExpressions

data CExpr
  = CComma       [CExpr]
  | CAssign      CAssignOp CExpr CExpr
  | CCond        CExpr CExpr CExpr
  | CBinary      CBinaryOp CExpr CExpr
  | CCast        CDecl CExpr
  | CUnary       CUnaryOp CExpr
  | CSizeOfExpr  CExpr
  | CSizeOfType  CDecl
  | CIndex       CExpr CExpr
  | CCall        CExpr [CExpr]
  | CMember      CExpr Ident Bool
  | CVar         Ident
  | CConstant    CConst
  | CCompoundLit CDecl CInit
  deriving (Show, Eq, Ord)


data CAssignOp
  = CAssignOp
  | CMulAssOp
  | CDivAssOp
  | CRmdAssOp
  | CAddAssOp
  | CSubAssOp
  | CShlAssOp
  | CShrAssOp
  | CAndAssOp
  | CXorAssOp
  | COrAssOp
  deriving (Show, Eq, Ord)


data CBinaryOp
  = CMulOp
  | CDivOp
  | CRmdOp
  | CAddOp
  | CSubOp
  | CShlOp
  | CShrOp
  | CLeOp
  | CGrOp
  | CLeqOp
  | CGeqOp
  | CEqOp
  | CNeqOp
  | CAndOp
  | CXorOp
  | COrOp
  | CLndOp
  | CLorOp
  deriving (Show, Eq, Ord)


data CUnaryOp
  = CPreIncOp
  | CPreDecOp
  | CPostIncOp
  | CPostDecOp
  | CAdrOp
  | CIndOp
  | CPlusOp
  | CMinOp
  | CCompOp
  | CNegOp
  deriving (Show, Eq, Ord)


data CConst
  = CIntConst    Integer
  | CCharConst   Char
  | CFloatConst  Float
  | CStringConst String
  deriving (Show, Eq, Ord)


--------------------------------------------------------------------------------
-- Infix and Smart Constructors

(.<.),(.>.),(.==.),(.||.),(.&&.),(.*.),(./.),(.-.),(.+.),(.=.),(.+=.),(.*=.),(.<=.),(.>=.)
  :: CExpr -> CExpr -> CExpr
a .<. b  = CBinary CLeOp a b
a .>. b  = CBinary CGrOp a b
a .==. b = CBinary CEqOp a b
a .||. b = CBinary CLorOp a b
a .&&. b = CBinary CLndOp a b
a .*. b  = CBinary CMulOp a b
a ./. b  = CBinary CDivOp a b
a .-. b  = CBinary CSubOp a b
a .+. b  = CBinary CAddOp a b
a .<=. b = CBinary CLeqOp a b
a .>=. b = CBinary CGeqOp a b
a .=. b  = CAssign CAssignOp a b
a .+=. b = CAssign CAddAssOp a b
a .*=. b = CAssign CMulAssOp a b

indirect, address :: CExpr -> CExpr
indirect = CUnary CIndOp
address  = CUnary CAdrOp

intE :: Integer -> CExpr
intE = CConstant . CIntConst

floatE :: Float -> CExpr
floatE = CConstant . CFloatConst

stringE :: String -> CExpr
stringE = CConstant . CStringConst

mkUnary :: String -> CExpr -> CExpr
mkUnary s = CCall (CVar . Ident $ s) . (:[])


--------------------------------------------------------------------------------
-- math.h

exp,expm1,log,log1p,sqrt :: CExpr -> CExpr
exp   = mkUnary "exp"
expm1 = mkUnary "expm1"
log   = mkUnary "log"
log1p = mkUnary "log1p"
sqrt  = mkUnary "sqrt"

--------------------------------------------------------------------------------
-- stdlib.h

rand :: CExpr
rand = CCall (CVar . Ident $ "rand") []
