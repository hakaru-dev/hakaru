--------------------------------------------------------------------------------
--                                                                  2016.09.08
-- |
-- Module      :  Language.Hakaru.CodeGen.Pretty
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  zsulliva@indiana.edu
-- Stability   :  experimental
-- Portability :  GHC-only
--
--   A pretty printer for the CodeGen AST
--
--------------------------------------------------------------------------------

module Language.Hakaru.CodeGen.Pretty
  ( pretty
  , prettyPrint
  , Pretty
  ) where

import Text.PrettyPrint
import Language.Hakaru.CodeGen.AST

prettyPrint :: Pretty a => a -> String
prettyPrint = render . pretty

class Pretty a where
  pretty :: a -> Doc
  prettyPrec :: Int -> a -> Doc

  pretty = prettyPrec 0
  prettyPrec _ = pretty

mpretty :: Pretty a => Maybe a -> Doc
mpretty Nothing  = empty
mpretty (Just x) = pretty x

--------------------------------------------------------------------------------
-- Top Level

instance Pretty Ident where
  pretty (Ident i) = text i

instance Pretty CAST where
  pretty (CAST extdecls) = (vcat . fmap pretty $ extdecls) $$ char '\n'

instance Pretty CExtDecl where
  pretty (CDeclExt d) = pretty d <> semi
  pretty (CFunDefExt f) = pretty f
  pretty (CCommentExt s) = text "/*" <+> text s <+> text "*/"
  pretty (CPPExt p) = pretty p

instance Pretty CFunDef where
  pretty (CFunDef dspecs dr ds s) =
    vcat [ (hsep . fmap pretty $ dspecs)
           <+> pretty dr
           <>  (parens . hsep . punctuate comma . fmap pretty $ ds)
         , pretty s
         ]

--------------------------------------------------------------------------------
-- Preprocessor

instance Pretty Preprocessor where
  pretty (PPDefine n x) = hsep . fmap text $ ["#define",n,x]
  pretty (PPInclude s) = text "#include" <+> text "<" <> text s <> text ">"
  pretty (PPUndef s) = text "#undef" <+> text s
  pretty (PPIf s) = text "#if" <+> text s
  pretty (PPIfDef s) = text "#ifdef" <+> text s
  pretty (PPIfNDef s) = text "#ifndef" <+> text s
  pretty (PPElse s) = text "#else" <+> text s
  pretty (PPElif s) = text "#elif" <+> text s
  pretty (PPEndif s) = text "#endif" <+> text s
  pretty (PPError s) = text "#error" <+> text s
  pretty (PPPragma ts) = text "#pragma" <+> (hsep . fmap text $ ts)


--------------------------------------------------------------------------------
-- CDeclarations

instance Pretty CDecl where
  pretty (CDecl ds ps) =
    hsep [ hsep . fmap pretty $ ds
         , hsep . punctuate comma . fmap declarators $ ps]
    where declarators (dr, Nothing) = pretty dr
          declarators (dr, Just ilist) = pretty dr <+> text "=" <+> pretty ilist

instance Pretty CDeclr where
  pretty (CDeclr mp dds) =
    mpretty mp <+> (hsep . fmap pretty $ dds)

instance Pretty CPtrDeclr where
  pretty (CPtrDeclr ts) = text "*" <+> (hsep . fmap pretty $ ts)

instance Pretty CDirectDeclr where
  pretty (CDDeclrIdent i) = pretty i
  pretty (CDDeclrArr dd e) = pretty dd <+> (brackets . pretty $ e)
  pretty (CDDeclrFun dd ts) =
    pretty dd <+> (hsep . punctuate comma . fmap pretty $ ts)


instance Pretty CDeclSpec where
  pretty (CStorageSpec ss) = pretty ss
  pretty (CTypeSpec ts) = pretty ts
  pretty (CTypeQual tq) = pretty tq
  pretty (CFunSpec _ ) = text "inline"  -- inline is the only CFunSpec

instance Pretty CStorageSpec where
  pretty CTypeDef = text "typedef"
  pretty CExtern = text "extern"
  pretty CStatic = text "static"
  pretty CAuto = text "auto"
  pretty CRegister = text "register"

instance Pretty CTypeQual where
  pretty CConstQual = text "const"
  pretty CVolatQual = text "volatile"

instance Pretty CTypeSpec where
  pretty CVoid = text "void"
  pretty CChar = text "char"
  pretty CShort = text "short"
  pretty CInt = text "int"
  pretty CLong = text "long"
  pretty CFloat = text "float"
  pretty CDouble = text "double"
  pretty CSigned = text "signed"
  pretty CUnsigned = text "unsigned"
  pretty (CSUType cs) = pretty cs
  pretty (CTypeDefType i) = error "TODO: Pretty TypeDef"
  pretty (CEnumType e) = error "TODO: Pretty Enum"

instance Pretty CSUSpec where
  pretty (CSUSpec tag mi []) =
    pretty tag <+> mpretty mi
  pretty (CSUSpec tag mi ds) =
    pretty tag
    <+> mpretty mi
    <+> lbrace
    $$ (sep . fmap (\d -> pretty d <> semi)  $ ds)
    $$ rbrace

instance Pretty CSUTag where
  pretty CStructTag = text "struct"
  pretty CUnionTag = text "union"

instance Pretty CEnum where
  pretty (CEnum mi es) = error "TODO: Pretty Enum"

instance Pretty CInit where
  pretty (CInitExpr e) = error "TODO: Pretty Init"
  pretty (CInitList list) = error "TODO: Pretty Init list"

instance Pretty CPartDesig where
  pretty (CArrDesig e) = error "TODO: Pretty Arr Desig"
  pretty (CMemberDesig e) = error "TODO: Pretty Memdesig"


--------------------------------------------------------------------------------
-- CStatements

instance Pretty CStat where
  pretty (CLabel lId s) = pretty lId <> colon $$ nest 2 (pretty s)
  pretty (CGoto lId) = text "goto" <+> pretty lId <> semi
  pretty (CSwitch e s) = text "switch" <+> (parens . pretty $ s )
  pretty (CCase e s) = text "case" <+> pretty e <> colon $$ nest 2 (pretty s)
  pretty (CDefault s) = text "default" <> colon $$ nest 2 (pretty s)
  pretty (CExpr me) = mpretty me <> semi
  pretty (CCompound bs) =
    lbrace $+$ (nest 2 . vcat . fmap (\b -> space <> pretty b <> space) $ bs) $+$ rbrace

  pretty (CIf ce thns (Just s)) =
    text "if" <+> (pretty ce)
  pretty (CIf ce thns Nothing) =
    text "if" <+> (pretty ce) $+$ pretty thns

  pretty (CWhile ce s b) =
    if b
    then text "do" <+> pretty s <+> text "while" <+> (parens $ pretty ce) <> semi
    else text "while" <+> (parens $ pretty ce) $$ pretty s

  pretty (CFor me mce mie s) =
    text "for"
    <+> (parens . hsep . punctuate semi . fmap mpretty $ [me,mce,mie])
    $$  pretty s
  pretty CCont = text "continue" <> semi
  pretty CBreak = text "break" <> semi
  pretty (CReturn me) = text "return" <+> mpretty me  <> semi
  pretty (CComment s) = text "/*" <+> text s <+> text "*/"
  pretty (CPPStat p) = pretty p

instance Pretty CCompoundBlockItem where
  pretty (CBlockStat s) = pretty s
  pretty (CBlockDecl d) = pretty d <> semi


--------------------------------------------------------------------------------
-- CExpressions

instance Pretty CExpr where
  pretty (CComma es) = hsep . punctuate comma . fmap pretty $ es
  pretty (CAssign op le re) = pretty le <+> pretty op <+> pretty re
  pretty (CCond ce thn els) = pretty ce <+> text "?" <+> pretty thn <+> colon <+> pretty els
  pretty (CBinary op e1 e2) = parens . hsep $ [pretty e1, pretty op, pretty e2]
  pretty (CCast d e) = parens (pretty d) <> pretty e
  pretty (CUnary op e) = pretty op <> pretty e
  pretty (CSizeOfExpr e) = text "sizeof" <> (parens . pretty $ e)
  pretty (CSizeOfType d) = text "sizeof" <> (parens . pretty $ d)
  pretty (CIndex arrId ie) = pretty arrId <> (brackets . pretty $ ie)
  pretty (CCall fune es) =
    pretty fune <> (parens . hcat . punctuate comma . fmap pretty $ es)
  pretty (CMember ve memId isPtr) =
    let op = text $ if isPtr then "." else "->"
    in  pretty ve <> op <> pretty memId
  pretty (CVar varId) = pretty varId
  pretty (CConstant c) = pretty c
  pretty (CCompoundLit d init) = parens (pretty d) <> pretty init


instance Pretty CAssignOp where
  pretty CAssignOp = text "="
  pretty CMulAssOp = text "*="
  pretty CDivAssOp = text "/="
  pretty CRmdAssOp = text "%="
  pretty CAddAssOp = text "+="
  pretty CSubAssOp = text "-="
  pretty CShlAssOp = text "<<="
  pretty CShrAssOp = text ">>="
  pretty CAndAssOp = text "&="
  pretty CXorAssOp = text "^="
  pretty COrAssOp  = text "|="


instance Pretty CBinaryOp where
  pretty CMulOp = text "*"
  pretty CDivOp = text "/"
  pretty CRmdOp = text "%"
  pretty CAddOp = text "+"
  pretty CSubOp = text "-"
  pretty CShlOp = text "<<"
  pretty CShrOp = text ">>"
  pretty CLeOp  = text "<"
  pretty CGrOp  = text ">"
  pretty CLeqOp = text "<="
  pretty CGeqOp = text ">="
  pretty CEqOp  = text "=="
  pretty CNeqOp = text "!="
  pretty CAndOp = text "&"
  pretty CXorOp = text "^"
  pretty COrOp  = text "|"
  pretty CLndOp = text "&&"
  pretty CLorOp = text "||"


instance Pretty CUnaryOp where
  pretty CPreIncOp  = text "++"
  pretty CPreDecOp  = text "--"
  pretty CPostIncOp = text "++"
  pretty CPostDecOp = text "--"
  pretty CAdrOp     = text "&"
  pretty CIndOp     = text "*"
  pretty CPlusOp    = text "+"
  pretty CMinOp     = text "-"
  pretty CCompOp    = text "~"
  pretty CNegOp     = text "!"


instance Pretty CConst where
  pretty (CIntConst i)    = text . show $ i
  pretty (CCharConst c)   = char c
  pretty (CFloatConst f)  = float f
  pretty (CStringConst s) = text . show $ s
