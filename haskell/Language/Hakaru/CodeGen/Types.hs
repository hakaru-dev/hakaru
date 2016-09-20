{-# LANGUAGE DataKinds,
             FlexibleContexts,
             GADTs,
             KindSignatures #-}

----------------------------------------------------------------
--                                                    2016.07.11
-- |
-- Module      :  Language.Hakaru.CodeGen.Types
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  zsulliva@indiana.edu
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Provides tools for building C Types from Hakaru types
--
----------------------------------------------------------------

module Language.Hakaru.CodeGen.Types
  ( buildDeclaration

  -- tools for building C types
  , typeDeclaration
  , typePtrDeclaration
  , arrayDeclaration
  , arrayName
  , arrayStruct
  , datumDeclaration
  , datumName
  , datumStruct
  , functionDef

  , datumSum
  , datumProd

  , buildType
  , mkDecl
  , mkPtrDecl
  , buildStruct
  , buildUnion

  , intDecl
  , doubleDecl
  , doublePtr
  , intPtr
  , boolTyp
  , binaryOp
  ) where

import Control.Monad.State

import Language.Hakaru.Syntax.AST
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Types.Sing
import Language.Hakaru.CodeGen.AST

import Prelude hiding (exp,log,sqrt)

buildDeclaration :: CTypeSpec -> Ident -> CDecl
buildDeclaration ctyp ident =
  CDecl [ CTypeSpec ctyp ]
        [( CDeclr Nothing [ CDDeclrIdent ident ]
         , Nothing)]

typeDeclaration :: Sing (a :: Hakaru) -> Ident -> CDecl
typeDeclaration typ ident =
  CDecl [CTypeSpec $ buildType typ]
        [( CDeclr Nothing [ CDDeclrIdent ident ]
         , Nothing)]

typePtrDeclaration :: Sing (a :: Hakaru) -> Ident -> CDecl
typePtrDeclaration typ ident =
  CDecl [CTypeSpec $ buildType typ]
        [( CDeclr (Just $ CPtrDeclr [])
                  [ CDDeclrIdent ident ]
         , Nothing)]

--------------------------------------------------------------------------------
--

arrayName :: Sing (a :: Hakaru) -> String
arrayName SInt  = "arrayInt"
arrayName SNat  = "arrayNat"
arrayName SReal = "arrayReal"
arrayName SProb = "arrayProb"
arrayName t    = error $ "arrayName: cannot make array from type: " ++ show t

arrayStruct :: Sing (a :: Hakaru) -> CExtDecl
arrayStruct t = CDeclExt (CDecl [CTypeSpec $ arrayStruct' t] [])

arrayStruct' :: Sing (a :: Hakaru) -> CTypeSpec
arrayStruct' t = aStruct
  where aSize   = buildDeclaration CInt (Ident "size")
        aData   = typePtrDeclaration t (Ident "data")
        aStruct = buildStruct (Just . Ident . arrayName $ t) [aSize,aData]


arrayDeclaration
  :: Sing (a :: Hakaru)
  -> Ident
  -> CDecl
arrayDeclaration typ = buildDeclaration (callStruct (arrayName typ))

--------------------------------------------------------------------------------
-- | datumProd and datumSum use a store of names, which needs to match up with
-- the names used when they are assigned and printed
-- datumDeclaration declares struct internally
-- datumStruct declares struct definitions externally

-- | datumName provides a unique name to identify a struct type
datumName :: Sing (a :: [[HakaruFun]]) -> String
datumName SVoid = "V"
datumName (SPlus prodD sumD) = concat ["S",datumName' prodD,datumName sumD]
  where datumName' :: Sing (a :: [HakaruFun]) -> String
        datumName' SDone = "U"
        datumName' (SEt (SKonst x) prod') = concat ["S",tail . show $ x,datumName' prod']
        datumName' (SEt SIdent _)         = error "TODO: datumName of SIdent"

datumNames :: [String]
datumNames = filter (\n -> not $ elem (head n) ['0'..'9']) names
  where base = ['0'..'9'] ++ ['a'..'z']
        names = [[x] | x <- base] `mplus` (do n <- names
                                              [n++[x] | x <- base])

datumStruct :: (Sing (HData' t)) -> CExtDecl
datumStruct (SData _ typ) = CDeclExt $ datumSum typ (Ident (datumName typ))

datumDeclaration
  :: (Sing (HData' t))
  -> Ident
  -> CDecl
datumDeclaration (SData _ typ) = buildDeclaration (callStruct (datumName typ))

datumSum :: Sing (a :: [[HakaruFun]]) -> Ident -> CDecl
datumSum funs ident =
  let declrs = fst $ runState (datumSum' funs) datumNames
      union  = buildDeclaration (buildUnion declrs) (Ident "sum")
      index  = buildDeclaration CInt (Ident "index")
      struct = buildStruct (Just ident) $ case declrs of
                                            [] -> [index]
                                            _  -> [index,union]
  in CDecl [ CTypeSpec struct ] []

datumSum' :: Sing (a :: [[HakaruFun]]) -> State [String] [CDecl]
datumSum' SVoid          = return []
datumSum' (SPlus prod rest) =
  do (name:names) <- get
     put names
     let ident = Ident name
         mdecl = datumProd prod ident
     rest' <- datumSum' rest
     case mdecl of
       Nothing -> return rest'
       Just d  -> return $ [d] ++ rest'


datumProd :: Sing (a :: [HakaruFun]) -> Ident -> Maybe CDecl
datumProd SDone _     = Nothing
datumProd funs ident  =
  let declrs = fst $ runState (datumProd' funs) datumNames
  in  Just $ buildDeclaration (buildStruct Nothing $ declrs) ident

-- datumProd uses a store of names, which needs to match up with the names used
-- when they are assigned as well as printed
datumProd' :: Sing (a :: [HakaruFun]) -> State [String] [CDecl]
datumProd' SDone                 = return []
datumProd' (SEt (SKonst t) rest) =
  do (name:names) <- get
     put names
     let ident = Ident name
         decl  = typeDeclaration t ident
     rest' <- datumProd' rest
     return $ [decl] ++ rest'
datumProd' (SEt SIdent _) = error "TODO: datumProd' SIdent"

----------------------------------------------------------------

functionDef
  :: Sing (a :: Hakaru)
  -> Ident
  -> [CDecl]
  -> [CDecl]
  -> [CStat]
  -> CFunDef
functionDef typ ident argDecls internalDecls stmts =
  CFunDef [CTypeSpec . buildType $ typ]
          (CDeclr Nothing [ CDDeclrIdent ident ])
          argDecls
          (CCompound ((fmap CBlockDecl internalDecls) ++ (fmap CBlockStat stmts)))

----------------------------------------------------------------
-- | buildType function do the work of describing how the Hakaru
-- type will be stored in memory. Arrays needed their own
-- declaration function for their arity
buildType :: Sing (a :: Hakaru) -> CTypeSpec
buildType SInt         = CInt
buildType SNat         = CInt
buildType SProb        = CDouble
buildType SReal        = CDouble
buildType (SMeasure x) = buildType x
buildType (SArray t)   = callStruct $ arrayName t
buildType (SFun _ x)   = buildType x -- build type the function returns
buildType (SData _ t)  = callStruct $ datumName t


-- these mk...Decl functions are used in coersions
mkDecl :: CTypeSpec -> CDecl
mkDecl t = CDecl [CTypeSpec t] []

mkPtrDecl :: CTypeSpec -> CDecl
mkPtrDecl t = CDecl [CTypeSpec t]
                    [( CDeclr (Just $ CPtrDeclr []) []
                     , Nothing )]

buildStruct :: Maybe Ident -> [CDecl] -> CTypeSpec
buildStruct mi decls =
  CSUType (CSUSpec CStructTag mi decls)

-- | callStruct will give the type spec calling a struct we have already declared externally
callStruct :: String -> CTypeSpec
callStruct name =
  CSUType (CSUSpec CStructTag (Just (Ident name)) [])

buildUnion :: [CDecl] -> CTypeSpec
buildUnion decls =
 CSUType (CSUSpec CUnionTag Nothing decls)


intDecl,doubleDecl :: CDecl
intDecl    = mkDecl CInt
doubleDecl = mkDecl CDouble

intPtr,doublePtr :: CDecl
intPtr    = mkPtrDecl CInt
doublePtr = mkPtrDecl CDouble

boolTyp :: CDecl
boolTyp =
  CDecl [CTypeSpec
          (CSUType
            (CSUSpec CStructTag
                     (Just (Ident "bool"))
                     [buildDeclaration CInt (Ident "index")]))]
        []



binaryOp :: NaryOp a -> CExpr -> CExpr -> CExpr
binaryOp (Sum HSemiring_Prob)  a b = CBinary CAddOp (exp a) (exp b)
binaryOp (Prod HSemiring_Prob) a b = CBinary CAddOp a b
binaryOp (Sum _)               a b = CBinary CAddOp a b
binaryOp (Prod _)              a b = CBinary CMulOp a b
-- vvv Operations on bools, keeping in mind that in Hakaru-C: 0 is true and 1 is false
binaryOp And                   a b = CUnary CNegOp (CBinary CEqOp  a b) -- still wrong
binaryOp Or                    a b = CBinary CAndOp a b                 -- still wrong
binaryOp Xor                   a b = CBinary CLorOp a b                 -- still wrong
binaryOp x _ _ = error $ "TODO: binaryOp " ++ show x
