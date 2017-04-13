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
  , buildDeclaration'
  , buildPtrDeclaration

  -- tools for building C types
  , typeDeclaration
  , typePtrDeclaration
  , typeName

  -- arrays
  , arrayDeclaration
  , arrayStruct
  , arraySize
  , arrayData
  , arrayPtrSize
  , arrayPtrData

  -- mdata
  , mdataDeclaration
  , mdataPtrDeclaration
  , mdataStruct
  , mdataStruct'
  , mdataWeight
  , mdataSample
  , mdataPtrWeight
  , mdataPtrSample

  -- datum
  , datumDeclaration
  , datumStruct
  , datumSum
  , datumProd

  -- functions and closures
  , functionDef
  , closureDeclaration

  , buildType
  , castTo
  , castToPtrOf
  , callStruct
  , buildStruct
  , buildUnion
  , binaryOp
  ) where

import Control.Monad.State

import Language.Hakaru.Syntax.AST
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Types.Sing
import Language.Hakaru.CodeGen.AST
import Language.Hakaru.CodeGen.Libs


buildDeclaration :: CTypeSpec -> Ident -> CDecl
buildDeclaration ctyp ident =
  CDecl [ CTypeSpec ctyp ]
        [( CDeclr Nothing (CDDeclrIdent ident)
         , Nothing)]

buildDeclaration' :: [CTypeSpec] -> Ident -> CDecl
buildDeclaration' specs ident =
  CDecl (fmap CTypeSpec specs)
        [( CDeclr Nothing (CDDeclrIdent ident)
         , Nothing)]

buildPtrDeclaration :: CTypeSpec -> Ident -> CDecl
buildPtrDeclaration ctyp ident =
  CDecl [ CTypeSpec ctyp ]
        [( CDeclr (Just $ CPtrDeclr []) (CDDeclrIdent ident)
         , Nothing)]

typeDeclaration :: Sing (a :: Hakaru) -> Ident -> CDecl
typeDeclaration typ ident =
  CDecl (fmap CTypeSpec $ buildType typ)
        [( CDeclr Nothing (CDDeclrIdent ident)
         , Nothing)]

typePtrDeclaration :: Sing (a :: Hakaru) -> Ident -> CDecl
typePtrDeclaration typ ident =
  CDecl (fmap CTypeSpec $ buildType typ)
        [( CDeclr (Just $ CPtrDeclr [])
                  (CDDeclrIdent ident)
         , Nothing)]


----------------
-- Type Names --
----------------
{-
Type names are used when constructing C structures. In most cases there is a
unique C structure name for a Hakaru type. This is not the case for functions
which are compiled into closures, which are unique to a certain context and
Hakaru type.
-}

typeName :: Sing (a :: Hakaru) -> String
typeName SInt         = "int"
typeName SNat         = "nat"
typeName SReal        = "real"
typeName SProb        = "prob"
typeName (SArray t)   = "array_" ++ typeName t
typeName (SMeasure t) = "mdata_" ++ typeName t
typeName f@(SFun _ _)  = error $ "typeName{SFun} doen't make sense: unknown context for {" ++ show f ++ "}"
typeName (SData _ t)  = "dat_" ++ datumSumName t
  where datumSumName :: Sing (a :: [[HakaruFun]]) -> String
        datumSumName SVoid = "V"
        datumSumName (SPlus p s) = datumProdName p ++ datumSumName s

        datumProdName :: Sing (a :: [HakaruFun]) -> String
        datumProdName SDone     = "D"
        datumProdName (SEt x p) = datumPrimName x ++ datumProdName p

        datumPrimName :: Sing (a :: HakaruFun) -> String
        datumPrimName SIdent = "I"
        datumPrimName (SKonst s) = "K" ++ typeName s




--------------------------------------------------------------------------------
--                                   Arrays                                   --
--------------------------------------------------------------------------------
{-
  We represent arrays as structs with an 'unsigned int' for the size and a
  pointer to a block of array elements.

  Because arrays may point to undeclared types (such as arrays of datum), we
  need to return a list of external declarations with our array type
-}

arrayStruct :: Sing (a :: Hakaru) -> CExtDecl
arrayStruct t = CDeclExt (CDecl [CTypeSpec $ arrayStruct' t] [])

arrayStruct' :: Sing (a :: Hakaru) -> CTypeSpec
arrayStruct' t = aStruct
  where aSize   = buildDeclaration CInt (Ident "size")
        aData   = typePtrDeclaration t (Ident "data")
        aStruct = buildStruct (Just . Ident . typeName . SArray $ t) [aSize,aData]


arrayDeclaration
  :: Sing (a :: Hakaru)
  -> Ident
  -> CDecl
arrayDeclaration = buildDeclaration . callStruct . typeName . SArray


arraySize :: CExpr -> CExpr
arraySize e = CMember e (Ident "size") True

arrayData :: CExpr -> CExpr
arrayData e = CMember e (Ident "data") True

arrayPtrSize :: CExpr -> CExpr
arrayPtrSize e = CMember e (Ident "size") False

arrayPtrData :: CExpr -> CExpr
arrayPtrData e = CMember e (Ident "data") False



--------------------------------------------------------------------------------
--                                  Measure Data                              --
--------------------------------------------------------------------------------
{-
  Measure datum are structures that will be used for sampling. We represent it
  as a structure with a 'double' in log-domain corresponding to the weight of
  the sample and an item of the sample type.
-}

mdataStruct :: Sing (a :: Hakaru) -> CExtDecl
mdataStruct t = CDeclExt (CDecl [CTypeSpec $ mdataStruct' t] [])

mdataStruct' :: Sing (a :: Hakaru) -> CTypeSpec
mdataStruct' t = mdStruct
  where weight = buildDeclaration CDouble (Ident "weight")
        sample = typeDeclaration t (Ident "sample")
        mdStruct = buildStruct (Just . Ident . typeName . SMeasure $ t) [weight,sample]

mdataDeclaration
  :: Sing (a :: Hakaru)
  -> Ident
  -> CDecl
mdataDeclaration = buildDeclaration . callStruct . typeName . SMeasure

mdataPtrDeclaration
  :: Sing (a :: Hakaru)
  -> Ident
  -> CDecl
mdataPtrDeclaration = buildPtrDeclaration . callStruct . typeName . SMeasure

mdataWeight :: CExpr -> CExpr
mdataWeight d = CMember d (Ident "weight") True

mdataSample :: CExpr -> CExpr
mdataSample d = CMember d (Ident "sample") True

mdataPtrWeight :: CExpr -> CExpr
mdataPtrWeight d = CMember d (Ident "weight") False

mdataPtrSample :: CExpr -> CExpr
mdataPtrSample d = CMember d (Ident "sample") False



--------------------------------------------------------------------------------
--                                     Datum                                  --
--------------------------------------------------------------------------------
{-
  In order to successfully represent Hakaru datum (Sums of Products of Hakaru
  types), we must have:

  > unique names for a given datum so if SVoid occurs twice in a program, C will
    be using the same structure

  > C structs

  > A datum may be recursive, so we will need to generate structures for all
    subtypes as well. These subtypes will need to be declared before the datum
    for the code to compile
-}

datumNames :: [String]
datumNames = filter (\n -> not $ elem (head n) ['0'..'9']) names
  where base = ['0'..'9'] ++ ['a'..'z']
        names = [[x] | x <- base] `mplus` (do n <- names
                                              [n++[x] | x <- base])


datumStruct :: (Sing (HData' t)) -> CExtDecl
datumStruct dat@(SData _ typ)
  = CDeclExt $ datumSum dat typ (Ident (typeName dat))

datumDeclaration
  :: (Sing (HData' t))
  -> Ident
  -> CDecl
datumDeclaration = buildDeclaration . callStruct . typeName

datumSum
  :: Sing (HData' t)
  -> Sing (a :: [[HakaruFun]])
  -> Ident
  -> CDecl
datumSum dat funs ident =
  let declrs = fst $ runState (datumSum' dat funs) datumNames
      union  = buildDeclaration (buildUnion declrs) (Ident "sum")
      index  = buildDeclaration CInt (Ident "index")
      struct = buildStruct (Just ident) $ case declrs of
                                            [] -> [index]
                                            _  -> [index,union]
  in CDecl [ CTypeSpec struct ] []

datumSum'
  :: Sing (HData' t)
  -> Sing (a :: [[HakaruFun]])
  -> State [String] [CDecl]
datumSum' _ SVoid               = return []
datumSum' dat (SPlus prod rest) =
  do (name:names) <- get
     put names
     let ident = Ident name
         mdecl = datumProd dat prod ident
     rest' <- datumSum' dat rest
     case mdecl of
       Nothing -> return rest'
       Just d  -> return $ [d] ++ rest'

datumProd
  :: Sing (HData' t)
  -> Sing (a :: [HakaruFun])
  -> Ident
  -> Maybe CDecl
datumProd _ SDone _       = Nothing
datumProd dat funs ident  =
  let declrs = fst $ runState (datumProd' dat funs) datumNames
  in  Just $ buildDeclaration (buildStruct Nothing $ declrs) ident

-- datumProd uses a store of names, which needs to match up with the names used
-- when they are assigned as well as printed
datumProd'
  :: Sing (HData' t)
  -> Sing (a :: [HakaruFun])
  -> State [String] [CDecl]
datumProd' _ SDone        = return []
datumProd' dat (SEt x ps) =
  do x'  <- datumPrim dat x
     ps' <- datumProd' dat ps
     return $ x' ++ ps'

-- We need to pass HData in case it is some recursive type
datumPrim
  :: Sing (HData' t)
  -> Sing (a :: HakaruFun)
  -> State [String] [CDecl]
datumPrim dat prim =
  do (name:names) <- get
     put names
     let ident = Ident name
         decl  = case prim of
                   SIdent     -> datumDeclaration dat ident
                   (SKonst k) -> typeDeclaration k ident
     return [decl]



--------------------------------------------------------------------------------
--                                Functions                                   --
--------------------------------------------------------------------------------
{-
   This still needs some work. Currently, we use the CodeGenMonad to give us
   a list of local declarations and statements to be used in a function. Then
   build a function from that.
-}

functionDef
  :: Sing (a :: Hakaru)
  -> Ident
  -> [CDecl]
  -> [CDecl]
  -> [CStat]
  -> CFunDef
functionDef typ ident argDecls internalDecls stmts =
  CFunDef (fmap CTypeSpec $ buildType typ)
          (CDeclr Nothing (CDDeclrIdent ident))
          argDecls
          (CCompound ((fmap CBlockDecl internalDecls)
                   ++ (fmap CBlockStat stmts)))

--------------
-- Closures --
--------------

closureDeclaration
  :: (Sing (a :: Hakaru))
  -> Ident
  -> CDecl
closureDeclaration = buildDeclaration . callStruct . typeName



--------------------------------------------------------------------------------
-- | buildType function do the work of describing how the Hakaru
-- type will be stored in memory. Arrays needed their own
-- declaration function for their arity

buildType :: Sing (a :: Hakaru) -> [CTypeSpec]
buildType SInt          = [CInt]
buildType SNat          = [CUnsigned, CInt]
buildType SProb         = [CDouble]
buildType SReal         = [CDouble]
buildType (SMeasure x)  = [callStruct . typeName . SMeasure $ x]
buildType (SArray t)    = [callStruct . typeName . SArray $ t]
buildType (SFun _ x)    = buildType $ x -- build type the function returns
buildType d@(SData _ _) = [callStruct . typeName $ d]


-- these mk...Decl functions are used in coersions
castTo :: CTypeSpec -> CExpr -> CExpr
castTo t = CCast (CTypeName [t] False)

castToPtrOf :: CTypeSpec -> CExpr -> CExpr
castToPtrOf t = CCast (CTypeName [t] True)

buildStruct :: Maybe Ident -> [CDecl] -> CTypeSpec
buildStruct mi decls =
  CSUType (CSUSpec CStructTag mi decls)

-- | callStruct will give the type spec calling a struct we have already
--   declared externally
callStruct :: String -> CTypeSpec
callStruct name =
  CSUType (CSUSpec CStructTag (Just (Ident name)) [])

buildUnion :: [CDecl] -> CTypeSpec
buildUnion decls =
 CSUType (CSUSpec CUnionTag Nothing decls)


binaryOp :: NaryOp a -> CExpr -> CExpr -> CExpr
binaryOp (Sum HSemiring_Prob)  a b = CBinary CAddOp (expE a) (expE b)
binaryOp (Prod HSemiring_Prob) a b = CBinary CAddOp a b
binaryOp (Sum _)               a b = CBinary CAddOp a b
binaryOp (Prod _)              a b = CBinary CMulOp a b
-- vvv Operations on bools, keeping in mind that in Hakaru-C: 0 is true and 1 is false
binaryOp And                   a b = CUnary CNegOp (CBinary CEqOp  a b) -- still wrong
binaryOp Or                    a b = CBinary CAndOp a b                 -- still wrong
binaryOp Xor                   a b = CBinary CLorOp a b                 -- still wrong
binaryOp x _ _ = error $ "TODO: binaryOp " ++ show x
