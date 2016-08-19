{-# LANGUAGE DataKinds,
             FlexibleContexts,
             GADTs,
             KindSignatures #-}

----------------------------------------------------------------
--                                                    2016.07.11
-- |
-- Module      :  Language.Hakaru.CodeGen.HOAS.Declaration
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  zsulliva@indiana.edu
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Provides tools for building C declarations from Hakaru types
--
----------------------------------------------------------------

module Language.Hakaru.CodeGen.HOAS.Declaration
  ( buildDeclaration
  , extDecl
  , extFunc

  -- tools for building C types
  , typeDeclaration
  , arrayDeclaration
  , datumDeclaration
  , datumStruct
  , datumName

  , datumSum
  , datumProd

  , buildType
  , buildStruct
  , buildUnion

  , doubleTyp
  , intTyp
  , doublePtr
  , intPtr
  , boolTyp
  ) where

import Control.Monad.State

import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Syntax.AST

import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing

node :: NodeInfo
node = undefNode

buildDeclaration :: CTypeSpec -> Ident -> CDecl
buildDeclaration ctyp ident =
  CDecl [CTypeSpec ctyp]
        [(Just $ CDeclr (Just ident) [] Nothing [] node,Nothing,Nothing)]
        node

extDecl :: CDecl -> CExtDecl
extDecl = CDeclExt

extFunc :: CFunDef -> CExtDecl
extFunc = CFDefExt
                 
typeDeclaration :: Sing (a :: Hakaru) -> Ident -> CDecl
typeDeclaration typ ident =
  CDecl [CTypeSpec $ buildType typ]
        [(Just $ CDeclr (Just ident) [] Nothing [] node,Nothing,Nothing)]
        node

-- and array declaration just requires the type
arrayDeclaration
  :: Sing (a :: Hakaru)
  -> Ident
  -> CDecl
arrayDeclaration typ ident =
  CDecl [ CTypeSpec
          $ buildStruct Nothing
                        [ CDecl [CTypeSpec intTyp ]
                                           [( Just $ CDeclr (Just (internalIdent "size"))
                                                            []
                                                            Nothing
                                                            []
                                                            node
                                             , Nothing
                                             , Nothing)]
                                            node
                        , CDecl [CTypeSpec $ buildType typ]
                                           [( Just $ CDeclr (Just (internalIdent "data"))
                                                            [CPtrDeclr [] node]
                                                            Nothing
                                                            []
                                                            node
                                            , Nothing
                                            , Nothing)]
                                            node
                        ]
       ]
       [ ( Just $ CDeclr (Just ident) [] Nothing [] node
         , Nothing
         , Nothing) ]
       node

--------------------------------------------------------------------------------
-- | datumProd and datumSum use a store of names, which needs to match up with
-- the names used when they are assigned and printed
-- datumDeclaration declares struct internally
-- datumStruct declares struct definitions externally
   
-- | datumName provides a unique name to identify a struct type
datumName :: Sing (a :: [[HakaruFun]]) -> String
datumName SVoid = "V"
datumName (SPlus prod sum) = concat ["S",datumName' prod,datumName sum]
  where datumName' :: Sing (a :: [HakaruFun]) -> String
        datumName' SDone = "U"
        datumName' (SEt (SKonst x) prod') = concat ["S",tail . show $ x,datumName' prod']
        datumName' (SEt SIdent prod')     = error "TODO: datumName of SIdent"

datumStruct :: (Sing (HData' t)) -> CExtDecl
datumStruct (SData _ typ) = extDecl $ datumSum typ (builtinIdent (datumName typ))

datumDeclaration
  :: (Sing (HData' t))
  -> Ident
  -> CDecl
datumDeclaration (SData _ typ) = buildDeclaration (callStruct (datumName typ))

datumSum :: Sing (a :: [[HakaruFun]]) -> Ident -> CDecl
datumSum funs ident =
  let declrs = fst $ runState (datumSum' funs) datumNames
      union  = CDecl [ CTypeSpec . buildUnion $ declrs ]
                     [ ( Just $ CDeclr (Just (internalIdent "sum")) [] Nothing [] node
                       , Nothing
                       , Nothing)]
                     node
      index  = CDecl [ CTypeSpec intTyp ]
                     [ ( Just $ CDeclr (Just (internalIdent "index")) [] Nothing [] node
                       , Nothing
                       , Nothing)]
                     node
  in CDecl [ CTypeSpec . buildStruct (Just ident) $ [index,union] ]
           [ ( Just $ CDeclr Nothing [] Nothing [] node
             , Nothing
             , Nothing)]
           node
  where datumNames = filter (\n -> not $ elem (head n) ['0'..'9']) names
        base = ['0'..'9'] ++ ['a'..'z']
        names = [[x] | x <- base] `mplus` (do n <- names
                                              [n++[x] | x <- base])

datumSum' :: Sing (a :: [[HakaruFun]]) -> State [String] [CDecl]
datumSum' SVoid          = return []
datumSum' (SPlus prod rest) =
  do (name:names) <- get
     put names
     let ident = internalIdent name
         decl  = datumProd prod ident
     rest' <- datumSum' rest
     return $ [decl] ++ rest'


datumProd :: Sing (a :: [HakaruFun]) -> Ident -> CDecl
datumProd funs ident =
  let declrs = fst $ runState (datumProd' funs) datumNames
  in  CDecl [ CTypeSpec . buildStruct Nothing $ declrs ]
            [ ( Just $ CDeclr (Just ident) [] Nothing [] node
              , Nothing
              , Nothing)]
            node
  where datumNames = filter (\n -> not $ elem (head n) ['0'..'9']) names
        base = ['0'..'9'] ++ ['a'..'z']
        names = [[x] | x <- base] `mplus` (do n <- names
                                              [n++[x] | x <- base])



-- datumProd uses a store of names, which needs to match up with the names used
-- when they are assigned as well as printed
datumProd' :: Sing (a :: [HakaruFun]) -> State [String] [CDecl]
datumProd' SDone                 = return []
datumProd' (SEt (SKonst t) rest) =
  do (name:names) <- get
     put names
     let ident = internalIdent name
         decl  = CDecl [ CTypeSpec . buildType $ t ]
                       [ ( Just $ CDeclr (Just ident) [] Nothing [] node
                         , Nothing
                         , Nothing)]
                       node
     rest' <- datumProd' rest
     return $ [decl] ++ rest'
datumProd' (SEt SIdent rest) = error "TODO: datumProd' SIdent"



----------------------------------------------------------------
-- | buildType function do the work of describing how the Hakaru
-- type will be stored in memory. Arrays needed their own
-- declaration function for their arity
buildType :: Sing (a :: Hakaru) -> CTypeSpec
buildType SInt         = CIntType undefNode
buildType SNat         = CIntType undefNode
buildType SProb        = CDoubleType undefNode
buildType SReal        = CDoubleType undefNode
buildType (SMeasure x) = buildType x
buildType (SArray x)   = buildType x
buildType _ = error $ "TODO: buildCType "

buildStruct :: Maybe Ident -> [CDecl] -> CTypeSpec
buildStruct mi [] =
  CSUType (CStruct CStructTag mi Nothing [] node) node
buildStruct mi declrs =
  CSUType (CStruct CStructTag mi (Just declrs) [] node) node

-- | callStruct will give the type spec calling a struct we have already declared externally 
callStruct :: String -> CTypeSpec
callStruct name =
  CSUType (CStruct CStructTag (Just (internalIdent name)) Nothing [] node) node

buildUnion :: [CDecl] -> CTypeSpec
buildUnion [] =
 CSUType (CStruct CUnionTag Nothing Nothing [] node) node
buildUnion declrs =
 CSUType (CStruct CUnionTag Nothing (Just declrs) [] node) node



intTyp,doubleTyp :: CTypeSpec
intTyp    = CIntType undefNode
doubleTyp = CDoubleType undefNode

intPtr,doublePtr :: CDecl
intPtr    = undefined
doublePtr = undefined

boolTyp :: CDecl
boolTyp =
  CDecl [CTypeSpec
          (CSUType
            (CStruct CStructTag
                     (Just (internalIdent "bool"))
                     (Just [CDecl [CTypeSpec (CIntType node)]
                                  [(Just (CDeclr (Just (internalIdent "index")) [] Nothing [] node),Nothing,Nothing)]
                                  node])
                     []
                     node)
            node)]
        []
        node
