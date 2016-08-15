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

  -- tools for building C types
  , typeDeclaration
  , arrayDeclaration
  , datumDeclaration

  , datumSum
  , datumProd

  , buildType
  , buildStruct
  , buildUnion

  , doubleTyp
  , intTyp
  , doublePtr
  , intPtr
  ) where

import Control.Monad.State

import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Syntax.AST

import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing

node :: NodeInfo
node = undefNode

buildDeclaration :: Sing (a :: Hakaru) -> Maybe Ident -> CDecl
buildDeclaration = undefined

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
          $ buildStruct [ CDecl [CTypeSpec intTyp ]
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

datumDeclaration
  :: (Sing (HData' t))
  -> Ident
  -> CDecl
datumDeclaration (SData _ typ) ident = datumSum typ ident

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
  in CDecl [ CTypeSpec . buildStruct $ [index,union] ]
           [ ( Just $ CDeclr (Just ident) [] Nothing [] node
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
  in  CDecl [ CTypeSpec . buildStruct $ declrs ]
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

buildStruct :: [CDecl] -> CTypeSpec
buildStruct [] =
 CSUType (CStruct CStructTag Nothing Nothing [] node) node
buildStruct declrs =
 CSUType (CStruct CStructTag Nothing (Just declrs) [] node) node

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
