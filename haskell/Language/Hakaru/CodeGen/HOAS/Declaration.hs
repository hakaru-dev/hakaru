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
  ( -- tools for building C types
    typeDeclaration
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


datumDeclaration
  :: (Sing (HData' t))
  -> Ident
  -> CDecl
datumDeclaration (SData _ SVoid) _                   =
  error $ "TODO: datumDeclaration: SVoid > is this possible?"
datumDeclaration (SData _ (SPlus x SVoid)) ident =
  CDecl [ CTypeSpec . buildStruct . return $
          CDecl [CTypeSpec intTyp ]
                [( Just $ CDeclr (Just (internalIdent "index"))
                                 []
                                 Nothing
                                 []
                                 node
                  , Nothing
                  , Nothing)]
                 node
        ]
        [ ( Just $ CDeclr (Just ident) [] Nothing [] node
        , Nothing
        , Nothing) ]
        node
datumDeclaration (SData _ (SPlus x rest)) _      = error $ "TODO: datumDeclaration Unit"


datumSum :: Sing (a :: [[HakaruFun]]) -> CDecl
datumSum SVoid
  = CDecl [ CTypeSpec intTyp ]
          [ ( Just $ CDeclr (Just (internalIdent "index")) [] Nothing [] node
            , Nothing
            , Nothing)]
          node
datumSum (SPlus x rest)
  = CDecl [ CTypeSpec . buildUnion $ [datumSum rest, datumProd x] ]
          [ ( Just $ CDeclr (Just (internalIdent "index")) [] Nothing [] node
            , Nothing
            , Nothing)]
          node

datumProd :: Sing (a :: [HakaruFun]) -> CDecl
datumProd funs = fst $ runState (datumProd' funs) datumNames
  where datumNames = filter (\n -> not $ elem (head n) ['0'..'9']) names
        base = ['0'..'9'] ++ ['a'..'z']
        names = [[x] | x <- base] `mplus` (do n <- names
                                              [n++[x] | x <- base])


-- datumProd uses a store of names, which needs to match up with the names used
-- when they are assigned as well as printed
datumProd' :: Sing (a :: [HakaruFun]) -> State [String] CDecl
datumProd' SDone                 = return
  $ CDecl [ CTypeSpec . buildStruct $ [] ]
          [ ( Just $ CDeclr (Just (internalIdent "product")) [] Nothing [] node
            , Nothing
            , Nothing)]
          node
datumProd' (SEt (SKonst s) rest) = return
  $ CDecl [ CTypeSpec . buildStruct $ [] ]
          [ ( Just $ CDeclr (Just (internalIdent "product")) [] Nothing [] node
            , Nothing
            , Nothing)]
          node
datumProd' (SEt SIdent _)        = error "TODO: datumProd' for SIdent"

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
