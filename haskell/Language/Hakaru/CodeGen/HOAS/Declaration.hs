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

  , buildType

  , doubleTyp
  , intTyp
  , doublePtr
  , intPtr
  ) where

import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Syntax.AST

-- import Language.Hakaru.Syntax.ABT
-- import Language.Hakaru.Syntax.AST
-- import Language.Hakaru.Syntax.Datum
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
          $ CSUType (CStruct CStructTag
                             Nothing
                             (Just [ -- contains and int and pointer to type
                                     CDecl [CTypeSpec $ buildType SInt]
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
                                    ])
                              []
                              node)
            node
       ]
       [ ( Just $ CDeclr (Just ident) [] Nothing [] node
         , Nothing
         , Nothing) ]
       node


datumDeclaration
  :: (Sing (HData' t))
  -> Ident
  -> CDecl
datumDeclaration dcode ident =
  CDecl [CTypeSpec $ CSUType (CStruct CStructTag Nothing (Just []) [] node) node]
        [( Just $ CDeclr (Just ident)
                         []
                         Nothing
                         []
                         node
         , Nothing
         , Nothing)]
        node


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

intTyp,doubleTyp :: CTypeSpec
intTyp    = CIntType undefNode
doubleTyp = CDoubleType undefNode

intPtr,doublePtr :: CDecl
intPtr    = undefined
doublePtr = undefined
