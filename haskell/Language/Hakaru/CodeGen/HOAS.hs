{-# LANGUAGE DataKinds,
             GADTs,
             KindSignatures #-}

----------------------------------------------------------------
--                                                    2016.07.01
-- |
-- Module      :  Language.Hakaru.CodeGen.HOAS
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  zsulliva@indiana.edu
-- Stability   :  experimental
-- Portability :  GHC-only
--
--   HOAS provides a higher order abstract syntax for building
-- C ASTs
--
----------------------------------------------------------------

module Language.Hakaru.CodeGen.HOAS
  ( typeDeclaration ) where

import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing

import Language.C.Data.Ident
import Language.C.Data.Node       
import Language.C.Syntax.AST

node = undefNode       

typeDeclaration :: Sing (a :: Hakaru) -> Ident -> CDecl
typeDeclaration typ ident =
  CDecl [CTypeSpec (toCType typ)]
        [(Just $ CDeclr (Just ident) [] Nothing [] node,Nothing,Nothing)]
        node

toCType :: Sing (a :: Hakaru) -> CTypeSpecifier NodeInfo
toCType SInt       = CIntType undefNode
toCType SNat       = CIntType undefNode
toCType SProb      = CDoubleType undefNode
toCType SReal      = CDoubleType undefNode
toCType _          = error "TODO: toCType"

