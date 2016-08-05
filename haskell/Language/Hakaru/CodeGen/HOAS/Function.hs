{-# LANGUAGE DataKinds,
             KindSignatures #-}

----------------------------------------------------------------
--                                                    2016.08.03
-- |
-- Module      :  Language.Hakaru.CodeGen.HOAS.Function
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  zsulliva@indiana.edu
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Provides tools for building C Functions with Hakaru types
--
----------------------------------------------------------------

module Language.Hakaru.CodeGen.HOAS.Function
  (function) where

import Language.C.Data.Node
import Language.C.Data.Ident
import Language.C.Syntax.AST

import Language.Hakaru.CodeGen.HOAS.Declaration
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing

node :: NodeInfo
node = undefNode

function :: Sing (a :: Hakaru)
         -> Ident
         -> [CDecl]
         -> [CStat]
         -> CFunDef
function typ ident declrs stmts =
  CFunDef [CTypeSpec (buildType typ)]
          (CDeclr (Just ident) [CFunDeclr (Right (declrs,False)) [] node] Nothing [] node)
          []
          (CCompound [] (fmap CBlockStmt stmts) node)
          node
