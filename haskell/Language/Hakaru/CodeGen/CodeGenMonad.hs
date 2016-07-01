{-# LANGUAGE DataKinds,
             FlexibleContexts,
             RankNTypes        #-}

----------------------------------------------------------------
--                                                    2016.07.01
-- |
-- Module      :  Language.Hakaru.CodeGen.CodeGenMonad
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  zsulliva@indiana.edu
-- Stability   :  experimental
-- Portability :  GHC-only
--
--   This module provides a monad for C code generation as well
-- as some useful helper functions for manipulating it
----------------------------------------------------------------


module Language.Hakaru.CodeGen.CodeGenMonad
  ( CodeGen
  , runCodeGen
  , assign
  , declare
  , getIdent ) where

import Control.Monad.State

import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Syntax.AST

node = undefNode
-- names = [ [letter] ++ show number
--         | letter <- ['a'..'z']
--         , number <- [1..]]

type CodeGen a = State ([CDecl],Ident) a

runCodeGen :: CodeGen CStat -> ([CDecl],Ident) -> ([CDecl], CStat)
runCodeGen gen initial =
  let (cstat, (decs, _)) = runState gen initial
  in  (decs,cstat)

getIdent :: CodeGen Ident
getIdent = snd <$> get

assign :: Ident -> CStat -> CodeGen CStat
assign var cstat = return $
  CExpr (Just (CAssign CAssignOp
                       (CVar var node)
                       (CStatExpr (CCompound [] [CBlockStmt cstat] node) node)
                       node))
        node

declare :: CDecl -> CodeGen ()
declare d = get >>= \(decs,ident) -> put (d:decs,ident)
