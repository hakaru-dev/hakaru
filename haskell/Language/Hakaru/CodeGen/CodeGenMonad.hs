{-# LANGUAGE CPP,
             DataKinds,
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
  , declare
  , assign
  , putStat
  , genIdent
  , genIdent' ) where

import Control.Monad.State

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative ((<$>))
#endif

import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Syntax.AST

node :: NodeInfo
node = undefNode

suffixes :: [String]
suffixes =
  [ [letter] ++ show number
  | letter <- ['a'..'z']
  , number <- [(1 :: Integer)..]]

type CodeGen a = State ([String],[CDecl],[CStat]) a

runCodeGen :: CodeGen a -> ([CDecl],[CStat]) -> ([CDecl], [CStat])
runCodeGen gen (ds,ss) =
  let (_, (_,ds',ss')) = runState gen (suffixes,ds,ss)
  in  (reverse ds',reverse ss')

genIdent :: CodeGen Ident
genIdent = do (n:ns,decs,stmts) <- get
              put (ns,decs,stmts)
              return $ builtinIdent n

genIdent' :: String -> CodeGen Ident
genIdent' word = do (n:ns,decs,stmts) <- get
                    put (ns,decs,stmts)
                    return $ builtinIdent (word ++ "_" ++ n)

declare :: CDecl -> CodeGen ()
declare d = get >>= \(ns,ds,ss) -> put (ns,d:ds,ss)

putStat :: CStat -> CodeGen ()
putStat s = get >>= \(ns,ds,ss) -> put (ns,ds,s:ss)

assign :: Ident -> CExpr -> CodeGen ()
assign var expr =
  let assignment = CExpr (Just (CAssign CAssignOp
                                        (CVar var node)
                                        expr
                                        node))
                         node
  in  putStat assignment
