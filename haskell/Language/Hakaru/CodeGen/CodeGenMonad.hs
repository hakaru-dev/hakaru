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
  , getIdent
  , genIdent ) where

import Control.Monad.State

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative ((<$>))
#endif

import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Syntax.AST

node = undefNode
names = fmap builtinIdent
        [ [letter] ++ show number
        | letter <- ['a'..'z']
        , number <- [1..]]

type CodeGen a = State ([Ident],[CDecl],Ident) a

runCodeGen :: CodeGen CStat -> ([CDecl],Ident) -> ([CDecl], CStat)
runCodeGen gen (ds,i) =
  let (cstat, (_,decs,_)) = runState gen (names,ds,i)
  in  (reverse decs,cstat)

getIdent :: CodeGen Ident
getIdent = (\(_,_,i) -> i) <$> get

genIdent :: CodeGen Ident
genIdent = do (n:ns,decs,cname) <- get
              put (ns,decs,cname)
              return n

declare :: CDecl -> CodeGen ()
declare d = get >>= \(names,decs,ident) -> put (names,d:decs,ident)
