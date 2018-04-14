{-# LANGUAGE CPP
           , DataKinds
           , EmptyCase
           , ExistentialQuantification
           , FlexibleContexts
           , GADTs
           , GeneralizedNewtypeDeriving
           , KindSignatures
           , MultiParamTypeClasses
           , OverloadedStrings
           , PolyKinds
           , ScopedTypeVariables
           , TypeFamilies
           , TypeOperators
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
-- |
-- Module      :  Language.Hakaru.Syntax.Rename 
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Performs renaming of variables hints only (in Hakaru expressions) 
-- which hopefully has no effect on semantics but can produce prettier expressions
--
----------------------------------------------------------------
module Language.Hakaru.Syntax.Rename where

import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.IClasses
import qualified Data.Text as Text 
import           Data.Text (Text) 
import           Data.Char 

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative
#endif

type Renamer = Text -> Text 

renameAST 
  :: forall abt xs a . (ABT Term abt)
  => Renamer 
  -> abt xs a
  -> abt xs a
renameAST r = start
  where
    start :: abt ys b -> abt ys b
    start = loop . viewABT

    loop :: View (Term abt) ys b -> abt ys b
    loop (Var v)    = var (renameVar r v)
    loop (Syn s)    = syn (fmap21 start s)
    loop (Bind v b) = bind (renameVar r v) (loop b) 

renameVar :: Renamer -> Variable a -> Variable a 
renameVar r v = v { varHint = r (varHint v) } 

removeUnicodeChars :: Text -> Text 
removeUnicodeChars = Text.filter isAscii 
