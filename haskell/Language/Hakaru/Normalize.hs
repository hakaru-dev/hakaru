{-# LANGUAGE DataKinds
           , FlexibleContexts 
           #-}

module Language.Hakaru.Normalize where

import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST


removeNestedAnnotations :: ABT Term abt => abt '[] a -> abt '[] a
removeNestedAnnotations  = cataABT var bind syn

collapseNestedSuperposes :: ABT Term abt => abt '[] a -> abt '[] a
collapseNestedSuperposes = cataABT var bind syn

reduceAST :: ABT Term abt => abt '[] a -> abt '[] a
reduceAST = removeNestedAnnotations . collapseNestedSuperposes
