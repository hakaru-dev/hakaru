{-# LANGUAGE DataKinds
           , GADTs
           , FlexibleContexts 
           #-}

module Language.Hakaru.Normalize where

import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST


removeNestedAnnotations :: ABT Term abt => abt '[] a -> abt '[] a
removeNestedAnnotations  = cataABT var bind $ \t1 ->
                             case t1 of
                               Ann_ typ :$ e1 :* End ->
                                   caseVarSyn e1 var $ \t2 ->
                                       case t2 of
                                         Ann_ _ :$ e2 :* End ->
                                              syn (Ann_ typ :$ e2 :* End)
                                         _ -> syn t1 
                               x -> syn x

collapseNestedSuperposes :: ABT Term abt => abt '[] a -> abt '[] a
collapseNestedSuperposes = cataABT var bind syn

reduceAST :: ABT Term abt => abt '[] a -> abt '[] a
reduceAST = removeNestedAnnotations . collapseNestedSuperposes
