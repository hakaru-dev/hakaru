{-# LANGUAGE DataKinds
           , GADTs
           , FlexibleContexts 
           #-}

module Language.Hakaru.Normalize where

import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST


removeNestedTypeAnnotations :: ABT Term abt => abt '[] a -> abt '[] a
removeNestedTypeAnnotations  =
    cataABT var bind $ \t1 ->
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

stripTypeAnnotations :: ABT Term abt => abt '[] a -> abt '[] a
stripTypeAnnotations =
    cataABT var bind $ \t1 ->
        case t1 of
        Ann_ typ :$ e1 :* End -> e1
        x -> syn x

reduceAST :: ABT Term abt => abt '[] a -> abt '[] a
reduceAST = removeNestedTypeAnnotations . collapseNestedSuperposes
