{-# LANGUAGE DataKinds
           , GADTs
           , TypeOperators
           , FlexibleContexts 
           , ScopedTypeVariables
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

stripTypeAnnotations :: ABT Term abt => abt '[] a -> abt '[] a
stripTypeAnnotations =
    cataABT var bind $ \t1 ->
        case t1 of
        Ann_ typ :$ e1 :* End -> e1
        x -> syn x

renameABT :: forall abt xs a
          .  (ABT Term abt)
          => abt xs a
          -> abt xs a
renameABT ast = cataABT var bind_ syn ast
    where bind_
              :: forall a x xs
              .  Variable x -> abt xs a -> abt (x ': xs) a
          bind_ x e = bind x' (rename x x' e)
           where x' = x { varID = nextBind e}      
