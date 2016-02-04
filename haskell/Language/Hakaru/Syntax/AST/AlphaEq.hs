{-# LANGUAGE DataKinds
           , GADTs
           , TypeOperators
           , PolyKinds
           , FlexibleContexts
           , ScopedTypeVariables
           , UndecidableInstances
           #-}

module Language.Hakaru.Syntax.AST.AlphaEq where

import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Pretty.Concrete

import Language.Hakaru.Normalize

renameABT :: (ABT Term abt)
          => abt xs a
          -> abt xs a
renameABT ast = cataABT var bind_ syn ast
    where bind_ x e = bind x' (rename x x' e)
           where x' = x { varID = nextBind e}      

alphaEq :: (ABT Term abt)
        => abt '[] a
        -> abt '[] a
        -> Bool
alphaEq a b = ast2str a == ast2str b
    where ast2str = show . pretty . renameABT . stripTypeAnnotations 
