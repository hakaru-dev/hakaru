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

alphaEq :: (ABT Term abt)
        => abt '[] a
        -> abt '[] a
        -> Bool
alphaEq a b = ast2str a == ast2str b
    where ast2str = show . pretty . renameABT . stripTypeAnnotations 
