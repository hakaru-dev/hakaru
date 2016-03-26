{-# LANGUAGE DataKinds
           , GADTs
           , TypeOperators
           , PolyKinds
           , FlexibleContexts
           , ScopedTypeVariables
           #-}

module Language.Hakaru.Syntax.AST.AlphaEq where

import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Pretty.Concrete


----------------------------------------------------------------
----------------------------------------------------------------
renameABT
    :: forall abt xs a
    .  (ABT Term abt)
    => abt xs a
    -> abt xs a
renameABT ast = cataABT var bind_ syn ast
    where
    bind_ :: forall b x xs . Variable x -> abt xs b -> abt (x ': xs) b
    bind_ x e =
        let x' = x { varID = nextBind e}      
        in bind x' (rename x x' e)


alphaEq :: (ABT Term abt) => abt '[] a -> abt '[] a -> Bool
alphaEq a b =
    ast2str a == ast2str b
    where
    ast2str = show . pretty . renameABT 

----------------------------------------------------------------
----------------------------------------------------------- fin.
