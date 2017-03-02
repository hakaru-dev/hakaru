{-# LANGUAGE DataKinds
           , FlexibleInstances
           , FlexibleContexts
           , KindSignatures
           , OverloadedStrings
           , UndecidableInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Language.Hakaru.Syntax.Gensym where

import           Control.Monad.State
import           Data.Number.Nat
import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.TypeOf
import           Language.Hakaru.Types.Sing

class Monad m => Gensym m where
  freshVarId :: m Nat

instance (Monad m, MonadState Nat m) => Gensym m where
  freshVarId = do
    vid <- gets succ
    put vid
    return vid

freshVar :: Gensym m => Variable (a :: k) -> m (Variable a)
freshVar v = fmap (\n -> v{varID=n}) freshVarId

varOfType :: Gensym m => Sing (a :: k) -> m (Variable a)
varOfType t = fmap (\n  -> Variable "" n t) freshVarId

varForExpr :: (Gensym m, ABT Term abt) => abt '[] a -> m (Variable a)
varForExpr v = fmap (\n -> Variable "" n (typeOf v)) freshVarId

