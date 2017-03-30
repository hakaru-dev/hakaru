{-# LANGUAGE CPP
           , DataKinds
           , FlexibleInstances
           , FlexibleContexts
           , KindSignatures
           , OverloadedStrings
           , UndecidableInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Language.Hakaru.Syntax.Gensym where

#if __GLASGOW_HASKELL__ < 710
import           Data.Functor                    ((<$>))
#endif
import Control.Monad.State
import Data.Number.Nat
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.TypeOf
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing

class Monad m => Gensym m where
  freshVarId :: m Nat

instance (Monad m, MonadState Nat m) => Gensym m where
  freshVarId = do
    vid <- gets succ
    put vid
    return vid

freshVar
    :: (Functor m, Gensym m)
    => Variable (a :: Hakaru) -> m (Variable a)
freshVar v = fmap (\n -> v{varID=n}) freshVarId

varOfType
    :: (Functor m, Gensym m)
    => Sing (a :: Hakaru) -> m (Variable a)
varOfType t = fmap (\n  -> Variable "" n t) freshVarId

varForExpr
    :: (Functor m, Gensym m, ABT Term abt)
    => abt '[] a -> m (Variable a)
varForExpr v = fmap (\n -> Variable "" n (typeOf v)) freshVarId

