{-# LANGUAGE CPP
           , DataKinds
           , GADTs
           , OverloadedStrings
           , TypeFamilies
           , KindSignatures
           , FlexibleContexts
           , StandaloneDeriving
           , DeriveDataTypeable
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.31
-- |
-- Module      :  Language.Hakaru.Syntax.Untyped
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- An example of using "Language.Hakaru.Syntax.ABT" to define the
-- untyped lambda calculus (with integers and addition).
--
-- TODO: this file doesn't belong here; should be moved to the
-- @Examples@ directory. If the 'U' type is actually used by the
-- parser, then that definition should move to @Language.Hakaru.Parser.*@
-- somewhere.
----------------------------------------------------------------
module Language.Hakaru.Syntax.U where

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.Variable
import Language.Hakaru.Types.Sing (Sing, SingI(..))

import Data.Typeable hiding (Refl)
#if __GLASGOW_HASKELL__ < 710
import Data.Monoid
#endif

----------------------------------------------------------------
----------------------------------------------------------------

-- | The kind containing exactly one type.
data Untyped = U
    deriving (Read, Show)

deriving instance Typeable 'U

data instance Sing (a :: Untyped) where
    SU :: Sing 'U

instance SingI 'U where
    sing = SU

instance Show (Sing (a :: Untyped)) where
    showsPrec = showsPrec1
    show      = show1

instance Show1 (Sing :: Untyped -> *) where
    showsPrec1 _ SU = ("SU" ++)

instance Eq (Sing (a :: Untyped)) where
    SU == SU = True

instance Eq1 (Sing :: Untyped -> *) where
    eq1 SU SU = True

instance JmEq1 (Sing :: Untyped -> *) where
    jmEq1 SU SU = Just Refl


-- | The untyped lambda calculus, with integers and addition.
data TLC :: ([Untyped] -> Untyped -> *) -> Untyped -> * where
    C    :: Int -> TLC abt 'U
    Lam  :: abt '[ 'U ] 'U -> TLC abt 'U
    App  :: abt '[] 'U     -> abt '[] 'U -> TLC abt 'U
    Add  :: abt '[] 'U     -> abt '[] 'U -> TLC abt 'U

instance Functor21 TLC where
    fmap21 _ (C i)       = C i
    fmap21 f (Lam e1)    = Lam (f e1)
    fmap21 f (App e1 e2) = App (f e1) (f e2)
    fmap21 f (Add e1 e2) = Add (f e1) (f e2)

instance Foldable21 TLC where
    foldMap21 _ (C _)       = mempty
    foldMap21 f (Lam e1)    = f e1
    foldMap21 f (App e1 e2) = f e1 `mappend` f e2
    foldMap21 f (Add e1 e2) = f e1 `mappend` f e2

lam n f = Lam $ binder n SU f


-- | The 'TLC' program: \"@(\x -> x + 3) $ 2@\"
prog :: ABT TLC abt => abt '[] 'U
prog = syn $ App
    (syn . lam "x" $ \ x ->
        (syn $ Add x (syn $ C 3)))
    (syn $ C 2)

prog' :: TrivialABT TLC '[] 'U
prog' = prog

type Env = [(Variable 'U, Val)]

data Val = I Int | F (Int -> Maybe Val)

instance Show Val where
    show (I n) = show n
    show (F _) = "<function>"


-- | For a larger language we'd make this a newtype and actually
-- give it Functor, Applicative, and Monad instances. But for now,
-- a type alias is fine.
type EvalMonad a = Env -> Maybe a

eval :: ABT TLC abt => abt '[] 'U -> EvalMonad Val
eval prog = \env -> caseVarSyn prog (`evalVar` env) (`evalSyn` env)

evalVar :: Variable 'U -> EvalMonad Val
evalVar v env = lookup v env

evalSyn :: ABT TLC abt => TLC abt 'U -> EvalMonad Val
evalSyn (C i)       env = return (I i)
evalSyn (Lam e1)    env =
    return . F $ \v ->
        caseBind e1 $ \x e1' ->
            eval e1' ((x, I v) : env)
evalSyn (App e1 e2) env = do
    F f <- eval e1 env
    I v <- eval e2 env
    f v
evalSyn (Add e1 e2) env = do
    I v1 <- eval e1 env
    I v2 <- eval e2 env
    return $ I (v1 + v2)

----------------------------------------------------------------
----------------------------------------------------------- fin.
