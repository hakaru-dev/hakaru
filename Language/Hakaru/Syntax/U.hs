{-# LANGUAGE DataKinds
           , GADTs
           , OverloadedStrings
           , TypeFamilies
           , StandaloneDeriving
           , KindSignatures
           , FlexibleContexts
           , DeriveDataTypeable #-}

module Language.Hakaru.Syntax.U where

import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.Nat

import Language.Hakaru.Syntax.Variable

import Data.Typeable hiding (Refl)
import Data.List
import Data.Monoid
    
data Untyped = U deriving (Read, Show)

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


data TLC :: ([Untyped] -> Untyped -> *) -> Untyped -> * where
    C    :: Int -> TLC abt 'U
    Lam  :: abt '[ 'U ] 'U -> TLC abt 'U
    App  :: abt '[] 'U     -> abt '[] 'U -> TLC abt 'U
    Add  :: abt '[] 'U     -> abt '[] 'U -> TLC abt 'U

instance Functor21 TLC where
    fmap21 f (C i)       = C i
    fmap21 f (Lam e1)    = Lam $ f e1
    fmap21 f (App e1 e2) = App (f e1) (f e2)
    fmap21 f (Add e1 e2) = Add (f e1) (f e2)

instance Foldable21 TLC where
    foldMap21 _ (C i)       = mempty
    foldMap21 f (Lam e1)    = f e1
    foldMap21 f (App e1 e2) = f e1 `mappend` f e2
    foldMap21 f (Add e1 e2) = f e1 `mappend` f e2

lam n f = Lam $ binder n SU f

prog :: ABT TLC abt => abt '[] 'U
prog = syn $ App (syn $ lam "x"
                          (\ x ->
                           (syn $ Add x
                            (syn $ C 3))))
                 (syn $ C 2)

prog' :: TrivialABT TLC '[] 'U
prog' = prog

type Env = [(Variable 'U, Val)]

data Val = I Int | F (Int -> Maybe Val)

instance Show Val where
    show (I n) = show n
    show (F _) = "<function>"

eval :: ABT TLC abt => abt '[] 'U -> Env -> Maybe Val
eval prog env = caseVarSyn prog (evalVar env) (evalSyn env)

evalVar :: Env -> Variable 'U -> Maybe Val
evalVar env v = lookup v env

evalSyn :: ABT TLC abt => Env -> TLC abt 'U -> Maybe Val
evalSyn env (C i)       = Just (I i)

evalSyn env (Lam e1)    =
    Just $ F (\v -> caseBind e1 $ \x e2 ->
                      eval e2 ((x, I v) : env))

evalSyn env (App e1 e2) = do F f  <- eval e1 env
                             I v  <- eval e2 env
                             f v

evalSyn env (Add e1 e2) = do I v1 <- eval e1 env
                             I v2 <- eval e2 env
                             return $ I (v1 + v2)
