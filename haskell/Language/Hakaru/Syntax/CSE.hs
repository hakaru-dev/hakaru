{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
module Language.Hakaru.Syntax.CSE where

import           Prelude hiding ((+))
import           Control.Monad.Reader
import qualified Data.IntMap                     as IM
import           Data.Maybe
import           Data.Number.Nat
import           Data.Sequence                   ((<|))
import qualified Data.Sequence                   as S

import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.AST.Eq
import           Language.Hakaru.Syntax.Datum
import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Syntax.TypeOf
import           Language.Hakaru.Types.DataKind

import           Language.Hakaru.Syntax.Prelude hiding (fst, (.), (>>=))

example1 :: TrivialABT Term '[] 'HReal
example1 = triv $ real_ 1 + real_ 2 + real_ 3

example2 :: TrivialABT Term '[] 'HReal
example2 = triv $ real_ 6

example3 :: TrivialABT Term '[] 'HReal
example3 = let_ (real_ 1 + real_ 2) $ \x ->
           let_ (real_ 1 + real_ 2) $ \y ->
           x + y

example4 :: TrivialABT Term '[] 'HReal
example4 = let_ (summate (nat_ 0) (nat_ 1) $ \x -> real_ 1) $ \x ->
           let_ (summate (nat_ 0) (nat_ 1) $ \x -> real_ 1) $ \y ->
           x + y

-- What we need is an environment like data structure which maps Terms (or
-- general abts?) to other abts. Can such a mapping be implemented efficiently?
-- This would seem to require a hash operation to make efficient.

data EAssoc (abt :: [Hakaru] -> Hakaru -> *)
  = forall a . EAssoc !(abt '[] a) !(abt '[] a)

-- An association list for now
newtype Env (abt :: [Hakaru] -> Hakaru -> *) = Env [EAssoc abt]

emptyEnv :: Env a
emptyEnv = Env []

-- Attempt to find a new expression in then environment. The lookup is chained
-- to iteratively perform lookup until no match is found, resulting in an
-- equivalence-relation in the environment. This could be made faster with path
-- compression and a more efficient lookup structure.
-- NB: This code could potentially produce an infinite loop depending on how
-- terms are added to the environment. How do we want to prevent this?
lookupEnv
  :: forall abt a . (ABT Term abt)
  => abt '[] a
  -> Env abt
  -> abt '[] a
lookupEnv ast (Env env) = go ast env
  where
    go :: abt '[] a -> [EAssoc abt] -> abt '[] a
    go ast []                = ast
    go ast (EAssoc a b : xs) =
      case jmEq1 (typeOf ast) (typeOf a) of
        Nothing                   -> go ast xs
        Just Refl | alphaEq ast a -> go b env
                  | otherwise     -> go ast xs

insertEnv
  :: forall abt a . (ABT Term abt)
  => abt '[] a
  -> abt '[] a
  -> Env abt
  -> Env abt
insertEnv ast1 ast2 (Env env) =
  case viewABT ast1 of
    -- Point new variables to the older ones, this does not affect the amount of
    -- work done, since ast2 is always a variable, but will make eliminating
    -- redundant let bindings easier.
    Var v -> Env (EAssoc ast2 ast1 : env)
    -- Otherwise map expressions to their binding variables
    _     -> Env (EAssoc ast1 ast2 : env)

newtype CSE (abt :: [Hakaru] -> Hakaru -> *) a = CSE { runCSE :: Reader (Env abt) a }
  deriving (Functor, Applicative, Monad, MonadReader (Env abt))

replaceCSE
  :: (ABT Term abt)
  => abt '[] a
  -> CSE abt (abt '[] a)
replaceCSE abt = lookupEnv abt `fmap` ask

cse :: forall abt a . (ABT Term abt) => abt '[] a -> abt '[] a
cse abt = runReader (runCSE (cse' abt)) emptyEnv

cse' :: forall abt xs a . (ABT Term abt) => abt xs a -> CSE abt (abt xs a)
cse' = loop . viewABT
  where
    loop :: View (Term abt) ys a ->  CSE abt (abt ys a)
    loop (Var v)    = cseVar v
    loop (Syn s)    = cseTerm s
    loop (Bind v b) = loop b >>= return . bind v

-- Variables can be equivalent to other variables
-- TODO: A good sanity check would be to ensure the result in this case is
-- always a variable or constant. A variable should never be substituted for
-- a more complex expression.
cseVar
  :: (ABT Term abt)
  => Variable a
  -> CSE abt (abt '[] a)
cseVar v = replaceCSE (var v)

-- Thanks to A-normalization, the only case we really need to care about is let
-- bindings. Everything else is just structural recursion.
cseTerm
  :: (ABT Term abt)
  => Term abt a
  -> CSE abt (abt '[] a)

cseTerm (Let_ :$ rhs :* body :* End) = do
  rhs' <- cse' rhs
  caseBind body $ \v body' ->
    local (insertEnv rhs' (var v)) $ do
      body'' <- cse' body'
      return $ syn (Let_ :$ rhs' :* bind v body'' :* End)

cseTerm term = traverse21 cse' term >>= replaceCSE . syn

