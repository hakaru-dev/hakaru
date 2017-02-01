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

import           Language.Hakaru.Syntax.Prelude hiding (fst, (.))

-- What we need is an environment like data structure which maps Terms (or
-- general abts?) to other abts. Can such a mapping be implemented efficiently?
-- This would seem to require a hash operation to make efficient.

data EAssoc (abt :: [Hakaru] -> Hakaru -> *)
  = forall a . EAssoc !(abt '[] a) !(abt '[] a)

-- An association list for now
newtype Env (abt :: [Hakaru] -> Hakaru -> *) = Env [EAssoc abt]

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
        Nothing   -> go ast xs
        Just Refl -> if alphaEq ast a then go b env else go ast xs

insertEnv
  :: forall abt a
  .  abt '[] a
  -> abt '[] a
  -> Env abt
  -> Env abt
insertEnv ast1 ast2 (Env env) = Env (EAssoc ast1 ast2 : env)

cse :: (ABT Term abt) => abt '[] a -> abt '[] a
cse = undefined

