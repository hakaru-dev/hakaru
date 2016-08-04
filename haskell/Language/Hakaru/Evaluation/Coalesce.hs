{-# LANGUAGE DataKinds
           , GADTs
           , Rank2Types
           , FlexibleContexts
           #-}

----------------------------------------------------------------
--                                                    2016.07.19
-- |
-- Module      :  Language.Hakaru.Evaluation.Coalesce
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  zsulliva@indiana.edu
-- Stability   :  experimental
-- Portability :  GHC-only
--
----------------------------------------------------------------

module Language.Hakaru.Evaluation.Coalesce
  ( coalesce )
  where

import qualified Language.Hakaru.Parser.AST as U
import           Language.Hakaru.Syntax.ABT
import qualified Data.Foldable                 as F

coalesce
    :: (ABT U.Term abt)
    => abt '[] a
    -> abt '[] a
coalesce =
    cataABT var bind alg
    where
    alg :: forall abt a. (ABT U.Term abt) => U.Term abt a -> abt '[] a
    alg (U.NaryOp_ op args) = syn $ U.NaryOp_ op (coalesceNaryOp op args)
    alg t                   = syn t

coalesceNaryOp
    :: (ABT U.Term abt)
    => U.NaryOp
    -> [abt '[] a]
    -> [abt '[] a]
coalesceNaryOp op = F.concatMap $ \ast' ->
     caseVarSyn ast' (return . var) $ \t ->
       case t of
       U.NaryOp_ op' args' | op == op' -> coalesceNaryOp op args'
       _                               -> [ast']
