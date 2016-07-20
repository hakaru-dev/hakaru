{-# LANGUAGE DataKinds,
             FlexibleContexts,
             GADTs,
             RankNTypes        #-}

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
  ( coalesce
  , coalesceTyped )
  where

import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT
import qualified Language.Hakaru.Parser.AST as U

import qualified Data.Sequence as S

----------------------------------------------------------------
-- Untyped

coalesce :: U.AST' a
         -> U.AST' a
coalesce (U.Var n)                = U.Var n
coalesce (U.Lam n typ e1)         = U.Lam n typ (coalesce e1)
coalesce (U.App e0 e1)            = U.App (coalesce e0) (coalesce e1)
coalesce (U.Let n e0 e1)          = U.Let n (coalesce e0) (coalesce e1)
coalesce (U.If e0 e1 e2)          = U.If (coalesce e0) (coalesce e1) (coalesce e2)
coalesce (U.Ann e0 typ)           = U.Ann (coalesce e0) typ
coalesce U.Infinity'              = U.Infinity'
coalesce (U.ULiteral lit)         = (U.ULiteral lit)
coalesce (U.NaryOp op es)         = U.NaryOp op (coalesceNaryOp op es)
coalesce U.Unit                   = U.Unit
coalesce U.Empty                  = U.Empty
coalesce (U.Pair e0 e1)           = U.Pair (coalesce e0) (coalesce e1)
coalesce (U.Array n e0 e1)        = U.Array n (coalesce e0) (coalesce e1)
coalesce (U.Index e0 e1)          = U.Index (coalesce e0) (coalesce e1)
coalesce (U.Case e0 bs)           = U.Case (coalesce e0)
                                           (fmap (\b -> case b of
                                                   (U.Branch'  p e0') -> U.Branch'  p (coalesce e0')
                                                   (U.Branch'' p e0') -> U.Branch'' p (coalesce e0'))
                                                 bs)
coalesce (U.Dirac e0)             = U.Dirac (coalesce e0)
coalesce (U.Bind n e0 e1)         = U.Bind n (coalesce e0) (coalesce e1)
coalesce (U.Plate n e0 e1)        = U.Plate n (coalesce e0) (coalesce e1)
coalesce (U.Chain n e0 e1 e2)     = U.Chain n (coalesce e0) (coalesce e1) (coalesce e2)
coalesce (U.Integrate n e0 e1 e2) = U.Integrate n (coalesce e0) (coalesce e1) (coalesce e2)
coalesce (U.Summate n e0 e1 e2)   = U.Summate n (coalesce e0) (coalesce e1) (coalesce e2)
coalesce (U.Product n e0 e1 e2)   = U.Product n (coalesce e0) (coalesce e1) (coalesce e2)
coalesce (U.Expect n e0 e1)       = U.Expect n (coalesce e0) (coalesce e1)
coalesce (U.Observe e0 e1)        = U.Observe (coalesce e0) (coalesce e1)
coalesce (U.Msum es)              = U.Msum (fmap coalesce es)
coalesce (U.Data n typs)          = U.Data n typs
coalesce (U.WithMeta e0 meta)     = U.WithMeta (coalesce e0) meta


coalesceNaryOp :: U.NaryOp -> [U.AST' a] -> [U.AST' a]
coalesceNaryOp op args =
  do ast' <- args
     case ast' of
       (U.NaryOp op' args') ->
         if op == op'
         then coalesceNaryOp op args' -- Typed typ args'
         else return (coalesce ast')
       _ -> return ast'


----------------------------------------------------------------
-- Typed vv

coalesceTyped :: forall abt a
              .  (ABT Term abt)
              => abt '[] a
              -> abt '[] a
coalesceTyped abt = caseVarSyn abt var onNaryOps
  where onNaryOps (NaryOp_ t es) = syn $ NaryOp_ t (coalesceNaryOpTyped t es)
        onNaryOps term           = syn term

coalesceNaryOpTyped :: ABT Term abt
                    => NaryOp a
                    -> S.Seq (abt '[] a)
                    -> S.Seq (abt '[] a)
coalesceNaryOpTyped typ args =
  do abt <- args
     case viewABT abt of
       Syn (NaryOp_ typ' args') ->
         if typ == typ'
         then coalesceNaryOpTyped typ args'
         else return (coalesceTyped abt)
       _ -> return abt
