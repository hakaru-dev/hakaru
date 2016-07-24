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

coalesce :: U.AST
         -> U.AST
coalesce (U.Var_ n)                = U.Var_ n
coalesce (U.Lam_ n typ e1)         = U.Lam_ n typ (coalesce e1)
coalesce (U.App_ e0 e1)            = U.App_ (coalesce e0) (coalesce e1)
coalesce (U.Let_ n e0 e1)          = U.Let_ n (coalesce e0) (coalesce e1)
coalesce (U.Ann_ e0 typ)           = U.Ann_ (coalesce e0) typ
coalesce (U.CoerceTo_ c e)         = U.CoerceTo_ c (coalesce e)
coalesce (U.UnsafeTo_ c e)         = U.UnsafeTo_ c (coalesce e)
coalesce (U.PrimOp_ op es)         = U.PrimOp_ op (fmap coalesce es)
coalesce (U.ArrayOp_ op es)        = U.ArrayOp_ op (fmap coalesce es)
coalesce (U.NaryOp_ op es)         = U.NaryOp_ op (coalesceNaryOp op es)
coalesce (U.Literal_ lit)          = U.Literal_ lit
coalesce U.Empty_                  = U.Empty_
coalesce (U.Pair_ e0 e1)           = U.Pair_ (coalesce e0) (coalesce e1)
coalesce (U.Array_ e0 n e1)        = U.Array_ (coalesce e0) n (coalesce e1)
coalesce (U.Datum_ d)              = U.Datum_ (coalesceDatum d)
coalesce (U.Case_ e0 bs)           = U.Case_ (coalesce e0)
                                             (fmap (\(U.Branch pat e) ->
                                                   U.Branch pat (coalesce e))
                                                   bs)
coalesce (U.MeasureOp_ op es)      = U.MeasureOp_ op (fmap coalesce es)
coalesce (U.Dirac_ e0)             = U.Dirac_ (coalesce e0)
coalesce (U.MBind_ n e0 e1)        = U.MBind_ n (coalesce e0) (coalesce e1)
coalesce (U.Plate_ n e0 e1)        = U.Plate_ n (coalesce e0) (coalesce e1)
coalesce (U.Chain_ n e0 e1 e2)     = U.Chain_ n (coalesce e0) (coalesce e1) (coalesce e2)
coalesce (U.Integrate_ n e0 e1 e2) = U.Integrate_ n (coalesce e0) (coalesce e1) (coalesce e2)
coalesce (U.Summate_ n e0 e1 e2)   = U.Summate_ n (coalesce e0) (coalesce e1) (coalesce e2)
coalesce (U.Product_ n e0 e1 e2)   = U.Product_ n (coalesce e0) (coalesce e1) (coalesce e2)
coalesce (U.Expect_ n e0 e1)       = U.Expect_ n (coalesce e0) (coalesce e1)
coalesce (U.Observe_ e0 e1)        = U.Observe_ (coalesce e0) (coalesce e1)
coalesce (U.Superpose_ es)         = U.Superpose_ (fmap (\(a,b) ->
                                                          (coalesce a, coalesce b)) es)
coalesce U.Reject_                 = U.Reject_


coalesceNaryOp :: U.NaryOp -> [U.AST] -> [U.AST]
coalesceNaryOp op args =
  do ast' <- args
     case ast' of
       (U.NaryOp_ op' args') ->
         if op == op'
         then coalesceNaryOp op args' -- Typed typ args'
         else return (coalesce ast')
       _ -> return ast'

coalesceDatum :: U.Datum -> U.Datum
coalesceDatum (U.Datum t xss) = U.Datum t (coalesceDCode xss)

coalesceDCode :: U.DCode -> U.DCode
coalesceDCode (U.Inr xss) = U.Inr (coalesceDCode xss)
coalesceDCode (U.Inl xs)  = U.Inl (coalesceDStruct xs)

coalesceDStruct :: U.DStruct -> U.DStruct
coalesceDStruct U.Done      = U.Done
coalesceDStruct (U.Et x xs) = U.Et (coalesceDFun x) (coalesceDStruct xs)

coalesceDFun :: U.DFun -> U.DFun
coalesceDFun (U.Konst x) = U.Konst (coalesce x)
coalesceDFun (U.Ident x) = U.Ident (coalesce x)



