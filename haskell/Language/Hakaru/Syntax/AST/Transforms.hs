{-# LANGUAGE FlexibleContexts
           , GADTs
           , Rank2Types
           , ScopedTypeVariables
           , DataKinds
           , TypeOperators
           , ViewPatterns
           , OverloadedStrings
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
---------------------------------------------------------------
module Language.Hakaru.Syntax.AST.Transforms where

import qualified Data.Sequence as S

import Language.Hakaru.Syntax.ANF      (normalize)
import Language.Hakaru.Syntax.CSE      (cse)
import Language.Hakaru.Syntax.Prune    (prune)
import Language.Hakaru.Syntax.Uniquify (uniquify)
import Language.Hakaru.Syntax.Hoist    (hoist)
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.TypeOf
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.Prelude (lamWithVar, app)
import Language.Hakaru.Types.DataKind

import Language.Hakaru.Expect       (expect)
import Language.Hakaru.Disintegrate (determine, observe)

import Data.Ratio (numerator, denominator)
import Language.Hakaru.Types.Sing (sing, Sing(..), sUnFun)
import Language.Hakaru.Types.HClasses (HFractional(..))
import Language.Hakaru.Types.Coercion (findCoercion, Coerce(..))
import qualified Data.Sequence as Seq 
import Control.Monad.Fix (MonadFix)
import Control.Monad (liftM)

import Debug.Trace


optimizations
  :: (ABT Term abt)
  => abt '[] a
  -> abt '[] a
optimizations = uniquify
              . prune
              . cse
              . hoist
              -- The hoist pass needs globally uniqiue identifiers
              . uniquify
              . normalize

underLam
    :: (ABT Term abt, Monad m)
    => (abt '[] b -> m (abt '[] b))
    -> abt '[] (a ':-> b)
    -> m (abt '[] (a ':-> b))
underLam f e = caseVarSyn e (return . var) $ \t ->
                   case t of
                   Lam_ :$ e1 :* End ->
                       caseBind e1 $ \x e1' -> do
                           e1'' <- f e1'
                           return . syn $
                                  Lam_  :$ (bind x e1'' :* End)

                   Let_ :$ e1 :* e2 :* End ->
                        case jmEq1 (typeOf e1) (typeOf e) of
                          Just Refl -> do
                               e1' <- underLam f e1
                               return . syn $
                                      Let_ :$ e1' :* e2 :* End
                          Nothing   -> caseBind e2 $ \x e2' -> do
                                         e2'' <- underLam f e2'
                                         return . syn $
                                                Let_ :$ e1 :* (bind x e2'') :* End

                   _ -> error "TODO: underLam"

underLam'
    :: forall abt m a b b'
     . (ABT Term abt, MonadFix m)
    => (abt '[] b -> m (abt '[] b'))
    -> abt '[] (a ':-> b)
    -> m (abt '[] (a ':-> b'))
underLam' f e = do
  f' <- trace "underLam': build function" $
        liftM (\f' b -> app (syn $ Lam_ :$ f' :* End) b) $
        binderM "" (snd $ sUnFun $ typeOf e) f
  return $ underLam'p f' e

underLam'p
    :: forall abt a b b'
     . (ABT Term abt)
    => (abt '[] b -> abt '[] b')
    -> abt '[] (a ':-> b)
    -> abt '[] (a ':-> b')
underLam'p f e =
  let var_ :: Variable (a ':-> b) -> abt '[] (a ':-> b')
      var_ v_ab = trace "underLam': entered var" $
        lamWithVar "" (fst $ sUnFun $ varType v_ab) $ \a ->
        trace "underLam': applied function" $ f $ app (var v_ab) a

      syn_ t = trace "underLam': entered syn" $
        case t of
        Lam_ :$ e1 :* End -> trace "underLam': entered syn/Lam_" $
          caseBind e1 $ \x e1' ->
            trace "underLam': rebuilt Lam_" $
            syn $ Lam_  :$
                (trace "underLam': applied bind{Lam_}" $
                      bind x (trace "underLam': applied function{Lam_}"
                                $ f e1')) :* End

        Let_ :$ e1 :* e2 :* End -> trace "underLam': entered syn/Lam_" $
          caseBind e2 $ \x e2' ->
            trace "underLam': rebuilt Let_" $
            syn $ Let_ :$ e1 :*
                  (trace "underLam': applied bind{Lam_}" $
                         bind x (trace "underLam': recursive case{Let_}" $
                                       go e2')) :* End

        _ -> error "TODO: underLam'"

      go e' = trace "underLam': entered main body" $
              caseVarSyn e' var_ syn_
  in go e

expandTransformations
    :: forall abt a
    . (ABT Term abt)
    => abt '[] a -> abt '[] a
expandTransformations =
    cataABT var bind alg
    where 
    alg :: forall b. Term abt b -> abt '[] b
    alg t =
        case t of
        Expect  :$ e1 :* e2 :* End -> expect  e1 e2
        Observe :$ e1 :* e2 :* End ->
          case determine (observe e1 e2) of
          Just t' -> t'
          Nothing -> syn t
        _                         -> syn t
        
coalesce
  :: forall abt a
  .  (ABT Term abt)
  => abt '[] a
  -> abt '[] a
coalesce abt = caseVarSyn abt var onNaryOps
  where onNaryOps (NaryOp_ t es) = syn $ NaryOp_ t (coalesceNaryOp t es)
        onNaryOps term           = syn term

coalesceNaryOp
  :: ABT Term abt
  => NaryOp a
  -> S.Seq (abt '[] a)
  -> S.Seq (abt '[] a)
coalesceNaryOp typ args =
  do abt <- args
     case viewABT abt of
       Syn (NaryOp_ typ' args') ->
         if typ == typ'
         then coalesceNaryOp typ args'
         else return (coalesce abt)
       _ -> return abt
