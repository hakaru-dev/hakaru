{-# LANGUAGE FlexibleContexts
           , GADTs
           , ScopedTypeVariables
           , DataKinds
           , TypeOperators
           , OverloadedStrings
           , LambdaCase
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

import Language.Hakaru.Expect       (expect, expect')
import Language.Hakaru.Disintegrate (determine, observe, disintegrate)
import Language.Hakaru.Inference    (mcmc', mh')
import Language.Hakaru.Maple        (sendToMaple, MapleOptions(..)
                                    ,defaultMapleOptions, MapleCommand(..)
                                    ,MapleException)

import Data.Ratio (numerator, denominator)
import Language.Hakaru.Types.Sing (sing, Sing(..), sUnFun)
import Language.Hakaru.Types.HClasses (HFractional(..))
import Language.Hakaru.Types.Coercion (findCoercion, Coerce(..))
import qualified Data.Sequence as Seq 
import Control.Monad.Fix (MonadFix)
import Control.Monad (liftM)
import Control.Monad.Trans (MonadTrans(..))
import Control.Monad.Reader (ReaderT(..), runReaderT, local, ask)
import Control.Monad.State  (StateT(..), runStateT, put)
import Control.Applicative (Applicative(..), Alternative(..), (<$>))
import Data.Functor.Identity (Identity(..))

import Control.Exception (try)
import System.IO (stderr)
import Data.Text.Utf8 (hPutStrLn)
import Data.Text (pack)

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

--------------------------------------------------------------------------------

expandTransformations
    :: forall abt a
    . (ABT Term abt)
    => abt '[] a -> abt '[] a
expandTransformations =
  expandTransformationsWith' haskellTransformations

expandAllTransformations
    :: forall abt a
    . (ABT Term abt)
    => abt '[] a -> IO (abt '[] a)
expandAllTransformations =
  expandTransformationsWith allTransformations

expandTransformationsWith'
    :: forall abt a
    . (ABT Term abt)
    => TransformTable abt Identity
    -> abt '[] a -> abt '[] a
expandTransformationsWith' tbl =
  runIdentity . expandTransformationsWith tbl


type LetBinds' (abt :: [k] -> k -> *) = List1 (Pair1 Variable (abt '[]))
type LetBinds abt = Some1 (LetBinds' abt)
type TransformM abt m = StateT Bool (ReaderT (LetBinds abt) m)

expandTransformationsWith
    :: forall abt a m
    . (ABT Term abt, Applicative m, Monad m)
    => TransformTable abt m
    -> abt '[] a -> m (abt '[] a)
expandTransformationsWith tbl =
  fmap (\(x,d) -> (if d then prune else id) x) .
  flip runReaderT (Some1 Nil1) .
  flip runStateT False .
  go'
   where

    lets' :: LetBinds' abt vs -> abt '[] b -> abt '[] b
    lets' Nil1 x = x
    lets' (Cons1 (Pair1 var val) vs) x =
      lets' vs $ syn $ Let_ :$ val :* bind var x :* End

    lets :: LetBinds abt -> abt xs b -> abt xs b
    lets (Some1 ls) x =
      let (vs, x1) = caseBinds x
          x2       = lets' ls x1
      in binds_ vs x2

    insLet :: Variable x -> abt '[] x -> LetBinds abt -> LetBinds abt
    insLet var val (Some1 ls) = Some1 $ Cons1 (Pair1 var val) ls

    go' :: abt xs b
        -> TransformM abt m (abt xs b)
    go' = go . viewABT

    go :: View (Term abt) xs b
       -> TransformM abt m (abt xs b)
    go (Var x)    = pure $ var x
    go (Bind x e) = bind x <$> go e
    go (Syn t)    =
      (case t of
         Let_ :$ e0 :* e1 :* End -> do
           e0' <- go' e0
           e1' <- local (insLet (caseBind e1 const) e0') (go' e1)
           pure $ Let_ :$ e0' :* e1' :* End
         _ -> traverse21 go' t) >>= \t1 ->
      (case t1 of
         Transform_ tr :$ as -> ask >>= \ls ->
           let as' = fmap21 (lets ls) as
               orig = pure $ syn t1
           in maybe orig
                    (\f -> (lift.lift) (f (as, as')) >>=
                             maybe orig (\r -> put True >> return r))
                    (lookupTransform tbl tr)
         _ -> pure $ syn t1)


mapleTransformationsWithOpts
  :: forall abt
   . ABT Term abt
  => MapleOptions ()
  -> TransformTable abt IO
mapleTransformationsWithOpts opts = TransformTable $ \tr ->
  let cmd c x =
        try (sendToMaple opts{command=MapleCommand c} x) >>=
          \case
            Left (err :: MapleException) ->
              hPutStrLn stderr (pack $ show err) >> pure Nothing
            Right r ->
              pure $ Just r
      cmd :: Transform '[LC i] o
          -> abt '[] i  -> IO (Maybe (abt '[] o)) in
  case tr of
    Simplify       ->
      Just $ \ctx -> \case { e1 :* End -> cmd tr e1 }
    Summarize      ->
      Just $ \ctx -> \case { e1 :* End -> cmd tr e1 }
    Reparam        ->
      Just $ \ctx -> \case { e1 :* End -> cmd tr e1 }
    Disint InMaple ->
      Just $ \ctx -> \case { e1 :* End -> cmd tr e1 }
    _              -> Nothing

mapleTransformations
  :: ABT Term abt
  => TransformTable abt IO
mapleTransformations = mapleTransformationsWithOpts defaultMapleOptions

haskellTransformations :: (Applicative m, ABT Term abt) => TransformTable abt m
haskellTransformations = simpleTable $ \tr ->
  case tr of
    Expect ->
      Just $ \ctx -> \case
        e1 :* e2 :* End -> expect' e1 e2

    Observe ->
      Just $ \ctx -> \case
        e1 :* e2 :* End -> determine (observe e1 e2)

    MCMC ->
      Just $ \ctx -> \case
        e1 :* e2 :* End -> mcmc' e1 e2

    MH ->
      Just $ \ctx -> \case
        e1 :* e2 :* End -> mh' e1 e2

    Disint InHaskell ->
      Just $ \ctx -> \case
        e1 :* End -> determine (disintegrate e1)

    _ -> Nothing

allTransformationsWithMOpts
   :: ABT Term abt
   => MapleOptions ()
   -> TransformTable abt IO
allTransformationsWithMOpts opts = unionTable
  (mapleTransformationsWithOpts opts)
  haskellTransformations

allTransformations :: ABT Term abt => TransformTable abt IO
allTransformations = allTransformationsWithMOpts defaultMapleOptions

--------------------------------------------------------------------------------

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
