{-# LANGUAGE FlexibleContexts
           , GADTs
           , Rank2Types
           , ScopedTypeVariables
           , DataKinds
           , TypeOperators
           , ViewPatterns
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
import Language.Hakaru.Types.DataKind

import Language.Hakaru.Expect       (expect)
import Language.Hakaru.Disintegrate (determine, observe)

import Data.Ratio (numerator, denominator)
import Language.Hakaru.Types.Sing (sing, Sing(..))
import Language.Hakaru.Types.HClasses (HFractional(..))
import Language.Hakaru.Types.Coercion (findCoercion, Coerce(..))
import qualified Data.Sequence as Seq 


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

-- if the literal might be ambiguous, i.e.
-- "1" might denote 1.nat or 1.int or 1.prob or 1.real
-- insert a coercion and convert the literal to the smallest type which represents it
-- and convert division of literals to literal rationals 
normalizeLiterals :: forall abt a. (ABT Term abt) => abt '[] a -> abt '[] a
normalizeLiterals = cataABT var bind div where 
  isLit :: abt '[] v -> Maybe (Literal v) 
  isLit (viewABT -> Syn x) = 
    case x of 
      Literal_ v -> Just v
      CoerceTo_ c :$ ((viewABT -> Syn (Literal_ v)) :* End) -> Just $ coerceTo c v
      _ -> Nothing 
  isLit _ = Nothing 

  litToRational :: Literal v -> Rational 
  litToRational (LInt i)  = toRational i 
  litToRational (LNat i)  = toRational i
  litToRational (LProb i) = toRational i 
  litToRational (LReal i) = i 

  rationalToLit :: HFractional v -> Rational -> Literal v 
  rationalToLit HFractional_Real n = LReal n
  rationalToLit HFractional_Prob n = LProb (realToFrac n) -- safe unless the AST is ill-typed

  div :: Term abt v -> abt '[] v 
  div (NaryOp_ Prod{} (Seq.viewl -> ((isLit -> Just a) 
               Seq.:< (Seq.viewl -> (viewABT -> Syn (PrimOp_ (Recip t) :$ ((isLit -> Just b) :* End)))
               Seq.:< (Seq.viewl -> Seq.EmptyL)))))
        = norm $ Literal_ $ rationalToLit t (litToRational a / litToRational b)
  div t@Literal_{} = norm t
  div t = syn t 

  norm :: Term abt v -> abt '[] v
  norm (Literal_ l) = 
    let mkc x = syn $ CoerceTo_ (maybe (error "normalizeLiterals") id $ findCoercion sing sing) 
                :$ ((syn $ Literal_ x) :* End) in 
    case l of 
      LInt i  | i >= 0 
             -> mkc (LNat $ fromIntegral i) 
  
      LProb p | denominator p == 1 
             -> mkc (LNat $ numerator p)
  
      LReal p | denominator p == 1 && numerator p >= 0
             -> mkc (LNat $ fromIntegral $ numerator p)
              | denominator p == 1 
             -> mkc (LInt $ numerator p)
              | numerator p >= 0 
             -> mkc (LProb $ realToFrac p)
  
      _      -> syn $ Literal_ l 
  norm x = syn x 
  

