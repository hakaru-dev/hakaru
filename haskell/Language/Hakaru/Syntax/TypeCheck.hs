{-# LANGUAGE CPP
           , ScopedTypeVariables
           , GADTs
           , DataKinds
           , KindSignatures
           , GeneralizedNewtypeDeriving
           , TypeOperators
           , FlexibleContexts
           , FlexibleInstances
           , OverloadedStrings
           , PatternGuards
           , Rank2Types
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.05.28
-- |
-- Module      :  Language.Hakaru.Syntax.TypeCheck
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Bidirectional type checking for our AST.
----------------------------------------------------------------
module Language.Hakaru.Syntax.TypeCheck
    (
    -- * The type checking monad
      TypeCheckError
    , TypeCheckMonad(), runTCM, unTCM
    , TypeCheckMode(..)
    -- * Type checking itself
    , inferable
    , mustCheck
    , TypedAST(..)
    , onTypedAST, onTypedASTM, elimTypedAST
    , inferType
    , checkType
    ) where

import           Prelude hiding (id, (.))
import           Control.Category
import           Data.Proxy            (KProxy(..))
import           Data.Text             (pack, Text())
import           Data.Either           (partitionEithers)
import qualified Data.IntMap           as IM
import qualified Data.Traversable      as T
import qualified Data.List.NonEmpty    as L
import qualified Data.Foldable         as F
import qualified Data.Sequence         as S
import qualified Data.Vector           as V
#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..), (<$>))
import           Data.Monoid           (Monoid(..))
#endif
import qualified Language.Hakaru.Parser.AST as U

import Data.Number.Nat                (fromNat)
import Language.Hakaru.Syntax.TypeCheck.TypeCheckMonad
import Language.Hakaru.Syntax.TypeCheck.Unification
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Types.DataKind (Hakaru(..), HData', HBool)
import Language.Hakaru.Types.Sing
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Types.HClasses
    ( HEq, hEq_Sing, HOrd, hOrd_Sing, HSemiring, hSemiring_Sing
    , hRing_Sing, sing_HRing, hFractional_Sing, sing_HFractional
    , sing_NonNegative, hDiscrete_Sing
    , HIntegrable(..)
    , HRadical(..), HContinuous(..))
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.Reducer
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.AST.Sing
    (sing_Literal, sing_MeasureOp)
import Language.Hakaru.Pretty.Concrete (prettyType, prettyTypeT)
import Language.Hakaru.Syntax.TypeOf (typeOf)
import Language.Hakaru.Syntax.Prelude (triv)

----------------------------------------------------------------
----------------------------------------------------------------

-- | Those terms from which we can synthesize a unique type. We are
-- also allowed to check them, via the change-of-direction rule.
inferable :: U.AST -> Bool
inferable = not . mustCheck


-- | Those terms whose types must be checked analytically. We cannot
-- synthesize (unambiguous) types for these terms.
--
-- N.B., this function assumes we're in 'StrictMode'. If we're
-- actually in 'LaxMode' then a handful of AST nodes behave
-- differently: in particular, 'U.NaryOp_', 'U.Superpose', and
-- 'U.Case_'. In strict mode those cases can just infer one of their
-- arguments and then check the rest against the inferred type.
-- (For case-expressions, we must also check the scrutinee since
-- it's type cannot be unambiguously inferred from the patterns.)
-- Whereas in lax mode we must infer all arguments and then take
-- the lub of their types in order to know which coercions to
-- introduce.
mustCheck :: U.AST -> Bool
mustCheck e = caseVarSyn e (const False) go
    where
    go :: U.MetaTerm -> Bool
    go (U.Lam_ _  e2)     = mustCheck' e2

    -- In general, applications don't require checking; we infer
    -- the first applicand to get the type of the second and of the
    -- result, then we check the second and return the result type.
    -- Thus, applications will only yield \"must check\" errors if
    -- the function does; but that's the responsability of the
    -- function term, not of the application term it's embedded
    -- within.
    --
    -- However, do note that the above only applies to lambda-defined
    -- functions, not to all \"function-like\" things. In particular,
    -- data constructors require checking (see the note below).
    go (U.App_ _  _)      = False

    -- We follow Dunfield & Pientka and \Pi\Sigma in inferring or
    -- checking depending on what the body requires. This is as
    -- opposed to the TLDI'05 paper, which always infers @e2@ but
    -- will check or infer the @e1@ depending on whether it has a
    -- type annotation or not.
    go (U.Let_ _ e2)      = mustCheck' e2

    go (U.Ann_ _ _)       = False
    go (U.CoerceTo_ _ _)  = False
    go (U.UnsafeTo_ _ _)  = False

    -- In general (according to Dunfield & Pientka), we should be
    -- able to infer the result of a fully saturated primop by
    -- looking up it's type and then checking all the arguments.
    go (U.PrimOp_  _ _)   = False
    go (U.ArrayOp_ _ es)  = F.all mustCheck es

    -- In strict mode: if we can infer any of the arguments, then
    -- we can check all the rest at the same type.
    --
    -- BUG: in lax mode we must be able to infer all of them;
    -- otherwise we may not be able to take the lub of the types
    go (U.NaryOp_   _ es) = F.all mustCheck es
    go (U.Superpose_ pes) = F.all (mustCheck . snd) pes

    -- Our numeric literals aren't polymorphic, so we can infer
    -- them just fine. Or rather, according to our AST they aren't;
    -- in truth, they are in the surface language. Which is part
    -- of the reason for needing 'LaxMode'
    --
    -- TODO: correctly capture our surface-language semantics by
    -- always treating literals as if we're in 'LaxMode'.
    go (U.Literal_ _) = False

    -- I return true because most folks (neelk, Pfenning, Dunfield
    -- & Pientka) say all data constructors mustCheck. The main
    -- issue here is dealing with (polymorphic) sum types and phantom
    -- types, since these mean the term doesn't contain enough
    -- information for all the type indices. Even for record types,
    -- there's the additional issue of the term (perhaps) not giving
    -- enough information about the nominal type even if it does
    -- give enough info for the structural type.
    --
    -- Still, given those limitations, we should be able to infer
    -- a subset of data constructors which happen to avoid the
    -- problem areas. In particular, given that our surface syntax
    -- doesn't use the sum-of-products representation, we should
    -- be able to rely on symbol resolution to avoid the nominal
    -- typing issue. Thus, for non-empty arrays and non-phantom
    -- record types, we should be able to infer the whole type
    -- provided we can infer the various subterms.
    go (U.Pair_ e1 e2)      = mustCheck  e1 && mustCheck e2
    go (U.Array_ _ e1)      = mustCheck' e1
    go (U.ArrayLiteral_ es) = F.all mustCheck es
    go (U.Datum_ _)         = True

    -- TODO: everyone says this, but it seems to me that if we can
    -- infer any of the branches (and check the rest to agree) then
    -- we should be able to infer the whole thing... Or maybe the
    -- problem is that the change-of-direction rule might send us
    -- down the wrong path?
    go (U.Case_ _ _)     = True

    go (U.Dirac_  e1)        = mustCheck  e1
    go (U.MBind_  _   e2)    = mustCheck' e2
    go (U.Plate_  _   e2)    = mustCheck' e2
    go (U.Chain_  _   e2 e3) = mustCheck  e2 && mustCheck' e3
    go (U.MeasureOp_ _ _)    = False
    go (U.Integrate_  _ _ _) = False
    go (U.Summate_    _ _ _) = False
    go (U.Product_    _ _ _) = False
    go (U.Bucket_     _ _ _) = False
    go U.Reject_             = True
    go (U.Transform_ tr es ) =
      case (tr, es) of
        (Expect   , (Nil2, e1) U.:* _ U.:* U.End)
          -> mustCheck e1
        (Observe  , (Nil2, e1) U.:* _ U.:* U.End)
          -> mustCheck e1
        (MCMC     , (Nil2, e1) U.:* (Nil2, e2) U.:* U.End)
          -> mustCheck e1 && mustCheck e2
        (Disint _ , (Nil2, e1) U.:* U.End)
          -> mustCheck e1
        (Simplify , (Nil2, e1) U.:* U.End)
          -> mustCheck e1
        (Summarize, (Nil2, e1) U.:* U.End)
          -> mustCheck e1
        (Reparam  , (Nil2, e1) U.:* U.End)
          -> mustCheck e1
    go U.InjTyped{}          = False

mustCheck'
    :: MetaABT U.SourceSpan U.Term '[ 'U.U ] 'U.U
    -> Bool
mustCheck' e = caseBind e $ \_ e' -> mustCheck e'

inferBinder
    :: (ABT Term abt)
    => Sing a
    -> MetaABT U.SourceSpan U.Term '[ 'U.U ] 'U.U
    -> (forall b. Sing b -> abt '[ a ] b -> TypeCheckMonad r)
    -> TypeCheckMonad r
inferBinder typ e k =
    caseBind e $ \x e1 -> do
    let x' = x {varType = typ}
    TypedAST typ1 e1' <- pushCtx x' (inferType e1)
    k typ1 (bind x' e1')

inferBinders
    :: (ABT Term abt)
    => List1 Variable xs
    -> U.AST
    -> (forall a. Sing a -> abt xs a -> TypeCheckMonad r)
    -> TypeCheckMonad r
inferBinders = \xs e k -> do
    TypedAST typ e' <- pushesCtx xs (inferType e)
    k typ (binds_ xs e')
    where
    -- TODO: make sure the 'TCM'\/'unTCM' stuff doesn't do stupid asymptotic things
    pushesCtx
        :: List1 Variable (xs :: [Hakaru])
        -> TypeCheckMonad b
        -> TypeCheckMonad b
    pushesCtx Nil1         m = m
    pushesCtx (Cons1 x xs) m = pushesCtx xs (TCM (unTCM m . insertVarSet x))


checkBinder
    :: (ABT Term abt)
    => Sing a
    -> Sing b
    -> MetaABT U.SourceSpan U.Term '[ 'U.U ] 'U.U
    -> TypeCheckMonad (abt '[ a ] b)
checkBinder typ eTyp e =
    caseBind e $ \x e1 -> do
    let x' = x {varType = typ}
    pushCtx x' (bind x' <$> checkType eTyp e1)


checkBinders
    :: (ABT Term abt)
    => List1 Variable xs
    -> Sing a
    -> U.AST
    -> TypeCheckMonad (abt xs a)
checkBinders xs eTyp e =
    case xs of
    Nil1        -> checkType eTyp e
    Cons1 x xs' -> pushCtx x (bind x <$> checkBinders xs' eTyp e)

----------------------------------------------------------------
-- | Given a typing environment and a term, synthesize the term's
-- type (and produce an elaborated term):
--
-- > Γ ⊢ e ⇒ e' ∈ τ
inferType
    :: forall abt
    .  (ABT Term abt)
    => U.AST
    -> TypeCheckMonad (TypedAST abt)
inferType = inferType_
  where
  -- HACK: we need to give these local definitions to avoid
  -- \"ambiguity\" in the choice of ABT instance...
  checkType_ :: forall b. Sing b -> U.AST -> TypeCheckMonad (abt '[] b)
  checkType_ = checkType

  inferOneCheckOthers_ ::
      [U.AST] -> TypeCheckMonad (TypedASTs abt)
  inferOneCheckOthers_ = inferOneCheckOthers


  inferVariable
      :: Maybe U.SourceSpan
      -> Variable 'U.U
      -> TypeCheckMonad (TypedAST abt)
  inferVariable sourceSpan (Variable hintID nameID _) = do
      ctx <- getCtx
      case IM.lookup (fromNat nameID) (unVarSet ctx) of
        Just (SomeVariable x') ->
            return $ TypedAST (varType x') (var x')
        Nothing -> ambiguousFreeVariable hintID sourceSpan


  -- HACK: We need this monomorphic binding so that GHC doesn't get
  -- confused about which @(ABT AST abt)@ instance to use in recursive
  -- calls.
  inferType_ :: U.AST -> TypeCheckMonad (TypedAST abt)
  inferType_ e0 =
    let s = getMetadata e0 in
    caseVarSyn e0 (inferVariable s) (go s)
    where
    go :: Maybe U.SourceSpan -> U.MetaTerm -> TypeCheckMonad (TypedAST abt)
    go sourceSpan t =
      case t of
       U.Lam_ (U.SSing typ) e -> do
           inferBinder typ e $ \typ2 e2 ->
               return . TypedAST (SFun typ typ2) $ syn (Lam_ :$ e2 :* End)

       U.App_ e1 e2 -> do
           TypedAST typ1 e1' <- inferType_ e1
           unifyFun typ1 sourceSpan $ \typ2 typ3 -> do
            e2' <- checkType_ typ2 e2
            return . TypedAST typ3 $ syn (App_ :$ e1' :* e2' :* End)

           -- case typ1 of
           --     SFun typ2 typ3 -> do
           --         e2' <- checkType_ typ2 e2
           --         return . TypedAST typ3 $ syn (App_ :$ e1' :* e2' :* End)
           --     _ -> typeMismatch sourceSpan (Left "function type") (Right typ1)
           -- The above is the standard rule that everyone uses.
           -- However, if the @e1@ is a lambda (rather than a primop
           -- or a variable), then it will require a type annotation.
           -- Couldn't we just as well add an additional rule that
           -- says to infer @e2@ and then infer @e1@ under the assumption
           -- that the variable has the same type as the argument? (or
           -- generalize that idea to keep track of a bunch of arguments
           -- being passed in; sort of like a dual to our typing
           -- environments?) Is this at all related to what Dunfield
           -- & Neelk are doing in their ICFP'13 paper with that
           -- \"=>=>\" judgment? (prolly not, but...)

       U.Let_ e1 e2 -> do
           TypedAST typ1 e1' <- inferType_ e1
           inferBinder typ1 e2 $ \typ2 e2' ->
               return . TypedAST typ2 $ syn (Let_ :$ e1' :* e2' :* End)

       U.Ann_ (U.SSing typ1) e1 -> do
           -- N.B., this requires that @typ1@ is a 'Sing' not a 'Proxy',
           -- since we can't generate a 'Sing' from a 'Proxy'.
           TypedAST typ1 <$> checkType_ typ1 e1

       U.PrimOp_  op es -> inferPrimOp  op es
       U.ArrayOp_ op es -> inferArrayOp op es
       U.NaryOp_  op es -> do
           mode <- getMode
           TypedASTs typ es' <-
               case mode of
               StrictMode -> inferOneCheckOthers_ es
               LaxMode    -> inferLubType sourceSpan es
               UnsafeMode -> inferLubType sourceSpan es
           op' <- make_NaryOp typ op
           return . TypedAST typ $ syn (NaryOp_ op' $ S.fromList es')

       U.Literal_ (Some1 v) ->
           -- TODO: in truth, we can infer this to be any supertype
           -- (adjusting the concrete @v@ as necessary). That is, the
           -- surface language treats numeric literals as polymorphic,
           -- so we should capture that somehow--- even if we're not
           -- in 'LaxMode'. We'll prolly need to handle this
           -- subtype-polymorphism the same way as we do for for
           -- everything when in 'UnsafeMode'.
           return . TypedAST (sing_Literal v) $ syn (Literal_ v)

       -- TODO: we can try to do 'U.Case_' by using branch-based
       -- variants of 'inferOneCheckOthers' and 'inferLubType' depending
       -- on the mode; provided we can in fact infer the type of the
       -- scrutinee. N.B., if we add this case, then we need to update
       -- 'mustCheck' to return the right thing.

       U.CoerceTo_ (Some2 c) e1 ->
           case singCoerceDomCod c of
           Nothing
               | inferable e1 -> inferType_ e1
               | otherwise    -> ambiguousNullCoercion sourceSpan
           Just (dom,cod) -> do
               e1' <- checkType_ dom e1
               return . TypedAST cod $ syn (CoerceTo_ c :$ e1' :* End)

       U.UnsafeTo_ (Some2 c) e1 ->
           case singCoerceDomCod c of
           Nothing
               | inferable e1 -> inferType_ e1
               | otherwise    -> ambiguousNullCoercion sourceSpan
           Just (dom,cod) -> do
               e1' <- checkType_ cod e1
               return . TypedAST dom $ syn (UnsafeFrom_ c :$ e1' :* End)

       U.MeasureOp_ (U.SomeOp op) es -> do
           let (typs, typ1) = sing_MeasureOp op
           es' <- checkSArgs typs es
           return . TypedAST (SMeasure typ1) $ syn (MeasureOp_ op :$ es')

       U.Pair_ e1 e2 -> do
           TypedAST typ1 e1' <- inferType_ e1
           TypedAST typ2 e2' <- inferType_ e2
           return . TypedAST (sPair typ1 typ2) $
                  syn (Datum_ $ dPair_ typ1 typ2 e1' e2')

       U.Array_ e1 e2 -> do
           e1' <- checkType_ SNat e1
           inferBinder SNat e2 $ \typ2 e2' ->
               return . TypedAST (SArray typ2) $ syn (Array_ e1' e2')

       U.ArrayLiteral_ es -> do
           mode <- getMode
           TypedASTs typ es' <-
               case mode of
                 StrictMode -> inferOneCheckOthers_ es
                 LaxMode    -> inferLubType sourceSpan es
                 UnsafeMode -> inferLubType sourceSpan es
           return . TypedAST (SArray typ) $ syn (ArrayLiteral_ es')

       U.Case_ e1 branches -> do
           TypedAST typ1 e1' <- inferType_ e1
           mode <- getMode
           case mode of
               StrictMode -> inferCaseStrict typ1 e1' branches
               LaxMode    -> inferCaseLax sourceSpan typ1 e1' branches
               UnsafeMode -> inferCaseLax sourceSpan typ1 e1' branches

       U.Dirac_ e1 -> do
           TypedAST typ1 e1' <- inferType_ e1
           return . TypedAST (SMeasure typ1) $ syn (Dirac :$ e1' :* End)

       U.MBind_ e1 e2 ->
           caseBind e2 $ \x e2' -> do
           TypedAST typ1 e1' <- inferType_ e1
           unifyMeasure typ1 sourceSpan $ \typ2 ->
            let x' = makeVar x typ2 in
            pushCtx x' $ do
             TypedAST typ3 e3' <- inferType_ e2'
             unifyMeasure typ3 sourceSpan $ \_ ->
              return . TypedAST typ3 $ syn (MBind :$ e1' :* bind x' e3' :* End)

       U.Plate_ e1 e2 ->
           caseBind e2 $ \x e2' -> do
           e1' <- checkType_ SNat e1
           let x' = makeVar x SNat
           pushCtx x' $ do
            TypedAST typ2 e3' <- inferType_ e2'
            unifyMeasure typ2 sourceSpan $ \typ3 ->
             return . TypedAST (SMeasure . SArray $ typ3) $
              syn (Plate :$ e1' :* bind x' e3' :* End)

       U.Chain_ e1 e2 e3 ->
           caseBind e3 $ \x e3' -> do
           e1' <- checkType_ SNat e1
           TypedAST typ2 e2' <- inferType_ e2
           let x' = makeVar x typ2
           pushCtx x' $ do
               TypedAST typ3 e4' <- inferType_ e3'
               unifyMeasure typ3 sourceSpan $ \typ4 ->
                unifyPair typ4 sourceSpan $ \a b ->
                matchTypes typ2 b sourceSpan () () $
                 return . TypedAST (SMeasure $ sPair (SArray a) typ2) $
                 syn (Chain :$ e1' :* e2' :* bind x' e4' :* End)

       U.Integrate_ e1 e2 e3 -> do
           e1' <- checkType_ SReal e1
           e2' <- checkType_ SReal e2
           e3' <- checkBinder SReal SProb e3
           return . TypedAST SProb $
                  syn (Integrate :$ e1' :* e2' :* e3' :* End)

       U.Summate_ e1 e2 e3 -> do
           TypedAST typ1 e1' <- inferType e1
           e2' <- checkType_ typ1 e2
           inferBinder typ1 e3 $ \typ2 ee' ->
               case (hDiscrete_Sing typ1, hSemiring_Sing typ2) of
                 (Just h1, Just h2) ->
                     return . TypedAST typ2 $
                            syn (Summate h1 h2 :$ e1' :* e2' :* ee' :* End)
                 _                  -> failwith_ "Summate given bounds which are not discrete"

       U.Product_ e1 e2 e3 -> do
           TypedAST typ1 e1' <- inferType e1
           e2' <- checkType_ typ1 e2
           inferBinder typ1 e3 $ \typ2 e3' ->
               case (hDiscrete_Sing typ1, hSemiring_Sing typ2) of
                 (Just h1, Just h2) ->
                     return . TypedAST typ2 $
                            syn (Product h1 h2 :$ e1' :* e2' :* e3' :* End)
                 _                  -> failwith_ "Product given bounds which are not discrete"

       U.Bucket_ e1 e2 r1 -> do
           e1' <- checkType_ SNat e1
           e2' <- checkType_ SNat e2
           TypedReducer typ1 Nil1 r1' <- inferReducer r1 Nil1
           return . TypedAST typ1 $
                  syn (Bucket e1' e2' r1')

       U.Transform_ tr es -> inferTransform sourceSpan tr es

       U.Superpose_ pes -> do
           -- TODO: clean up all this @map fst@, @map snd@, @zip@ stuff
           mode <- getMode
           TypedASTs typ es' <-
               case mode of
               StrictMode -> inferOneCheckOthers_    (L.toList $ fmap snd pes)
               LaxMode    -> inferLubType sourceSpan (L.toList $ fmap snd pes)
               UnsafeMode -> inferLubType sourceSpan (L.toList $ fmap snd pes)
           unifyMeasure typ sourceSpan $ \_ -> do
            ps' <- T.traverse (checkType SProb) (fmap fst pes)
            return $ TypedAST typ (syn (Superpose_ (L.zip ps' (L.fromList es'))))

       U.InjTyped t     -> let t' = t in return $ TypedAST (typeOf t') t'

       _   | mustCheck e0 -> ambiguousMustCheck sourceSpan
           | otherwise    -> error "inferType: missing an inferable branch!"

  inferTransform
      :: Maybe U.SourceSpan
      -> Transform as x
      -> U.SArgs U.U_ABT as
      -> TypeCheckMonad (TypedAST abt)
  inferTransform sourceSpan
                 Expect
                 ((Nil2, e1) U.:* (Cons2 U.ToU Nil2, e2) U.:* U.End) = do
    let e1src = getMetadata e1
    TypedAST typ1 e1' <- inferType_ e1
    unifyMeasure typ1 e1src $ \typ2 -> do
     e2' <- checkBinder typ2 SProb e2
     return . TypedAST SProb $ syn
       (Transform_ Expect :$ e1' :* e2' :* End)

  inferTransform sourceSpan
                 Observe
                 ((Nil2, e1) U.:* (Nil2, e2) U.:* U.End) = do
    let e1src = getMetadata e1
    TypedAST typ1 e1' <- inferType_ e1
    unifyMeasure typ1 e1src $ \typ2 -> do
     e2' <- checkType_ typ2 e2
     return . TypedAST typ1 $ syn
       (Transform_ Observe :$ e1' :* e2' :* End)

  inferTransform sourceSpan
                 MCMC
                 ((Nil2, e1) U.:* (Nil2, e2) U.:* U.End) = do
    let e1src = getMetadata e1
        e2src = getMetadata e2
    TypedAST typ1 e1' <- inferType_ e1
    TypedAST typ2 e2' <- inferType_ e2
    unifyFun     typ1  e1src $ \typa typmb ->
     unifyMeasure typmb e1src $ \typb ->
     unifyMeasure typ2  e2src $ \typc ->
     matchTypes typa typb e1src (SFun typa (SMeasure typa)) typ1 $
     matchTypes typb typc e2src typmb typ2 $
     return $ TypedAST (SFun typa (SMeasure typa))
            $ syn $ Transform_ MCMC :$ e1' :* e2' :* End

  inferTransform sourceSpan
                 (Disint k)
                 ((Nil2, e1) U.:* U.End) = do
    let e1src = getMetadata e1
    TypedAST typ1 e1' <- inferType_ e1
    unifyMeasure typ1 e1src $ \typ2 ->
     unifyPair typ2 e1src $ \typa typb ->
     return $ TypedAST (SFun typa (SMeasure typb)) $
     syn $ Transform_ (Disint k) :$ e1' :* End

  inferTransform sourceSpan
                 Simplify
                 ((Nil2, e1) U.:* U.End) = do
    TypedAST typ1 e1' <- inferType_ e1
    return $ TypedAST typ1 $ syn (Transform_ Simplify :$ e1' :* End)

  inferTransform sourceSpan
                 Reparam
                 ((Nil2, e1) U.:* U.End) = do
    TypedAST typ1 e1' <- inferType_ e1
    return $ TypedAST typ1 $ syn (Transform_ Reparam :$ e1' :* End)

  inferTransform sourceSpan
                 Summarize
                 ((Nil2, e1) U.:* U.End) = do
    TypedAST typ1 e1' <- inferType_ e1
    return $ TypedAST typ1 $ syn (Transform_ Summarize :$ e1' :* End)

  inferTransform _ tr _ = error $ "inferTransform{" ++ show tr ++ "}: TODO"

  inferPrimOp
      :: U.PrimOp
      -> [U.AST]
      -> TypeCheckMonad (TypedAST abt)
  inferPrimOp U.Not es =
      case es of
        [e] -> do e' <- checkType_ sBool e
                  return . TypedAST sBool $ syn (PrimOp_ Not :$ e' :* End)
        _   -> argumentNumberError

  inferPrimOp U.Pi es =
      case es of
        [] -> return . TypedAST SProb $ syn (PrimOp_ Pi :$ End)
        _  -> argumentNumberError

  inferPrimOp U.Cos es =
      case es of
        [e] -> do e' <- checkType_ SReal e
                  return . TypedAST SReal $ syn (PrimOp_ Cos :$ e' :* End)
        _   -> argumentNumberError

  inferPrimOp U.RealPow es =
      case es of
        [e1, e2] -> do e1' <- checkType_ SProb e1
                       e2' <- checkType_ SReal e2
                       return . TypedAST SProb $
                              syn (PrimOp_ RealPow :$ e1' :* e2' :* End)
        _        -> argumentNumberError

  inferPrimOp U.Choose es =
      case es of 
        [e1, e2] -> do e1' <- checkType_ SNat e1
                       e2' <- checkType_ SNat e2
                       return . TypedAST SNat $
                              syn (PrimOp_ Choose :$ e1' :* e2' :* End)
        _        -> argumentNumberError

  inferPrimOp U.Exp es =
      case es of
        [e] -> do e' <- checkType_ SReal e
                  return . TypedAST SProb $ syn (PrimOp_ Exp :$ e' :* End)
        _   -> argumentNumberError

  inferPrimOp U.Log es =
      case es of
        [e] -> do e' <- checkType_ SProb e
                  return . TypedAST SReal $ syn (PrimOp_ Log :$ e' :* End)
        _   -> argumentNumberError

  inferPrimOp U.Infinity es =
      case es of
        [] -> return . TypedAST SProb $
                     syn (PrimOp_ (Infinity HIntegrable_Prob) :$ End)
        _  -> argumentNumberError

  inferPrimOp U.GammaFunc es =
      case es of
        [e] -> do e' <- checkType_ SReal e
                  return . TypedAST SProb $ syn (PrimOp_ GammaFunc :$ e' :* End)
        _   -> argumentNumberError

  inferPrimOp U.BetaFunc es =
      case es of
        [e1, e2] -> do e1' <- checkType_ SProb e1
                       e2' <- checkType_ SProb e2
                       return . TypedAST SProb $
                              syn (PrimOp_ BetaFunc :$ e1' :* e2' :* End)
        _        -> argumentNumberError

  inferPrimOp U.Equal es =
      case es of
        [_, _] -> do mode <- getMode
                     TypedASTs typ [e1', e2'] <-
                         case mode of
                           StrictMode -> inferOneCheckOthers_ es
                           _          -> inferLubType Nothing es
                     primop <- Equal <$> getHEq typ
                     return . TypedAST sBool $
                            syn (PrimOp_ primop :$ e1' :* e2' :* End)
        _      -> argumentNumberError

  inferPrimOp U.Less es =
      case es of
        [_, _] -> do mode <- getMode
                     TypedASTs typ [e1', e2'] <-
                         case mode of
                           StrictMode -> inferOneCheckOthers_ es
                           _          -> inferLubType Nothing es
                     primop <- Less <$> getHOrd typ
                     return . TypedAST sBool $
                            syn (PrimOp_ primop :$ e1' :* e2' :* End)
        _      -> argumentNumberError

  inferPrimOp U.NatPow es =
      case es of
        [e1, e2] -> do TypedAST typ e1' <- inferType_ e1
                       e2' <- checkType_ SNat e2
                       primop <- NatPow <$> getHSemiring typ
                       return . TypedAST typ $
                              syn (PrimOp_ primop :$ e1' :* e2' :* End)
        _        -> argumentNumberError

  inferPrimOp U.Negate es =
      case es of
        [e] -> do TypedAST typ e' <- inferType_ e
                  mode <- getMode
                  SomeRing ring c <- getHRing typ mode
                  primop <- Negate <$> return ring
                  let e'' = case c of
                              CNil -> e'
                              c'   -> unLC_ . coerceTo c' $ LC_ e'
                  return . TypedAST (sing_HRing ring) $
                         syn (PrimOp_ primop :$ e'' :* End)
        _   -> argumentNumberError

  inferPrimOp U.Abs es =
      case es of
        [e] -> do TypedAST typ e' <- inferType_ e
                  mode <- getMode
                  SomeRing ring c <- getHRing typ mode
                  primop <- Abs <$> return ring
                  let e'' = case c of
                              CNil -> e'
                              c'   -> unLC_ . coerceTo c' $ LC_ e'
                  return . TypedAST (sing_NonNegative ring) $
                         syn (PrimOp_ primop :$ e'' :* End)
        _   -> argumentNumberError

  inferPrimOp U.Signum es =
      case es of
        [e] -> do TypedAST typ e' <- inferType_ e
                  mode <- getMode
                  SomeRing ring c <- getHRing typ mode
                  primop <- Signum <$> return ring
                  let e'' = case c of
                              CNil -> e'
                              c'   -> unLC_ . coerceTo c' $ LC_ e'
                  return . TypedAST (sing_HRing ring) $
                         syn (PrimOp_ primop :$ e'' :* End)
        _   -> argumentNumberError

  inferPrimOp U.Recip es =
      case es of
        [e] -> do TypedAST typ e' <- inferType_ e
                  mode <- getMode
                  SomeFractional frac c <- getHFractional typ mode
                  primop <- Recip <$> return frac
                  let e'' = case c of
                              CNil -> e'
                              c'   -> unLC_ . coerceTo c' $ LC_ e'
                  return . TypedAST (sing_HFractional frac) $
                         syn (PrimOp_ primop :$ e'' :* End)
        _   -> argumentNumberError

  -- BUG: Only defined for HRadical_Prob
  inferPrimOp U.NatRoot es =
      case es of
        [e1, e2] -> do e1' <- checkType_ SProb e1
                       e2' <- checkType_ SNat  e2
                       return . TypedAST SProb $
                              syn (PrimOp_ (NatRoot HRadical_Prob)
                                   :$ e1' :* e2' :* End)
        _   -> argumentNumberError

  -- BUG: Only defined for HContinuous_Real
  inferPrimOp U.Erf es =
      case es of
        [e] -> do e' <- checkType_ SReal e
                  return . TypedAST SReal $
                         syn (PrimOp_ (Erf HContinuous_Real)
                              :$ e' :* End)
        _   -> argumentNumberError

  inferPrimOp x es
      | Just y <- lookup x
                 [(U.Sin  , Sin  ),
                  (U.Cos  , Cos  ),
                  (U.Tan  , Tan  ),
                  (U.Asin , Asin ),
                  (U.Acos , Acos ),
                  (U.Atan , Atan ),
                  (U.Sinh , Sinh ),
                  (U.Cosh , Cosh ),
                  (U.Tanh , Tanh ),
                  (U.Asinh, Asinh),
                  (U.Acosh, Acosh),
                  (U.Atanh, Atanh)] =
      case es of
        [e] -> do e' <- checkType_ SReal e
                  return . TypedAST SReal $
                         syn (PrimOp_ y :$ e' :* End)
        _   -> argumentNumberError

  inferPrimOp U.Floor es =
      case es of
        [e] -> do e' <- checkType_ SProb e
                  return . TypedAST SNat $ syn (PrimOp_ Floor :$ e' :* End)
        _   -> argumentNumberError

  inferPrimOp x _ = error ("TODO: inferPrimOp: " ++ show x)


  inferArrayOp :: U.ArrayOp
               -> [U.AST]
               -> TypeCheckMonad (TypedAST abt)
  inferArrayOp U.Index_ es =
      case es of
        [e1, e2] -> do TypedAST typ1 e1' <- inferType_ e1
                       unifyArray typ1 Nothing $ \typ2 -> do
                        e2' <- checkType_ SNat e2
                        return . TypedAST typ2 $
                               syn (ArrayOp_ (Index typ2) :$ e1' :* e2' :* End)
        _        -> argumentNumberError

  inferArrayOp U.Size es =
      case es of
        [e] -> do TypedAST typ e' <- inferType_ e
                  unifyArray typ Nothing $ \typ1 ->
                   return . TypedAST SNat $
                          syn (ArrayOp_ (Size typ1) :$ e' :* End)
        _   -> argumentNumberError

  inferArrayOp U.Reduce es =
      case es of
        [e1, e2, e3] -> do
           TypedAST typ e1' <- inferType_ e1
           unifyFun typ Nothing $ \typ1 typ2 -> do
            Refl <- jmEq1_ typ2 (SFun typ1 typ1)
            e2' <- checkType_ typ1 e2
            e3' <- checkType_ (SArray typ1) e3
            return . TypedAST typ1 $
                   syn (ArrayOp_ (Reduce typ1)
                        :$ e1' :* e2' :* e3' :* End)
        _            -> argumentNumberError

  inferReducer :: U.Reducer xs U.U_ABT 'U.U
               -> List1 Variable xs1
               -> TypeCheckMonad (TypedReducer abt xs1)

  inferReducer (U.R_Fanout_ r1 r2) xs = do
      TypedReducer t1 _ r1' <- inferReducer r1 xs
      TypedReducer t2 _ r2' <- inferReducer r2 xs
      return (TypedReducer (sPair t1 t2) xs (Red_Fanout r1' r2'))

  inferReducer (U.R_Index_ x n ix r1) xs = do
      let (_, n') = caseBinds n
      let b = makeVar x SNat
      TypedReducer t1 _ r1' <- inferReducer r1 (Cons1 b xs)
      n'' <- checkBinders xs SNat n'
      caseBind ix $ \i ix1 ->
          let i' = makeVar i SNat
              (_, ix2) = caseBinds ix1 in do
          ix3 <- pushCtx i' (checkBinders xs SNat ix2)
          return . TypedReducer (SArray t1) xs $
                 Red_Index n'' (bind i' ix3) r1'

  inferReducer (U.R_Split_ b r1 r2) xs = do
      TypedReducer t1 _ r1' <- inferReducer r1 xs
      TypedReducer t2 _ r2' <- inferReducer r2 xs
      caseBind b $ \x b1 ->
       let (_, b2) = caseBinds b1
           x'  = makeVar x SNat in do
           b3 <- pushCtx x' (checkBinders xs sBool b2)
           return . TypedReducer (sPair t1 t2) xs $
                  (Red_Split (bind x' b3) r1' r2')

  inferReducer U.R_Nop_ xs = return (TypedReducer sUnit xs Red_Nop)

  inferReducer (U.R_Add_ e) xs =
      caseBind e $ \x e1 ->
      let (_, e2) = caseBinds e1
          x'  = makeVar x SNat in
          pushCtx x' $
            inferBinders xs e2 $ \typ e3 -> do
              h <- getHSemiring typ
              return $ TypedReducer typ xs (Red_Add h (bind x' e3))

-- TODO: can we make this lazier in the second component of 'TypedASTs'
-- so that we can perform case analysis on the type component before
-- actually evaluating 'checkOthers'? Problem is, even though we
-- have the type to return we don't know whether the whole thing
-- will succeed or not until after calling 'checkOthers'... We could
-- handle this by changing the return type to @TypeCheckMonad (exists
-- b. (Sing b, TypeCheckMonad [abt '[] b]))@ thereby making the
-- staging explicit.
--
-- | Given a list of terms which must all have the same type, try
-- inferring each term in order until one of them succeeds and then
-- check all the others against that type. This is appropriate for
-- 'StrictMode' where we won't need to insert coercions; for
-- 'LaxMode', see 'inferLubType' instead.
inferOneCheckOthers
    :: forall abt
    .  (ABT Term abt)
    => [U.AST]
    -> TypeCheckMonad (TypedASTs abt)
inferOneCheckOthers = inferOne []
    where
    inferOne :: [U.AST] -> [U.AST] -> TypeCheckMonad (TypedASTs abt)
    inferOne ls []
        | null ls   = ambiguousEmptyNary Nothing
        | otherwise = ambiguousMustCheckNary Nothing
    inferOne ls (e:rs) = do
        m <- try $ inferType e
        case m of
            Nothing                -> inferOne (e:ls) rs
            Just (TypedAST typ e') -> do
                ls' <- checkOthers typ ls
                rs' <- checkOthers typ rs
                return (TypedASTs typ (reverse ls' ++ e' : rs'))

    checkOthers
        :: forall a. Sing a -> [U.AST] -> TypeCheckMonad [abt '[] a]
    checkOthers typ = T.traverse (checkType typ)

-- | Given a list of terms which must all have the same type, infer
-- all the terms in order and coerce them to the lub of all their
-- types. This is appropriate for 'LaxMode' where we need to insert
-- coercions; for 'StrictMode', see 'inferOneCheckOthers' instead.
inferLubType
    :: forall abt
    .  (ABT Term abt)
    => Maybe U.SourceSpan
    -> [U.AST]
    -> TypeCheckMonad (TypedASTs abt)
inferLubType s = start
    where
    start :: [U.AST] -> TypeCheckMonad (TypedASTs abt)
    start []     = ambiguousEmptyNary Nothing
    start (u:us) = do
        TypedAST  typ1 e1 <- inferType u
        TypedASTs typ2 es <- F.foldlM step (TypedASTs typ1 [e1]) us
        return (TypedASTs typ2 (reverse es))

    -- TODO: inline 'F.foldlM' and then inline this, to unpack the first argument.
    step :: TypedASTs abt -> U.AST -> TypeCheckMonad (TypedASTs abt)
    step (TypedASTs typ1 es) u = do
        TypedAST typ2 e2 <- inferType u
        case findLub typ1 typ2 of
            Nothing              -> missingLub typ1 typ2 s
            Just (Lub typ c1 c2) ->
                let es' = map (unLC_ . coerceTo c1 . LC_) es
                    e2' = unLC_ . coerceTo c2 $ LC_ e2
                in return (TypedASTs typ (e2' : es'))


inferCaseStrict
    :: forall abt a
    .  (ABT Term abt)
    => Sing a
    -> abt '[] a
    -> [U.Branch]
    -> TypeCheckMonad (TypedAST abt)
inferCaseStrict typA e1 = inferOne []
    where
    inferOne :: [U.Branch] -> [U.Branch] -> TypeCheckMonad (TypedAST abt)
    inferOne ls []
        | null ls   = ambiguousEmptyNary Nothing
        | otherwise = ambiguousMustCheckNary Nothing
    inferOne ls (b@(U.Branch_ pat e):rs) = do
        SP pat' vars <- checkPattern typA pat
        m <- try $ inferBinders vars e $ \typ e' -> do
                    ls' <- checkOthers typ ls
                    rs' <- checkOthers typ rs
                    return (TypedAST typ $ syn (Case_ e1 (reverse ls' ++ (Branch pat' e') : rs')))
        case m of
            Nothing -> inferOne (b:ls) rs
            Just m' -> return m'

    checkOthers
        :: forall b. Sing b -> [U.Branch] -> TypeCheckMonad [Branch a abt b]
    checkOthers typ = T.traverse (checkBranch typA typ)

inferCaseLax
    :: forall abt a
    .  (ABT Term abt)
    => Maybe U.SourceSpan
    -> Sing a
    -> abt '[] a
    -> [U.Branch]
    -> TypeCheckMonad (TypedAST abt)
inferCaseLax s typA e1 = start
    where
    start :: [U.Branch] -> TypeCheckMonad (TypedAST abt)
    start []     = ambiguousEmptyNary Nothing
    start ((U.Branch_ pat e):us) = do
        SP pat' vars <- checkPattern typA pat
        inferBinders vars e $ \typ1 e' -> do
            SomeBranch typ2 bs <- F.foldlM step (SomeBranch typ1 [Branch pat' e']) us
            return . TypedAST typ2 . syn . Case_ e1 $ reverse bs

    -- TODO: inline 'F.foldlM' and then inline this, to unpack the first argument.
    step :: SomeBranch a abt
        -> U.Branch
        -> TypeCheckMonad (SomeBranch a abt)
    step (SomeBranch typB bs) (U.Branch_ pat e) = do
        SP pat' vars <- checkPattern typA pat
        inferBinders vars e $ \typE e' ->
            case findLub typB typE of
            Nothing                     -> missingLub typB typE s
            Just (Lub typLub coeB coeE) ->
                return $ SomeBranch typLub
                    ( Branch pat' (coerceTo_nonLC coeE e')
                    : map (coerceTo coeB) bs
                    )

----------------------------------------------------------------
----------------------------------------------------------------

-- HACK: we must add the constraints that 'LCs' and 'UnLCs' are inverses.
-- TODO: how can we do that in general rather than needing to repeat
-- it here and in the various constructors of 'SCon'?
checkSArgs
    :: (ABT Term abt, typs ~ UnLCs args, args ~ LCs typs)
    => List1 Sing typs
    -> [U.AST]
    -> TypeCheckMonad (SArgs abt args)
checkSArgs Nil1             []     = return End
checkSArgs (Cons1 typ typs) (e:es) =
    (:*) <$> checkType typ e <*> checkSArgs typs es
checkSArgs _ _ =
    error "checkSArgs: the number of types and terms doesn't match up"


-- | Given a typing environment, a type, and a term, verify that
-- the term satisfies the type (and produce an elaborated term):
--
-- > Γ ⊢ τ ∋ e ⇒ e'
checkType
    :: forall abt a
    .  (ABT Term abt)
    => Sing a
    -> U.AST
    -> TypeCheckMonad (abt '[] a)
checkType = checkType_
    where
    -- HACK: to convince GHC to stop being stupid about resolving
    -- the \"choice\" of @abt'@. I'm not sure why we don't need to
    -- use this same hack when 'inferType' calls 'checkType', but whatevs.
    inferType_ :: U.AST -> TypeCheckMonad (TypedAST abt)
    inferType_ = inferType

    checkVariable
        :: forall b
        .  Sing b
        -> Maybe U.SourceSpan
        -> Variable 'U.U
        -> TypeCheckMonad (abt '[] b)
    checkVariable typ0 sourceSpan x = do
      TypedAST typ' e0' <- inferType_ (var x)
      mode <- getMode
      case mode of
        StrictMode ->
            case jmEq1 typ0 typ' of
              Just Refl -> return e0'
              Nothing   -> typeMismatch sourceSpan (Right typ0) (Right typ')
        LaxMode    -> checkOrCoerce       sourceSpan e0' typ' typ0
        UnsafeMode -> checkOrUnsafeCoerce sourceSpan e0' typ' typ0


    checkType_
        :: forall b. Sing b -> U.AST -> TypeCheckMonad (abt '[] b)
    checkType_ typ0 e0 =
      let s = getMetadata e0 in
      caseVarSyn e0 (checkVariable typ0 s) (go s)
      where
      go sourceSpan t =
        case t of
        -- Change of direction rule suggests this doesn't need to be here
        -- We keep it here in case, we later use a U.Lam which doesn't
        -- carry the type of its variable 
        U.Lam_ (U.SSing typ) e1 ->
          unifyFun typ0 sourceSpan $ \typ1 typ2 ->
          matchTypes typ1 typ sourceSpan () () $
            do e1' <- checkBinder typ1 typ2 e1
               return $ syn (Lam_ :$ e1' :* End)

        U.Let_ e1 e2 -> do
            TypedAST typ1 e1' <- inferType_ e1
            e2' <- checkBinder typ1 typ0 e2
            return $ syn (Let_ :$ e1' :* e2' :* End)

        U.CoerceTo_ (Some2 c) e1 ->
            case singCoerceDomCod c of
            Nothing -> do
                e1' <- checkType_ typ0 e1
                return $ syn (CoerceTo_ CNil :$  e1' :* End)
            Just (dom, cod) ->
                matchTypes typ0 cod sourceSpan () () $ do
                 e1' <- checkType_ dom e1
                 return $ syn (CoerceTo_ c :$ e1' :* End)

        U.UnsafeTo_ (Some2 c) e1 ->
            case singCoerceDomCod c of
            Nothing -> do
                e1' <- checkType_ typ0 e1
                return $ syn (UnsafeFrom_ CNil :$  e1' :* End)
            Just (dom, cod) ->
                matchTypes typ0 dom sourceSpan () () $ do
                 e1' <- checkType_ cod e1
                 return $ syn (UnsafeFrom_ c :$ e1' :* End)

        -- TODO: Find better place to put this logic
        U.PrimOp_ U.Infinity [] -> do
            case typ0 of
              SNat  -> return $
                         syn (PrimOp_ (Infinity HIntegrable_Nat) :$ End)
              SInt  -> checkOrCoerce sourceSpan (syn (PrimOp_ (Infinity HIntegrable_Nat) :$ End))
                         SNat
                         SInt
              SProb -> return $
                         syn (PrimOp_ (Infinity HIntegrable_Prob) :$ End)
              SReal -> checkOrCoerce sourceSpan (syn (PrimOp_ (Infinity HIntegrable_Prob) :$ End))
                         SProb
                         SReal
              _     -> failwith =<<
                        makeErrMsg
                         "Type Mismatch:"
                         sourceSpan
                         "infinity can only be checked against nat or prob"

        U.NaryOp_ op es -> do
            mode <- getMode
            case mode of
              StrictMode -> safeNaryOp typ0
              LaxMode    -> safeNaryOp typ0
              UnsafeMode -> do
                op' <- make_NaryOp typ0 op
                (bads, goods) <-
                  fmap partitionEithers . T.forM es $
                  \e -> fmap (maybe (Left e) Right)
                             (tryWith LaxMode (checkType_ typ0 e))
                if null bads
                then return $ syn (NaryOp_ op' (S.fromList goods))
                else do TypedAST typ bad <- inferType (case bads of
                          [b] -> b
                          _   -> syn $ U.NaryOp_ op bads)
                        bad <- checkOrUnsafeCoerce sourceSpan bad typ typ0
                        return (case bad:goods of
                          [e] -> e
                          es' -> syn $ NaryOp_ op' (S.fromList es'))
            where
            safeNaryOp :: forall c. Sing c -> TypeCheckMonad (abt '[] c)
            safeNaryOp typ = do
                op'  <- make_NaryOp typ op
                es'  <- T.forM es $ checkType_ typ
                return $ syn (NaryOp_ op' (S.fromList es'))

        U.Pair_ e1 e2 ->
          unifyPair typ0 sourceSpan $ \a b -> do
           e1' <- checkType_ a e1
           e2' <- checkType_ b e2
           return $ syn (Datum_ $ dPair_ a b e1' e2')

        U.Array_ e1 e2 ->
            unifyArray typ0 sourceSpan $ \typ1 -> do
             e1' <- checkType_  SNat e1
             e2' <- checkBinder SNat typ1 e2
             return $ syn (Array_ e1' e2')

        U.ArrayLiteral_ es ->
            unifyArray typ0 sourceSpan $ \typ1 ->
            if null es then return $ syn (Empty_ typ0) else do
               es' <- T.forM es $ checkType_ typ1
               return $ syn (ArrayLiteral_ es')

        U.Datum_ (U.Datum hint d) ->
            case typ0 of
            SData _ typ2 ->
                (syn . Datum_ . Datum hint typ0)
                    <$> checkDatumCode typ0 typ2 d
            _ -> typeMismatch sourceSpan (Right typ0) (Left "HData")

        U.Case_ e1 branches -> do
            TypedAST typ1 e1' <- inferType_ e1
            branches' <- T.forM branches $ checkBranch typ1 typ0
            return $ syn (Case_ e1' branches')

        U.Dirac_ e1 ->
            unifyMeasure typ0 sourceSpan $ \typ1 -> do
             e1' <- checkType_ typ1 e1
             return $ syn (Dirac :$ e1' :* End)

        U.MBind_ e1 e2 ->
            unifyMeasure typ0 sourceSpan $ \_ -> do
             TypedAST typ1 e1' <- inferType_ e1
             unifyMeasure typ1 (getMetadata e1) $ \typ2 -> do
              e2' <- checkBinder typ2 typ0 e2
              return $ syn (MBind :$ e1' :* e2' :* End)

        U.Plate_ e1 e2 ->
            unifyMeasure typ0 sourceSpan $ \typ1 -> do
             e1' <- checkType_ SNat e1
             unifyArray typ1 sourceSpan $ \typ2 -> do
              e2' <- checkBinder SNat (SMeasure typ2) e2
              return $ syn (Plate :$ e1' :* e2' :* End)

        U.Chain_ e1 e2 e3 ->
            unifyMeasure typ0 sourceSpan $ \typ1 ->
            unifyPair typ1 sourceSpan $ \aa s ->
            unifyArray aa sourceSpan $ \a -> do
              e1' <- checkType_  SNat e1
              e2' <- checkType_  s    e2
              e3' <- checkBinder s    (SMeasure $ sPair a s) e3
              return $ syn (Chain :$ e1' :* e2' :* e3' :* End)

        U.Transform_ tr es -> checkTransform sourceSpan typ0 tr es

        U.Superpose_ pes ->
            unifyMeasure typ0 sourceSpan $ \_ ->
                fmap (syn . Superpose_) .
                    T.forM pes $ \(p,e) ->
                        (,) <$> checkType_ SProb p <*> checkType_ typ0 e

        U.Reject_ ->
            unifyMeasure typ0 sourceSpan $ \_ ->
            return $ syn (Reject_ typ0)

        U.InjTyped t ->
            let typ1 = typeOf $ triv t
            in case jmEq1 typ0 typ1 of
                 Just Refl -> return t
                 Nothing   -> typeMismatch sourceSpan (Right typ0) (Right typ1)

        _   | inferable e0 -> do
                TypedAST typ' e0' <- inferType_ e0
                mode <- getMode
                case mode of
                  StrictMode ->
                    case jmEq1 typ0 typ' of
                    Just Refl -> return e0'
                    Nothing   -> typeMismatch sourceSpan (Right typ0) (Right typ')
                  LaxMode    -> checkOrCoerce       sourceSpan e0' typ' typ0
                  UnsafeMode -> checkOrUnsafeCoerce sourceSpan e0' typ' typ0
            | otherwise -> error "checkType: missing an mustCheck branch!"

    checkTransform
        :: Maybe U.SourceSpan
        -> Sing x'
        -> Transform as x
        -> U.SArgs U.U_ABT as
        -> TypeCheckMonad (abt '[] x')
    checkTransform sourceSpan typ0
                   Expect
                   ((Nil2, e1) U.:* (Cons2 U.ToU Nil2, e2) U.:* U.End) =
      case typ0 of
      SProb -> do
          TypedAST typ1 e1' <- inferType_ e1
          unifyMeasure typ1 sourceSpan $ \typ2 -> do
           e2' <- checkBinder typ2 typ0 e2
           return $ syn (Transform_ Expect :$ e1' :* e2' :* End)
      _ -> typeMismatch sourceSpan (Right typ0) (Left "HProb")

    checkTransform sourceSpan typ0
                   Observe
                   ((Nil2, e1) U.:* (Nil2, e2) U.:* U.End) =
      unifyMeasure typ0 sourceSpan $ \typ2 -> do
          e1' <- checkType_ typ0 e1
          e2' <- checkType_ typ2 e2
          return $ syn (Transform_ Observe :$ e1' :* e2' :* End)

    checkTransform sourceSpan typ0
                   MCMC
                   ((Nil2, e1) U.:* (Nil2, e2) U.:* U.End) =
      unifyFun typ0 sourceSpan $ \typa typmb ->
      unifyMeasure typmb sourceSpan $ \typb ->
      matchTypes typa typb sourceSpan (SFun typa (SMeasure typa)) typ0 $ do
       e1' <- checkType (SFun typa (SMeasure typa)) e1
       e2' <- checkType            (SMeasure typa)  e2
       return $ syn $ Transform_ MCMC :$ e1' :* e2' :* End

    checkTransform sourceSpan typ0
                   (Disint k)
                   ((Nil2, e1) U.:* U.End) =
      unifyFun typ0 sourceSpan $ \typa typmb ->
      unifyMeasure typmb sourceSpan $ \typb -> do
       e1' <- checkType (SMeasure (sPair typa typb)) e1
       return $ syn $ Transform_ (Disint k) :$ e1' :* End

    checkTransform sourceSpan typ0
                   Simplify
                   ((Nil2, e1) U.:* U.End) = do
      e1' <- checkType_ typ0 e1
      return $ syn (Transform_ Simplify :$ e1' :* End)

    checkTransform sourceSpan typ0
                   Reparam
                   ((Nil2, e1) U.:* U.End) = do
      e1' <- checkType_ typ0 e1
      return $ syn (Transform_ Reparam :$ e1' :* End)

    checkTransform sourceSpan typ0
                   Summarize
                   ((Nil2, e1) U.:* U.End) = do
      e1' <- checkType_ typ0 e1
      return $ syn (Transform_ Summarize :$ e1' :* End)

    checkTransform _ _ tr _ = error $ "checkTransform{" ++ show tr ++ "}: TODO"

    --------------------------------------------------------
    -- We make these local to 'checkType' for the same reason we have 'checkType_'
    -- TODO: can we combine these in with the 'checkBranch' functions somehow?
    checkDatumCode
        :: forall xss t
        .  Sing (HData' t)
        -> Sing xss
        -> U.DCode_
        -> TypeCheckMonad (DatumCode xss (abt '[]) (HData' t))
    checkDatumCode typA typ d =
        case d of
        U.Inr d2 ->
            case typ of
            SPlus _ typ2 -> Inr <$> checkDatumCode typA typ2 d2
            _            -> failwith_ "expected datum of `inr' type"
        U.Inl d1 ->
            case typ of
            SPlus typ1 _ -> Inl <$> checkDatumStruct typA typ1 d1
            _            -> failwith_ "expected datum of `inl' type"

    checkDatumStruct
        :: forall xs t
        .  Sing (HData' t)
        -> Sing xs
        -> U.DStruct_
        -> TypeCheckMonad (DatumStruct xs (abt '[]) (HData' t))
    checkDatumStruct typA typ d =
        case d of
        U.Et d1 d2 ->
            case typ of
            SEt typ1 typ2 -> Et
                <$> checkDatumFun    typA typ1 d1
                <*> checkDatumStruct typA typ2 d2
            _     -> failwith_ "expected datum of `et' type"
        U.Done ->
            case typ of
            SDone -> return Done
            _     -> failwith_ "expected datum of `done' type"

    checkDatumFun
        :: forall x t
        .  Sing (HData' t)
        -> Sing x
        -> U.DFun_
        -> TypeCheckMonad (DatumFun x (abt '[]) (HData' t))
    checkDatumFun typA typ d =
        case d of
        U.Ident e1 ->
            case typ of
            SIdent      -> Ident <$> checkType_ typA e1
            _           -> failwith_ "expected datum of `I' type"
        U.Konst e1 ->
            case typ of
            SKonst typ1 -> Konst <$> checkType_ typ1 e1
            _           -> failwith_ "expected datum of `K' type"

checkBranch
    :: (ABT Term abt)
    => Sing a
    -> Sing b
    -> U.Branch
    -> TypeCheckMonad (Branch a abt b)
checkBranch patTyp bodyTyp (U.Branch_ pat body) = do
    SP pat' vars <- checkPattern patTyp pat
    Branch pat' <$> checkBinders vars bodyTyp body

checkPattern
    :: Sing a
    -> U.Pattern
    -> TypeCheckMonad (SomePattern a)
checkPattern = \typA pat ->
    case pat of
    U.PVar x -> return $ SP PVar (Cons1 (makeVar (U.nameToVar x) typA) Nil1)
    U.PWild  -> return $ SP PWild Nil1
    U.PDatum hint pat1 ->
        case typA of
        SData _ typ1 -> do
            SPC pat1' xs <- checkPatternCode typA typ1 pat1
            return $ SP (PDatum hint pat1') xs
        _ -> typeMismatch Nothing (Right typA) (Left "HData")
    where
    checkPatternCode
        :: Sing (HData' t)
        -> Sing xss
        -> U.PCode
        -> TypeCheckMonad (SomePatternCode xss t)
    checkPatternCode typA typ pat =
        case pat of
        U.PInr pat2 ->
            case typ of
            SPlus _ typ2 -> do
                SPC pat2' xs <- checkPatternCode typA typ2 pat2
                return $ SPC (PInr pat2') xs
            _            -> failwith_ "expected pattern of `sum' type"
        U.PInl pat1 ->
            case typ of
            SPlus typ1 _ -> do
                SPS pat1' xs <- checkPatternStruct typA typ1 pat1
                return $ SPC (PInl pat1') xs
            _ -> failwith_ "expected pattern of `zero' type"

    checkPatternStruct
        :: Sing (HData' t)
        -> Sing xs
        -> U.PStruct
        -> TypeCheckMonad (SomePatternStruct xs t)
    checkPatternStruct  typA typ pat =
        case pat of
        U.PEt pat1 pat2 ->
            case typ of
            SEt typ1 typ2 -> do
                SPF pat1' xs <- checkPatternFun    typA typ1 pat1
                SPS pat2' ys <- checkPatternStruct typA typ2 pat2
                return $ SPS (PEt pat1' pat2') (append1 xs ys)
            _ -> failwith_ "expected pattern of `et' type"
        U.PDone ->
            case typ of
            SDone -> return $ SPS PDone Nil1
            _     -> failwith_ "expected pattern of `done' type"

    checkPatternFun
        :: Sing (HData' t)
        -> Sing x
        -> U.PFun
        -> TypeCheckMonad (SomePatternFun x t)
    checkPatternFun typA typ pat =
        case pat of
        U.PIdent pat1 ->
            case typ of
            SIdent -> do
                SP pat1' xs <- checkPattern typA pat1
                return $ SPF (PIdent pat1') xs
            _ -> failwith_ "expected pattern of `I' type"
        U.PKonst pat1 ->
            case typ of
            SKonst typ1 -> do
                SP pat1' xs <- checkPattern typ1 pat1
                return $ SPF (PKonst pat1') xs
            _ -> failwith_ "expected pattern of `K' type"

checkOrCoerce
    :: (ABT Term abt)
    => Maybe (U.SourceSpan)
    -> abt '[] a
    -> Sing a
    -> Sing b
    -> TypeCheckMonad (abt '[] b)
checkOrCoerce s e typA typB =
    case findCoercion typA typB of
    Just c  -> return . unLC_ . coerceTo c $ LC_ e
    Nothing -> typeMismatch s (Right typB) (Right typA)

checkOrUnsafeCoerce
    :: (ABT Term abt)
    => Maybe (U.SourceSpan)
    -> abt '[] a
    -> Sing a
    -> Sing b
    -> TypeCheckMonad (abt '[] b)
checkOrUnsafeCoerce s e typA typB =
    case findEitherCoercion typA typB of
    Just (Unsafe  c) ->
        return . unLC_ . coerceFrom c $ LC_ e
    Just (Safe    c) ->
        return . unLC_ . coerceTo c $ LC_ e
    Just (Mixed   (_, c1, c2)) ->
        return . unLC_ . coerceTo c2 . coerceFrom c1 $ LC_ e
    Nothing ->
        case (typA, typB) of
          -- mighty, mighty hack!
          (SMeasure typ1, SMeasure _) -> do
            let x = Variable (pack "") 0 U.SU
            e2' <- checkBinder typ1 typB (bind x $ syn $ U.Dirac_ (var x))
            return $ syn (MBind :$ e :* e2' :* End)
          (_ ,  _) -> typeMismatch s (Right typB) (Right typA)



----------------------------------------------------------------
----------------------------------------------------------- fin.
