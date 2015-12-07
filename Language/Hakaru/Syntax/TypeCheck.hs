{-# LANGUAGE CPP
           , ScopedTypeVariables
           , GADTs
           , DataKinds
           , PolyKinds
           , GeneralizedNewtypeDeriving
           , TypeOperators
           , FlexibleContexts
           , FlexibleInstances
           , Rank2Types
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.12.07
-- |
-- Module      :  Language.Hakaru.Syntax.TypeCheck
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Bidirectional type checking for our AST.
----------------------------------------------------------------
module Language.Hakaru.Syntax.TypeCheck
    ( inferable
    , mustCheck
    , TypeCheckError
    , TypeCheckMonad(), runTCM, unTCM
    , TypeCheckMode(..)
    , TypedAST(..)
    , inferType
    , checkType
    ) where

import           Prelude hiding (id, (.))
import           Control.Category
import           Data.Proxy            (KProxy(..))
import qualified Data.IntMap           as IM
import qualified Data.Traversable      as T
import qualified Data.Foldable         as F
import qualified Data.Sequence         as S
#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..), (<$>))
#endif
import           Control.Applicative   (Alternative(..))
import qualified Language.Hakaru.Parser.AST as U

import Language.Hakaru.Syntax.Nat      (fromNat)
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.DataKind (Hakaru(..), HData')
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.TypeHelpers
import Language.Hakaru.Syntax.Coercion
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.ABT

----------------------------------------------------------------
----------------------------------------------------------------

-- | Those terms from which we can synthesize a unique type. We are
-- also allowed to check them, via the change-of-direction rule.
inferable :: U.AST a -> Bool
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
mustCheck :: U.AST a -> Bool
mustCheck = go
    where
    go (U.Var_ _)    = False
    go (U.Lam_ _ _)  = True

    -- In general, applications don't require checking; however,
    -- for fully saturated data constructors they do (according to
    -- neelk; also see the note below).
    go (U.App_ _  _) = False

    -- We follow Dunfield & Pientka and \Pi\Sigma in inferring or
    -- checking depending on what the body requires. This is as
    -- opposed to the TLDI'05 paper, which always inders @e2@ but
    -- will check or infer the @e1@ depending on whether it has a
    -- type annotation or not.
    go (U.Let_ _ _ e2)    = mustCheck e2

    go (U.Ann_ _ _)       = False
    go (U.CoerceTo_ _ _)  = False
    go (U.UnsafeTo_ _ _)  = False

    -- In general (according to Dunfield & Pientka), we should be
    -- able to infer the result of a fully saturated primop by
    -- looking up it's type and then checking all the arguments.
    go (U.PrimOp_ _ _)    = False

    -- In strict mode: if we can infer any of the arguments, then we can check all the rest at the same type.
    -- BUG: in lax mode we must be able to infer all of them; otherwise we may not be able to take the lub of the types
    go (U.NaryOp_   _ es) = F.all mustCheck es
    go (U.Superpose_ pes) = F.all (mustCheck . snd) pes -- TODO: back this up, like we do for NaryOp

    -- I return true because most folks (neelk, Pfenning, Dunfield
    -- & Pientka) say all data constructors mustCheck (even though
    -- that doesn't seem right to me; also, cf.,
    -- <http://jozefg.bitbucket.org/posts/2014-11-22-bidir.html>).
    --
    -- TODO: For 'Array_', it seems to me that if we can infer the
    -- body, then we should be able to infer the whole thing, right?
    -- Or maybe the problem is that the change-of-direction rule
    -- might send us down the wrong path? Usually I'd assume the
    -- binder is what does it, but here we know the type of the
    -- bound variable, because it's the same for every array.
    --
    -- TODO: For 'Datum_', all atomic types should be inferable.
    -- However, because we have polymorphic sum data types (HEither,
    -- HMaybe, HList), those cannot be inferred. Also, we have
    -- polymorphic product types (HPair) which can only be inferred
    -- if all their components can be inferred.
    go (U.Literal_ _)   = False
    go U.Empty_         = True
    go (U.Array_ _ _ _) = True
    go (U.Datum_ _)     = True

    -- TODO: everyone says this, but it seems to me that if we can
    -- infer any of the branches (and check the rest to agree) then
    -- we should be able to infer the whole thing... Or maybe the
    -- problem is that the change-of-direction rule might send us
    -- down the wrong path?
    go (U.Case_ _ _)      = True

    go (U.Dirac_  e1)     = mustCheck e1
    go (U.MBind_  _ _ e2) = mustCheck e2
    go (U.MeasureOp_ _ _) = False
    go (U.Expect_ _ _ e2) = mustCheck e2


----------------------------------------------------------------
----------------------------------------------------------------

type Ctx = VarSet ('KProxy :: KProxy Hakaru)

data TypeCheckMode = StrictMode | LaxMode
    deriving (Read, Show, Eq)

type TypeCheckError = String -- TODO: something better

newtype TypeCheckMonad a =
    TCM { unTCM :: Ctx -> TypeCheckMode -> Either TypeCheckError a }

runTCM :: TypeCheckMonad a -> TypeCheckMode -> Either TypeCheckError a 
runTCM m = unTCM m emptyVarSet

instance Functor TypeCheckMonad where
    fmap f m = TCM $ \ctx mode -> fmap f (unTCM m ctx mode)

instance Applicative TypeCheckMonad where
    pure x    = TCM $ \_ _ -> Right x
    mf <*> mx = mf >>= \f -> fmap f mx

-- TODO: ensure this instance has the appropriate strictness
instance Monad TypeCheckMonad where
    return   = pure
    mx >>= k =
        TCM $ \ctx mode ->
        unTCM mx ctx mode >>= \x ->
        unTCM (k x) ctx mode

-- TODO: we might want to just inline this definition into the use of 'asum'; rather than actually having an instance...
instance Alternative TypeCheckMonad where
    empty   = failwith "Need type annotation in one of your arguments"
    x <|> y = TCM $ \ctx mode ->
        case unTCM x ctx mode of
        Left  _ -> unTCM y ctx mode
        Right e -> Right e

-- | Return the mode in which we're checking\/inferring types.
getMode :: TypeCheckMonad TypeCheckMode
getMode = TCM (const Right)

-- | Extend the typing context, but only locally.
pushCtx
    :: Variable (a :: Hakaru)
    -> TypeCheckMonad b
    -> TypeCheckMonad b
pushCtx x (TCM m) = TCM (m . insertVarSet x)

getCtx :: TypeCheckMonad Ctx
getCtx = TCM (const . Right)

failwith :: TypeCheckError -> TypeCheckMonad a
failwith e = TCM $ \_ _ -> Left e

-- | Fail with a type-mismatch error.
typeMismatch
    :: Show1 (Sing :: k -> *)
    => Either String (Sing (a :: k))
    -> Either String (Sing (b :: k))
    -> TypeCheckMonad c
typeMismatch typ1 typ2 =
    failwith $ "Type Mismatch: expected " ++ msg1 ++ ", found " ++ msg2
    where
    msg1 = case typ1 of { Left msg -> msg; Right typ -> show1 typ }
    msg2 = case typ2 of { Left msg -> msg; Right typ -> show1 typ }


----------------------------------------------------------------
----------------------------------------------------------------
-- BUG: haddock doesn't like annotations on GADT constructors. So
-- here we'll avoid using the GADT syntax, even though it'd make
-- the data type declaration prettier\/cleaner.
-- <https://github.com/hakaru-dev/hakaru/issues/6>
--
-- | The @e' ∈ τ@ portion of the inference judgement.
data TypedAST (abt :: [Hakaru] -> Hakaru -> *)
    = forall b. TypedAST !(Sing b) !(abt '[] b)

instance Show2 abt => Show (TypedAST abt) where
    showsPrec p (TypedAST typ e) =
        showParen_12 p "TypedAST" typ e


inferBinderType
    :: (ABT AST abt)
    => Variable a
    -> U.AST n
    -> (forall b. Sing b -> abt '[ a ] b -> TypeCheckMonad r)
    -> TypeCheckMonad r
inferBinderType x e k = do
    TypedAST typ e' <- pushCtx x (inferType e)
    k typ (bind x e')


checkBinderType
    :: (ABT AST abt)
    => Variable a
    -> Sing b
    -> U.AST n
    -> TypeCheckMonad (abt '[ a ] b)
checkBinderType x eTyp e =
    pushCtx x (bind x <$> checkType eTyp e)


-- | Given a typing environment and a term, synthesize the term's type:
--
-- > Γ ⊢ e ⇒ e' ∈ τ
inferType
    :: forall abt n
    .  (ABT AST abt)
    => U.AST n
    -> TypeCheckMonad (TypedAST abt)
inferType = inferType_
  where
  checkType_ :: forall b. Sing b -> U.AST n -> TypeCheckMonad (abt '[] b)
  checkType_ = checkType

  -- HACK: We need this monomorphic binding so that GHC doesn't get confused about which @(ABT AST abt)@ instance to use in recursive calls.
  inferType_ :: U.AST n -> TypeCheckMonad (TypedAST abt)
  inferType_ e0 =
    case e0 of
    U.Var_ x -> do
        ctx <- getCtx
        case IM.lookup (fromNat $ U.nameID x) (unVarSet ctx) of
            Just (SomeVariable x') ->
                return $ TypedAST (varType x') (var x')
            Nothing ->
                failwith $ "cannot infer type of free variable: " ++ show x

    U.App_ e1 e2 -> do
        TypedAST typ1 e1' <- inferType_ e1
        case typ1 of
            SFun typ2 typ3 -> do
                e2' <- checkType_ typ2 e2
                return . TypedAST typ3 $ syn (App_ :$ e1' :* e2' :* End)
            _ -> typeMismatch (Left "function type") (Right typ1)
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
        {-
    U.App_ (U.Lam_ name e1) e2 -> do
        TypedAST typ2 e2' <- inferType_ e2
        caseBind e1 $ \x -> pushCtx x typ2 . inferType_
        -}

    U.Let_ x e1 e2 -> do
        TypedAST typ1 e1' <- inferType_ e1
        inferBinderType (U.makeVar x typ1) e2 $ \typ2 e2' ->
            return . TypedAST typ2 $ syn (Let_ :$ e1' :* e2' :* End)
                    
    U.Ann_ e1 (U.SSing typ1) -> do
        -- N.B., this requires that @typ1@ is a 'Sing' not a 'Proxy',
        -- since we can't generate a 'Sing' from a 'Proxy'.
        e1' <- checkType_ typ1 e1
        return . TypedAST typ1 $ syn (Ann_ typ1 :$ e1' :* End)

    U.PrimOp_ (U.SealedOp op) es -> do
        let (typs, typ1) = sing_PrimOp op
        es' <- checkSArgs typs es
        return . TypedAST typ1 $ syn (PrimOp_ op :$ es')
    {- -- TODO:
    U.ArrayOp_ (U.SealedOp op) es -> do
        let (typs, typ1) = sing_ArrayOp op
        es' <- checkSArgs typs es
        return . TypedAST typ1 $ syn (ArrayOp_ op :$ es')
    -}

    U.NaryOp_ op es -> do
        -- TODO: abstract out this infer-one-check-all pattern so we can reuse it elsewhere. Also, make it zipper-like so we don't re-check the one we inferred.
        TypedAST typ1 _ <- F.asum $ fmap inferType_ es
        case make_NaryOp typ1 op of
            Nothing  -> failwith "expected type with semiring"
            Just op' -> do
                es'' <- T.forM es $ checkType_ typ1
                return . TypedAST typ1 $ syn (NaryOp_ op' $ S.fromList es'')

    U.Literal_ (Some1 v) ->
        -- BUG: need to finish implementing sing_Literal for Datum
        return . TypedAST (sing_Literal v) $ syn (Literal_ v)

    U.CoerceTo_ (Some2 c) e1 ->
        case singCoerceDomCod c of
        Nothing
            | inferable e1 -> inferType_ e1
            | otherwise    -> 
                failwith "Cannot infer type for null-coercion over a checking term; please add a type annotation"  
        Just (dom,cod) -> do
            e1' <- checkType_ dom e1
            return . TypedAST cod $ syn (CoerceTo_ c :$ e1' :* End)

    U.UnsafeTo_ (Some2 c) e1 ->
        case singCoerceDomCod c of
        Nothing
            | inferable e1 -> inferType_ e1
            | otherwise    -> 
                failwith "Cannot infer type for null-coercion over a checking term; please add a type annotation"  
        Just (dom,cod) -> do
            e1' <- checkType_ cod e1
            return . TypedAST dom $ syn (UnsafeFrom_ c :$ e1' :* End)

    U.MeasureOp_ (U.SealedOp op) es -> do
        let (typs, typ1) = sing_MeasureOp op
        es' <- checkSArgs typs es
        return . TypedAST (SMeasure typ1) $ syn (MeasureOp_ op :$ es')

    U.Dirac_ e1 | inferable e1 -> do
        TypedAST typ1 e1' <- inferType_ e1
        return . TypedAST (SMeasure typ1) $ syn (Dirac :$ e1' :* End)

    U.MBind_ x e1 e2 -> do
        TypedAST typ1 e1' <- inferType_ e1
        case typ1 of
            SMeasure typ2 ->
                let x' = U.makeVar x typ2 in
                pushCtx x' $ do
                    TypedAST typ3 e2' <- inferType_ e2
                    case typ3 of
                        SMeasure _ ->
                            return . TypedAST typ3 $
                                syn (MBind :$ e1' :* bind x' e2' :* End)
                        _ -> typeMismatch (Left "HMeasure") (Right typ3)
                {-
                -- BUG: the \"ambiguous\" @abt@ issue again...
                inferBinderType (U.makeVar x typ2) e2 $ \typ3 e2' ->
                    case typ3 of
                    SMeasure _ -> return . TypedAST typ3 $
                        syn (MBind :$ e1' :* e2' :* End)
                    _ -> typeMismatch (Left "HMeasure") (Right typ3)
                -}
            _ -> typeMismatch (Left "HMeasure") (Right typ1)

    U.Expect_ x e1 e2 -> do
        TypedAST typ1 e1' <- inferType_ e1
        case typ1 of
            SMeasure typ2 -> do
                e2' <- checkBinderType (U.makeVar x typ2) SProb e2
                return . TypedAST SProb $ syn (Expect :$ e1' :* e2' :* End)
            _ -> typeMismatch (Left "HMeasure") (Right typ1)

    U.Superpose_ pes -> do
      TypedAST typ1 _ <- F.asum $ fmap inferType_ (map snd pes)
      pes' <- checkType_ typ1 (U.Superpose_ pes)
      return $ TypedAST typ1 pes'

    _   | mustCheck e0 -> failwith "Cannot infer types for checking terms; please add a type annotation"
        | otherwise    -> error "inferType: missing an inferable branch!"


----------------------------------------------------------------
----------------------------------------------------------------

-- HACK: we must add the constraints that 'LCs' and 'UnLCs' are inverses.
-- TODO: how can we do that in general rather than needing to repeat it here and in the various constructors of 'SCon'?
checkSArgs
    :: (ABT AST abt, typs ~ UnLCs args, args ~ LCs typs)
    => List1 Sing typs
    -> [U.AST c]
    -> TypeCheckMonad (SArgs abt args)
checkSArgs Nil1             []     = return End
checkSArgs (Cons1 typ typs) (e:es) =
    (:*) <$> checkType typ e <*> checkSArgs typs es
checkSArgs _ _ =
    error "checkSArgs: the number of types and terms doesn't match up"


-- | Given a typing environment, a term, and a type, check that the
-- term satisfies the type:
--
-- > Γ ⊢ τ ∋ e ⇒ e'
checkType
    :: forall abt a c
    .  (ABT AST abt)
    => Sing a
    -> U.AST c
    -> TypeCheckMonad (abt '[] a)
checkType = checkType_
    where
    -- HACK: to convince GHC to stop being stupid about resolving
    -- the \"choice\" of @abt'@. I'm not sure why we don't need to
    -- use this same hack when 'inferType' calls 'checkType', but whatevs.
    inferType_ :: U.AST c -> TypeCheckMonad (TypedAST abt)
    inferType_ = inferType

    checkType_
        :: forall b. Sing b -> U.AST c -> TypeCheckMonad (abt '[] b)
    checkType_ typ0 e0 =
        case e0 of
        U.Lam_ x e1 ->
            case typ0 of
            SFun typ1 typ2 -> do
                e1' <- checkBinderType (U.makeVar x typ1) typ2 e1
                return $ syn (Lam_ :$ e1' :* End)
            _ -> typeMismatch (Right typ0) (Left "function type")

        U.Let_ x e1 e2 -> do
            TypedAST typ1 e1' <- inferType_ e1
            e2' <- checkBinderType (U.makeVar x typ1) typ0 e2
            return $ syn (Let_ :$ e1' :* e2' :* End)

        U.CoerceTo_ (Some2 c) e1 ->
            case singCoerceDomCod c of
            Nothing -> do
                e1' <- checkType_ typ0 e1
                return $ syn (CoerceTo_ CNil :$  e1' :* End)
            Just (dom, cod) -> 
                case jmEq1 typ0 cod of
                Just Refl -> do
                    e1' <- checkType_ dom e1
                    return $ syn (CoerceTo_ c :$ e1' :* End)
                Nothing -> typeMismatch (Right typ0) (Right cod)

        U.UnsafeTo_ (Some2 c) e1 ->
            case singCoerceDomCod c of
            Nothing -> do
                e1' <- checkType_ typ0 e1
                return $ syn (UnsafeFrom_ CNil :$  e1' :* End)
            Just (dom, cod) -> 
                case jmEq1 typ0 dom of
                Just Refl -> do
                    e1' <- checkType_ cod e1
                    return $ syn (UnsafeFrom_ c :$ e1' :* End)
                Nothing -> typeMismatch (Right typ0) (Right dom)

        U.NaryOp_ op es ->
            case make_NaryOp typ0 op of
            Nothing  -> failwith "expected type with semiring"
            Just op' -> do
                es' <- T.forM es $ checkType_ typ0
                return $ syn (NaryOp_ op' (S.fromList es'))

        U.Empty_ ->
            case typ0 of
            SArray _ -> return $ syn (Empty_ typ0)
            _        -> typeMismatch (Right typ0) (Left "HArray")
    
        -- Not sure Array should be a binding form
        U.Array_ e1 x e2 ->
            case typ0 of
            SArray typ1 -> do
                e1' <- checkType_ SNat e1
                e2' <- checkBinderType (U.makeVar x SNat) typ1 e2
                return $ syn (Array_ e1' e2')
            _ -> typeMismatch (Right typ0) (Left "HArray")

        U.Datum_ (U.Datum hint d) ->
            case typ0 of
            SData _ typ2 ->
                (syn . Datum_ . Datum hint)
                    <$> checkDatumCode typ0 typ2 d
            _ -> typeMismatch (Right typ0) (Left "HData")
    
        U.Case_ e1 branches -> do
            TypedAST typ1 e1' <- inferType_ e1
            branches' <- T.forM branches $ checkBranch typ1 typ0
            return $ syn (Case_ e1' branches')

        U.Dirac_ e1 ->
            case typ0 of
            SMeasure typ1 -> do
                e1' <- checkType_ typ1 e1
                return $ syn (Dirac :$ e1' :* End)
            _ -> typeMismatch (Right typ0) (Left "HMeasure")
    
        U.MBind_ x e1 e2 ->
            case typ0 of
            SMeasure _ -> do
                TypedAST typ1 e1' <- inferType_ e1
                case typ1 of
                    SMeasure typ2 -> do
                        e2' <- checkBinderType (U.makeVar x typ2) typ0 e2
                        return $ syn (MBind :$ e1' :* e2' :* End)
                    _ -> typeMismatch (Right typ0) (Right typ1)
            _ -> typeMismatch (Right typ0) (Left "HMeasure")
    
        U.Expect_ x e1 e2 ->
            case typ0 of
            SProb -> do
                TypedAST typ1 e1' <- inferType_ e1
                case typ1 of
                    SMeasure typ2 -> do
                        e2' <- checkBinderType (U.makeVar x typ2) typ0 e2
                        return $ syn (Expect :$ e1' :* e2' :* End)
                    _ -> typeMismatch (Left "HMeasure") (Right typ1)
            _ -> typeMismatch (Right typ0) (Left "HProb")

        U.Superpose_ pes ->
            case typ0 of
            SMeasure _ ->
                fmap (syn . Superpose_) .
                    T.forM pes $ \(p,e) ->
                        (,) <$> checkType_ SProb p <*> checkType_ typ0 e
            _ -> typeMismatch (Right typ0) (Left "HMeasure")

        _   | inferable e0 -> do
                TypedAST typ' e0' <- inferType_ e0
                mode <- getMode
                case mode of
                  StrictMode ->
                    case jmEq1 typ0 typ' of
                    Just Refl -> return e0'
                    Nothing   -> typeMismatch (Right typ0) (Right typ')
                  LaxMode ->
                    case findCoercion typ' typ0 of
                    Just CNil -> return e0'
                    Just c    -> checkType_ typ0 $ U.CoerceTo_ (Some2 c) e0
                    Nothing   -> typeMismatch (Right typ0) (Right typ')
            | otherwise -> error "checkType: missing an mustCheck branch!"

    --------------------------------------------------------
    -- We make these local to 'checkType' for the same reason we have 'checkType_'
    -- TODO: can we combine these in with the 'checkBranch' functions somehow?
    checkDatumCode
        :: forall xss t
        .  Sing (HData' t)
        -> Sing xss
        -> U.DCode c
        -> TypeCheckMonad (DatumCode xss (abt '[]) (HData' t))
    checkDatumCode typA typ d =
        case d of
        U.Inr d2 ->
            case typ of
            SPlus _ typ2 -> Inr <$> checkDatumCode typA typ2 d2
            _            -> failwith "expected term of `inr' type"
        U.Inl d1 ->
            case typ of
            SPlus typ1 _ -> Inl <$> checkDatumStruct typA typ1 d1
            _            -> failwith "expected term of `inl' type"
    
    checkDatumStruct
        :: forall xs t
        .  Sing (HData' t)
        -> Sing xs
        -> U.DStruct c
        -> TypeCheckMonad (DatumStruct xs (abt '[]) (HData' t))
    checkDatumStruct typA typ d =
        case d of
        U.Et d1 d2 ->
            case typ of
            SEt typ1 typ2 -> Et
                <$> checkDatumFun    typA typ1 d1
                <*> checkDatumStruct typA typ2 d2
            _     -> failwith "expected term of `et' type"
        U.Done ->
            case typ of
            SDone -> return Done
            _     -> failwith "expected term of `done' type"
    
    checkDatumFun
        :: forall x t
        .  Sing (HData' t)
        -> Sing x
        -> U.DFun c
        -> TypeCheckMonad (DatumFun x (abt '[]) (HData' t))
    checkDatumFun typA typ d =
        case d of
        U.Ident e1 ->
            case typ of
            SIdent      -> Ident <$> checkType_ typA e1
            _           -> failwith "expected term of `I' type"
        U.Konst e1 ->
            case typ of
            SKonst typ1 -> Konst <$> checkType_ typ1 e1
            _           -> failwith "expected term of `K' type"


----------------------------------------------------------------
-- BUG: haddock doesn't like annotations on GADT constructors. So
-- here we'll avoid using the GADT syntax, even though it'd make
-- the data type declaration prettier\/cleaner.
-- <https://github.com/hakaru-dev/hakaru/issues/6>
data SomePattern (a :: Hakaru) =
    forall vars.
        SP  !(Pattern vars a)
            !(List1 Variable vars)

data SomePatternCode xss t =
    forall vars.
        SPC !(PDatumCode xss vars (HData' t))
            !(List1 Variable vars)

data SomePatternStruct xs t =
    forall vars.
        SPS !(PDatumStruct xs vars (HData' t))
            !(List1 Variable vars)

data SomePatternFun x t =
    forall vars.
        SPF !(PDatumFun x vars (HData' t))
            !(List1 Variable vars)

checkBranch
    :: (ABT AST abt)
    => Sing a
    -> Sing b
    -> U.Branch c
    -> TypeCheckMonad (Branch a abt b)
checkBranch =
    \patTyp bodyTyp (U.Branch pat body) -> do
        SP pat' vars <- checkPattern patTyp pat
        Branch pat' <$> checkBranchBody bodyTyp body vars
    where
    checkBranchBody
        :: (ABT AST abt)
        => Sing b
        -> U.AST c
        -> List1 Variable xs
        -> TypeCheckMonad (abt xs b)
    checkBranchBody bodyTyp body xs =
        case xs of
        Nil1        -> checkType bodyTyp body
        Cons1 x xs' ->
            pushCtx x $
                bind x <$> checkBranchBody bodyTyp body xs'

    checkPattern
        :: Sing a
        -> U.Pattern
        -> TypeCheckMonad (SomePattern a)
    checkPattern typA pat =
        case pat of
        U.PVar x -> return $ SP PVar (Cons1 (U.makeVar x typA) Nil1)
        U.PWild  -> return $ SP PWild Nil1
        U.PDatum hint pat1 ->
            case typA of
            SData _ typ1 -> do
                SPC pat1' xs <- checkPatternCode typA typ1 pat1
                return $ SP (PDatum hint pat1') xs
            _ -> typeMismatch (Right typA) (Left "HData")

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
            _            -> failwith "expected term of `sum' type"
        U.PInl pat1 ->
            case typ of
            SPlus typ1 _ -> do
                SPS pat1' xs <- checkPatternStruct typA typ1 pat1
                return $ SPC (PInl pat1') xs
            _ -> failwith "expected term of `zero' type"

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
            _ -> failwith "expected term of `et' type"
        U.PDone ->
            case typ of
            SDone -> return $ SPS PDone Nil1
            _     -> failwith "expected term of `done' type"

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
            _ -> failwith "expected term of `I' type"
        U.PKonst pat1 ->
            case typ of
            SKonst typ1 -> do
                SP pat1' xs <- checkPattern typ1 pat1
                return $ SPF (PKonst pat1') xs
            _ -> failwith "expected term of `K' type"


findCoercion :: Sing a -> Sing b -> Maybe (Coercion a b)
findCoercion SNat  SInt  = Just signed
findCoercion SProb SReal = Just signed
findCoercion SNat  SProb = Just continuous
findCoercion SInt  SReal = Just continuous
findCoercion SNat  SReal = Just (continuous . signed)
findCoercion a     b     = jmEq1 a b >>= \Refl -> Just CNil

----------------------------------------------------------------
----------------------------------------------------------- fin.
