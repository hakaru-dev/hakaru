{-# LANGUAGE CPP
           , ScopedTypeVariables
           , GADTs
           , DataKinds
           , PolyKinds
           , GeneralizedNewtypeDeriving
           , TypeOperators
           , FlexibleContexts
           , FlexibleInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.11.07
-- |
-- Module      :  Language.Hakaru.Syntax.TypeCheck
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Bidirectional type checking for our AST. N.B., since we use a
-- GADT, most of the usual type inference\/checking is trivial; the
-- only thing we actually need to do is ensure well-formedness of
-- the 'ABT' structure and the well-typedness of binders\/variables.
--
-- TODO: we should be able to get rid of the ABT well-formedness
-- checking by having our 'View' type be indexed by the number of
-- bindings it introduces.
----------------------------------------------------------------
module Language.Hakaru.Syntax.TypeCheck
    ( inferable
    , mustCheck
    , TypeCheckError
    , TypeCheckMonad(), runTCM
    , TypedAST(..)
    , inferType
    , checkType
    ) where

import           Data.Proxy            (KProxy(..))
import           Data.IntMap           (IntMap)
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
import Language.Hakaru.Syntax.HClasses
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.DataKind (Hakaru(..), HData')
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.TypeHelpers
import Language.Hakaru.Syntax.Coercion (Coercion(..),
                                        PrimCoercion(..),
                                        singCoerceDomCod)
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
mustCheck :: U.AST a -> Bool
mustCheck = go
    where
    go (U.Var_ _)    = False
    go (U.Lam_ _ _)  = True
    go (U.Fix_ _ _)  = True
 
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

    go (U.NaryOp_ _ es)   = F.all mustCheck es

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
    go (U.Value_ _)     = False -- BUG: should be true for VDatum...
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
    go (U.Superpose_ pes) = F.all (mustCheck . snd) pes -- TODO: back this up, like we do for NaryOp
    go (U.Lub_ es)        = error "TODO: mustCheck{Lub_}" -- TODO: inferrable iff at least one component is inferrable?


----------------------------------------------------------------
----------------------------------------------------------------

type Ctx = IntMap (SomeVariable ('KProxy :: KProxy Hakaru))

type TypeCheckError = String -- TODO: something better

newtype TypeCheckMonad a =
    TCM { unTCM :: Ctx -> Either TypeCheckError a }

runTCM :: TypeCheckMonad a -> Either TypeCheckError a 
runTCM m = unTCM m IM.empty

instance Functor TypeCheckMonad where
    fmap f m = TCM $ fmap f . unTCM m

instance Applicative TypeCheckMonad where
    pure      = TCM . const . Right
    mf <*> mx = mf >>= \f -> fmap f mx

-- TODO: ensure this instance has the appropriate strictness
instance Monad TypeCheckMonad where
    return   = pure
    mx >>= k = TCM $ \ctx -> unTCM mx ctx >>= \x -> unTCM (k x) ctx

instance Alternative TypeCheckMonad where
    empty   = failwith "Need type annotation in one of your arguments"
    x <|> y = TCM $ \ctx ->
        case unTCM x ctx of
        Left  _ -> unTCM y ctx
        Right e -> Right e


-- | Extend the typing context, but only locally.
pushCtx
    :: SomeVariable ('KProxy :: KProxy Hakaru)
    -> TypeCheckMonad a
    -> TypeCheckMonad a
pushCtx tv@(SomeVariable x) (TCM m) =
    TCM $ \ctx -> m $ IM.insert (fromNat $ varID x) tv ctx

getCtx :: TypeCheckMonad Ctx
getCtx = TCM Right

failwith :: TypeCheckError -> TypeCheckMonad a
failwith = TCM . const . Left

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


data TypingMode = TStrictMode | TLaxMode | TUnsafeLaxMode 

----------------------------------------------------------------
----------------------------------------------------------------
-- BUG: haddock doesn't like annotations on GADT constructors. So
-- here we'll avoid using the GADT syntax, even though it'd make
-- the data type declaration prettier\/cleaner.
-- <https://github.com/hakaru-dev/hakaru/issues/6>
data TypedAST (abt :: [Hakaru] -> Hakaru -> *)
    = forall b. TypedAST !(Sing b) !(abt '[] b)


-- | Given a typing environment and a term, synthesize the term's type.
inferType
    :: forall abt a
    .  (ABT AST abt)
    => U.AST a
    -> TypeCheckMonad (TypedAST abt)
inferType = inferType_
  where
  -- HACK: We need this monomorphic binding so that GHC doesn't get confused about which @(ABT AST abt)@ instance to use in recursive calls.
  inferType_ :: U.AST a -> TypeCheckMonad (TypedAST abt)
  inferType_ e0 =
    case e0 of
    U.Var_ x -> do
        ctx <- getCtx
        case IM.lookup (fromNat $ U.nameID x) ctx of
            Just (SomeVariable x') ->
                return $ TypedAST (varType x') (var x')
            Nothing ->
                failwith $ "cannot infer type of free variable: " ++ show x

    U.App_ e1 e2 -> do
        TypedAST typ1 e1' <- inferType_ e1
        case typ1 of
            SFun typ2 typ3 -> do
                e2' <- checkType typ2 e2
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
        caseBind e1 $ \x -> pushCtx (SomeVariable x typ2) . inferType_
        -}

    U.Let_ x e1 e2 -> do
        TypedAST typ1 e1' <- inferType_ e1
        let x' = U.makeVar x typ1
        pushCtx (SomeVariable x') $ do
            TypedAST typ2 e2' <- inferType_ e2
            return . TypedAST typ2 $ syn (Let_ :$ e1' :* bind x' e2' :* End)
                    
    U.Ann_ e1 (U.SSing typ1) -> do
        -- N.B., this requires that @typ1@ is a 'Sing' not a 'Proxy',
        -- since we can't generate a 'Sing' from a 'Proxy'.
        e1' <- checkType typ1 e1
        return . TypedAST typ1 $ syn (Ann_ typ1 :$ e1' :* End)

    U.PrimOp_ (U.SealedOp op) es -> do
        let (typs, typ1) = sing_PrimOp op
        es' <- checkSArgs typs es
        return . TypedAST typ1 $ syn (PrimOp_ op :$ es')

    U.NaryOp_ op es -> do
        TypedAST typ1 _ <- F.asum $ fmap inferType_ es
        es'' <- T.forM es $ checkType typ1
        case make_NaryOp typ1 op of
            Nothing -> failwith "expected type with semiring"
            Just op' ->
                return . TypedAST typ1 $ syn (NaryOp_ op' (S.fromList es''))

    U.Value_ (Some1 v) ->
        -- BUG: need to finish implementing sing_Value for Datum
        return . TypedAST (sing_Value v) $ syn (Value_ v)

    U.CoerceTo_ (Some2 c) e1 ->
        case singCoerceDomCod c of
        Nothing
            | inferable e1 -> inferType_ e1
            | otherwise    -> 
                failwith "Cannot infer type for null-coercion over a checking term; please add a type annotation"  
        Just (dom,cod) -> do
            e1' <- checkType dom e1
            return . TypedAST cod $ syn (CoerceTo_ c :$ e1' :* End)

    U.UnsafeTo_ (Some2 c) e1 ->
        case singCoerceDomCod c of
        Nothing
            | inferable e1 -> inferType_ e1
            | otherwise    -> 
                failwith "Cannot infer type for null-coercion over a checking term; please add a type annotation"  
        Just (dom,cod) -> do
            e1' <- checkType cod e1
            return . TypedAST dom $ syn (UnsafeFrom_ c :$ e1' :* End)

    U.MeasureOp_ (U.SealedOp op) es -> do
        let (typs, typ1) = sing_MeasureOp op
        es' <- checkSArgs typs es
        return . TypedAST (SMeasure typ1) $ syn (MeasureOp_ op :$ es')

    U.Dirac_ e1 | inferable e1 -> do
        TypedAST typ1 e1' <- inferType_ e1
        return . TypedAST (SMeasure typ1) $ syn (Dirac :$ e1' :* End)

    U.MBind_ name e1 e2 -> do
        TypedAST typ1 e1' <- inferType_ e1
        case typ1 of
            SMeasure typ2 ->
                let x = U.makeVar name typ2
                in pushCtx (SomeVariable x) $ do
                    TypedAST typ3 e2' <- inferType_ e2
                    case typ3 of
                        SMeasure _ ->
                            return . TypedAST typ3 $
                                syn (MBind :$ e1' :* bind x e2' :* End)
                        _ -> typeMismatch (Left "HMeasure") (Right typ3)
            _ -> typeMismatch (Left "HMeasure") (Right typ1)

    U.Expect_ name e1 e2 -> do
        TypedAST typ1 e1' <- inferType_ e1
        case typ1 of
            SMeasure typ2 ->
                let x = U.makeVar name typ2
                in pushCtx (SomeVariable x) $ do
                    e2' <- checkType SProb e2
                    return . TypedAST SProb $
                        syn (Expect :$ e1' :* bind x e2' :* End)
            _ -> typeMismatch (Left "HMeasure") (Right typ1)


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
-- term satisfies the type.
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
        U.Lam_ name e1 ->
            case typ0 of
            SFun typ1 typ2 ->
                let x = U.makeVar name typ1 in
                pushCtx (SomeVariable x) $ do
                    e1' <- checkType_ typ2 e1
                    return $ syn (Lam_ :$ bind x e1' :* End)
            _ -> typeMismatch (Right typ0) (Left "function type")

        U.Let_ name e1 e2 -> do
            TypedAST typ1 e1' <- inferType_ e1
            let x = U.makeVar name typ1
            pushCtx (SomeVariable x) $ do
                e2' <- checkType_ typ0 e2
                return $ syn (Let_ :$ e1' :* bind x e2' :* End)
    
        U.Fix_ name e1 ->
            let x = U.makeVar name typ0 in
            pushCtx (SomeVariable x) $ do
                e1' <- checkType_ typ0 e1
                return $ syn (Fix_ :$ bind x e1' :* End)
    
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
                es' <- T.forM es $ checkType typ0
                return $ syn (NaryOp_ op' (S.fromList es'))

        U.Empty_ ->
            case typ0 of
            SArray _ -> return $ syn Empty_
            _        -> typeMismatch (Right typ0) (Left "HArray")
    
        -- Not sure Array should be a binding form
        U.Array_ e1 name e2 ->
            case typ0 of
            SArray typ1 -> do
                e1' <- checkType_ SNat e1
                let x = U.makeVar name SNat
                pushCtx (SomeVariable x) $ do
                    e2' <- checkType_ typ1 e2
                    return $ syn (Array_ e1' (bind x e2'))
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
    
        U.MBind_ name e1 e2 ->
            case typ0 of
            SMeasure _ -> do
                TypedAST typ1 e1' <- inferType_ e1
                case typ1 of
                    SMeasure typ2 ->
                        let x = U.makeVar name typ2 in
                        pushCtx (SomeVariable x) $ do
                            e2' <- checkType_ typ0 e2
                            return $ syn (MBind :$ e1' :* bind x e2' :* End)
                    _ -> typeMismatch (Right typ0) (Right typ1)
            _ -> typeMismatch (Right typ0) (Left "HMeasure")
    
        U.Expect_ name e1 e2 ->
            case typ0 of
            SProb -> do
                TypedAST typ1 e1' <- inferType_ e1
                case typ1 of
                    SMeasure typ2 ->
                        let x = U.makeVar name typ2 in
                        pushCtx (SomeVariable x) $ do
                            e2' <- checkType_ typ0 e2
                            return $ syn (Expect :$ e1' :* bind x e2' :* End)
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
                -- If we ever get evaluation at the type level, then
                -- (==) should be the appropriate notion of type
                -- equivalence. More generally, we should have that the
                -- inferred @typ'@ is a subtype of (i.e., subsumed by)
                -- the goal @typ@. This will be relevant to us for handling our coercion calculus :(
                case jmEq1 typ0 typ' of
                    Just Refl -> return e0'
                    Nothing   -> case findCoercion typ' typ0 of
                                   Just c  -> checkType typ0 $ U.CoerceTo_ (Some2 c) e0
                                   Nothing -> typeMismatch (Right typ0) (Right typ')
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
            pushCtx (SomeVariable x) $
                bind x <$> checkBranchBody bodyTyp body xs'

    checkPattern
        :: Sing a
        -> U.Pattern
        -> TypeCheckMonad (SomePattern a)
    checkPattern typA pat =
        case pat of
        U.PVar name -> return $ SP PVar  (Cons1 (U.makeVar name typA) Nil1)
        U.PWild            -> return $ SP PWild Nil1
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
findCoercion SNat  SInt  = Just $ CCons (Signed HRing_Int) CNil
findCoercion SProb SReal = Just $ CCons (Signed HRing_Real) CNil
findCoercion SNat  SProb = Just $ CCons (Continuous HContinuous_Prob) CNil
findCoercion SInt  SReal = Just $ CCons (Continuous HContinuous_Real) CNil
findCoercion SNat  SReal = Just $ CCons (Signed HRing_Int)
                           (CCons (Continuous HContinuous_Real) CNil)
findCoercion _     _     = Nothing

----------------------------------------------------------------
----------------------------------------------------------- fin.
