{-# LANGUAGE CPP
           , ScopedTypeVariables
           , GADTs
           , DataKinds
           , KindSignatures
           , GeneralizedNewtypeDeriving
           , TypeOperators
           , FlexibleContexts
           , FlexibleInstances
           , Rank2Types
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.12.29
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
    (
    -- * The type checking monad
      TypeCheckError
    , TypeCheckMonad(), runTCM, unTCM
    , TypeCheckMode(..)
    -- * Type checking itself
    , inferable
    , mustCheck
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
import qualified Language.Hakaru.Parser.AST as U

import Data.Number.Nat                (fromNat)
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Types.DataKind (Hakaru(..), HData', HBool)
import Language.Hakaru.Types.Sing
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Types.HClasses
    (HOrd, hOrd_Sing, HSemiring, hSemiring_Sing)
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.AST.Sing
    (sing_Literal, sing_PrimOp, sing_ArrayOp, sing_MeasureOp)


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
mustCheck = go
    where
    go (U.Var_ _)    = False
    go (U.Lam_ _ _)  = True

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
    go (U.App_ _  _) = False

    -- We follow Dunfield & Pientka and \Pi\Sigma in inferring or
    -- checking depending on what the body requires. This is as
    -- opposed to the TLDI'05 paper, which always infers @e2@ but
    -- will check or infer the @e1@ depending on whether it has a
    -- type annotation or not.
    go (U.Let_ _ _ e2)    = mustCheck e2

    go (U.Ann_ _ _)       = False
    go (U.CoerceTo_ _ _)  = False
    go (U.UnsafeTo_ _ _)  = False

    -- In general (according to Dunfield & Pientka), we should be
    -- able to infer the result of a fully saturated primop by
    -- looking up it's type and then checking all the arguments.
    go (U.PrimOp_  _ _)   = False
    go (U.ArrayOp_ _ _)   = False

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

data TypeCheckMode = StrictMode | LaxMode | UnsafeMode
    deriving (Read, Show)

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

{-
-- We could provide this instance, but there's no decent error
-- message to give for the 'empty' case that works in all circumstances.
-- Because we only would need this to define 'inferOneCheckOthers',
-- we inline the definition there instead.
instance Alternative TypeCheckMonad where
    empty   = failwith "Alternative.empty"
    x <|> y = TCM $ \ctx mode ->
        case unTCM x ctx mode of
        Left  _ -> unTCM y ctx mode
        Right e -> Right e
-}

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
    :: Either String (Sing (a :: Hakaru))
    -> Either String (Sing (b :: Hakaru))
    -> TypeCheckMonad r
typeMismatch typ1 typ2 =
    failwith $ "Type Mismatch: expected " ++ msg1 ++ ", found " ++ msg2
    where
    msg1 = case typ1 of { Left msg -> msg; Right typ -> show1 typ }
    msg2 = case typ2 of { Left msg -> msg; Right typ -> show1 typ }

missingInstance
    :: String
    -> Sing (a :: Hakaru)
    -> TypeCheckMonad r
missingInstance clas typ =
    failwith $ "No " ++ clas ++ " instance for type " ++ show typ

missingLub
    :: Sing (a :: Hakaru)
    -> Sing (b :: Hakaru)
    -> TypeCheckMonad r
missingLub typ1 typ2 =
    failwith $ "No lub of types " ++ show typ1 ++ " and " ++ show typ2

ambiguousFreeVariable :: U.Name -> TypeCheckMonad r
ambiguousFreeVariable x =
    failwith $ "Cannot infer unambiguous type of free variable: " ++ show x

ambiguousNullCoercion :: TypeCheckMonad r
ambiguousNullCoercion =
    failwith "Cannot infer type for null-coercion over a checking term. Please add a type annotation to either the term being coerced or the result of the coercion."

ambiguousEmptyNary :: TypeCheckMonad r
ambiguousEmptyNary =
    failwith "Cannot infer unambiguous type for empty n-ary operator. Try adding an annotation on the result of the operator."

ambiguousMustCheckNary :: TypeCheckMonad r
ambiguousMustCheckNary =
    failwith "Could not infer any of the arguments. Try adding a type annotation to at least one of them."

ambiguousMustCheck :: TypeCheckMonad r
ambiguousMustCheck =
    failwith "Cannot infer types for checking terms. Please add a type annotation."

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


inferBinder
    :: (ABT Term abt)
    => Variable a
    -> U.AST
    -> (forall b. Sing b -> abt '[ a ] b -> TypeCheckMonad r)
    -> TypeCheckMonad r
inferBinder x e k = do
    TypedAST typ e' <- pushCtx x (inferType e)
    k typ (bind x e')

inferBinders
    :: (ABT Term abt)
    => List1 Variable xs
    -> U.AST
    -> (forall a. Sing a -> abt xs a -> TypeCheckMonad r)
    -> TypeCheckMonad r
inferBinders xs e k = do
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
    => Variable a
    -> Sing b
    -> U.AST
    -> TypeCheckMonad (abt '[ a ] b)
checkBinder x eTyp e =
    pushCtx x (bind x <$> checkType eTyp e)


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


  -- HACK: We need this monomorphic binding so that GHC doesn't get
  -- confused about which @(ABT AST abt)@ instance to use in recursive
  -- calls.
  inferType_ :: U.AST -> TypeCheckMonad (TypedAST abt)
  inferType_ e0 =
    case e0 of
    U.Var_ x -> do
        ctx <- getCtx
        case IM.lookup (fromNat $ U.nameID x) (unVarSet ctx) of
            Just (SomeVariable x') ->
                return $ TypedAST (varType x') (var x')
            Nothing -> ambiguousFreeVariable x

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
        inferBinder (U.makeVar x typ1) e2 $ \typ2 e2' ->
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

    U.ArrayOp_ (U.SealedOp op) es -> do
        let (typs, typ1) = sing_ArrayOp op
        es' <- checkSArgs typs es
        return . TypedAST typ1 $ syn (ArrayOp_ op :$ es')

    U.NaryOp_ op es -> do
        mode <- getMode
        TypedASTs typ es' <-
            case mode of
            StrictMode -> inferOneCheckOthers_ es
            LaxMode    -> inferLubType es
            UnsafeMode -> error "TODO: inferType{NaryOp_} in UnsafeMode"
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
            | otherwise    -> ambiguousNullCoercion
        Just (dom,cod) -> do
            e1' <- checkType_ dom e1
            return . TypedAST cod $ syn (CoerceTo_ c :$ e1' :* End)

    U.UnsafeTo_ (Some2 c) e1 ->
        case singCoerceDomCod c of
        Nothing
            | inferable e1 -> inferType_ e1
            | otherwise    -> ambiguousNullCoercion
        Just (dom,cod) -> do
            e1' <- checkType_ cod e1
            return . TypedAST dom $ syn (UnsafeFrom_ c :$ e1' :* End)

    U.MeasureOp_ (U.SealedOp op) es -> do
        let (typs, typ1) = sing_MeasureOp op
        es' <- checkSArgs typs es
        return . TypedAST (SMeasure typ1) $ syn (MeasureOp_ op :$ es')

    U.Case_ e1 branches -> do
        TypedAST typ1 e1' <- inferType_ e1
        mode <- getMode
        case mode of
            StrictMode -> inferCaseStrict typ1 e1' branches
            LaxMode    -> inferCaseLax typ1 e1' branches
            UnsafeMode -> error "TODO: inferType{Case_} in UnsafeMode"

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
                inferBinder (U.makeVar x typ2) e2 $ \typ3 e2' ->
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
                e2' <- checkBinder (U.makeVar x typ2) SProb e2
                return . TypedAST SProb $ syn (Expect :$ e1' :* e2' :* End)
            _ -> typeMismatch (Left "HMeasure") (Right typ1)

    U.Superpose_ pes -> do
        -- TODO: clean up all this @map fst@, @map snd@, @zip@ stuff
        mode <- getMode
        TypedASTs typ es' <-
            case mode of
            StrictMode -> inferOneCheckOthers_ (map snd pes)
            LaxMode    -> inferLubType         (map snd pes)
            UnsafeMode -> error "TODO: inferType{Superpose_} in UnsafeMode"
        case typ of
            SMeasure _ -> do
                ps' <- T.traverse (checkType SProb) (map fst pes)
                return $ TypedAST typ (syn (Superpose_ (zip ps' es')))
            _ -> typeMismatch (Left "HMeasure") (Right typ)

    _   | mustCheck e0 -> ambiguousMustCheck
        | otherwise    -> error "inferType: missing an inferable branch!"


make_NaryOp :: Sing a -> U.NaryOp' -> TypeCheckMonad (NaryOp a)
make_NaryOp a U.And'  = isBool a >>= \Refl -> return And
make_NaryOp a U.Or'   = isBool a >>= \Refl -> return Or
make_NaryOp a U.Xor'  = isBool a >>= \Refl -> return Xor
make_NaryOp a U.Iff'  = isBool a >>= \Refl -> return Iff
make_NaryOp a U.Min'  = Min  <$> getHOrd a
make_NaryOp a U.Max'  = Max  <$> getHOrd a
make_NaryOp a U.Sum'  = Sum  <$> getHSemiring a
make_NaryOp a U.Prod' = Prod <$> getHSemiring a

isBool :: Sing a -> TypeCheckMonad (TypeEq a HBool)
isBool typ =
    case jmEq1 typ sBool of
    Just proof -> return proof
    Nothing    -> typeMismatch (Left "HBool") (Right typ)

getHOrd :: Sing a -> TypeCheckMonad (HOrd a)
getHOrd typ =
    case hOrd_Sing typ of
    Just theOrd -> return theOrd
    Nothing     -> missingInstance "HOrd" typ

getHSemiring :: Sing a -> TypeCheckMonad (HSemiring a)
getHSemiring typ =
    case hSemiring_Sing typ of
    Just theSemi -> return theSemi
    Nothing      -> missingInstance "HSemiring" typ


----------------------------------------------------------------
data TypedASTs (abt :: [Hakaru] -> Hakaru -> *)
    = forall b. TypedASTs !(Sing b) [abt '[] b]

{-
instance Show2 abt => Show (TypedASTs abt) where
    showsPrec p (TypedASTs typ es) =
        showParen_1x p "TypedASTs" typ es
-}


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
        | null ls   = ambiguousEmptyNary
        | otherwise = ambiguousMustCheckNary
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


-- TODO: some day we may want a variant of this function which
-- returns the error message in the event that the computation fails
-- (e.g., to provide all of them if 'inferOneCheckOthers' ultimately
-- fails.
--
-- | a la @optional :: Alternative f => f a -> f (Maybe a)@ but
-- without needing the 'empty' of the 'Alternative' class.
try :: TypeCheckMonad a -> TypeCheckMonad (Maybe a)
try m = TCM $ \ctx mode -> Right $
    case unTCM m ctx mode of
    Left  _ -> Nothing -- Don't worry; no side effects to unwind
    Right e -> Just e


-- | Given a list of terms which must all have the same type, infer
-- all the terms in order and coerce them to the lub of all their
-- types. This is appropriate for 'LaxMode' where we need to insert
-- coercions; for 'StrictMode', see 'inferOneCheckOthers' instead.
inferLubType
    :: forall abt
    .  (ABT Term abt)
    => [U.AST]
    -> TypeCheckMonad (TypedASTs abt)
inferLubType = start
    where
    start :: [U.AST] -> TypeCheckMonad (TypedASTs abt)
    start []     = ambiguousEmptyNary
    start (u:us) = do
        TypedAST  typ1 e1 <- inferType u
        TypedASTs typ2 es <- F.foldlM step (TypedASTs typ1 [e1]) us
        return (TypedASTs typ2 (reverse es))

    -- TODO: inline 'F.foldlM' and then inline this, to unpack the first argument.
    step :: TypedASTs abt -> U.AST -> TypeCheckMonad (TypedASTs abt)
    step (TypedASTs typ1 es) u = do
        TypedAST typ2 e2 <- inferType u
        case findLub typ1 typ2 of
            Nothing              -> missingLub typ1 typ2
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
        | null ls   = ambiguousEmptyNary
        | otherwise = ambiguousMustCheckNary
    inferOne ls (b@(U.Branch pat e):rs) = do
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

data SomeBranch a abt = forall b. SomeBranch !(Sing b) [Branch a abt b]

inferCaseLax
    :: forall abt a
    .  (ABT Term abt)
    => Sing a
    -> abt '[] a
    -> [U.Branch]
    -> TypeCheckMonad (TypedAST abt)
inferCaseLax typA e1 = start
    where
    start :: [U.Branch] -> TypeCheckMonad (TypedAST abt)
    start []     = ambiguousEmptyNary
    start ((U.Branch pat e):us) = do
        SP pat' vars <- checkPattern typA pat
        inferBinders vars e $ \typ1 e' -> do
          SomeBranch typ2 bs <- F.foldlM step (SomeBranch typ1 [Branch pat' e']) us
          return (TypedAST typ2 $ syn (Case_ e1 (reverse bs)))

    -- TODO: inline 'F.foldlM' and then inline this, to unpack the first argument.
    step :: SomeBranch a abt -> U.Branch -> TypeCheckMonad (SomeBranch a abt)
    step (SomeBranch typ1 bs) (U.Branch pat e) = do
        SP pat' vars <- checkPattern typA pat
        inferBinders vars e $ \typ2 e2 ->
         case findLub typ1 typ2 of
            Nothing              -> missingLub typ1 typ2
            Just (Lub typ c1 c2) ->
                let bs' = map (\(Branch pat e) ->
                                   let (vars', e') = caseBinds e in
                                   let e'' = binds_ vars'
                                             (syn $ CoerceTo_ c1 :$ e' :* End) in
                                   Branch pat e'') bs
                    (vars', e2') = caseBinds e2
                    e2'' = Branch pat' (binds_ vars'
                                        (syn $ CoerceTo_ c2 :$ e2' :* End)) 
                in return (SomeBranch typ (e2'' : bs'))


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

    checkType_
        :: forall b. Sing b -> U.AST -> TypeCheckMonad (abt '[] b)
    checkType_ typ0 e0 =
        case e0 of
        U.Lam_ x e1 ->
            case typ0 of
            SFun typ1 typ2 -> do
                e1' <- checkBinder (U.makeVar x typ1) typ2 e1
                return $ syn (Lam_ :$ e1' :* End)
            _ -> typeMismatch (Right typ0) (Left "function type")

        U.Let_ x e1 e2 -> do
            TypedAST typ1 e1' <- inferType_ e1
            e2' <- checkBinder (U.makeVar x typ1) typ0 e2
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

        U.NaryOp_ op es -> do
            op' <- make_NaryOp typ0 op
            es' <- T.forM es $ checkType_ typ0
            return $ syn (NaryOp_ op' (S.fromList es'))

        U.Empty_ ->
            case typ0 of
            SArray _ -> return $ syn (Empty_ typ0)
            _        -> typeMismatch (Right typ0) (Left "HArray")

        U.Array_ e1 x e2 ->
            case typ0 of
            SArray typ1 -> do
                e1' <- checkType_ SNat e1
                e2' <- checkBinder (U.makeVar x SNat) typ1 e2
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
                        e2' <- checkBinder (U.makeVar x typ2) typ0 e2
                        return $ syn (MBind :$ e1' :* e2' :* End)
                    _ -> typeMismatch (Right typ0) (Right typ1)
            _ -> typeMismatch (Right typ0) (Left "HMeasure")

        U.Expect_ x e1 e2 ->
            case typ0 of
            SProb -> do
                TypedAST typ1 e1' <- inferType_ e1
                case typ1 of
                    SMeasure typ2 -> do
                        e2' <- checkBinder (U.makeVar x typ2) typ0 e2
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
                    Just c  -> return . unLC_ . coerceTo c $ LC_ e0'
                    Nothing -> typeMismatch (Right typ0) (Right typ')
                  UnsafeMode ->
                    case findEitherCoercion typ' typ0 of
                    Just (Left  c) ->
                        return . unLC_ . coerceFrom c $ LC_ e0'
                    Just (Right c) ->
                        return . unLC_ . coerceTo c $ LC_ e0'
                    Nothing ->
                        typeMismatch (Right typ0) (Right typ')
            | otherwise -> error "checkType: missing an mustCheck branch!"


    --------------------------------------------------------
    -- We make these local to 'checkType' for the same reason we have 'checkType_'
    -- TODO: can we combine these in with the 'checkBranch' functions somehow?
    checkDatumCode
        :: forall xss t
        .  Sing (HData' t)
        -> Sing xss
        -> U.DCode
        -> TypeCheckMonad (DatumCode xss (abt '[]) (HData' t))
    checkDatumCode typA typ d =
        case d of
        U.Inr d2 ->
            case typ of
            SPlus _ typ2 -> Inr <$> checkDatumCode typA typ2 d2
            _            -> failwith "expected datum of `inr' type"
        U.Inl d1 ->
            case typ of
            SPlus typ1 _ -> Inl <$> checkDatumStruct typA typ1 d1
            _            -> failwith "expected datum of `inl' type"

    checkDatumStruct
        :: forall xs t
        .  Sing (HData' t)
        -> Sing xs
        -> U.DStruct
        -> TypeCheckMonad (DatumStruct xs (abt '[]) (HData' t))
    checkDatumStruct typA typ d =
        case d of
        U.Et d1 d2 ->
            case typ of
            SEt typ1 typ2 -> Et
                <$> checkDatumFun    typA typ1 d1
                <*> checkDatumStruct typA typ2 d2
            _     -> failwith "expected datum of `et' type"
        U.Done ->
            case typ of
            SDone -> return Done
            _     -> failwith "expected datum of `done' type"

    checkDatumFun
        :: forall x t
        .  Sing (HData' t)
        -> Sing x
        -> U.DFun
        -> TypeCheckMonad (DatumFun x (abt '[]) (HData' t))
    checkDatumFun typA typ d =
        case d of
        U.Ident e1 ->
            case typ of
            SIdent      -> Ident <$> checkType_ typA e1
            _           -> failwith "expected datum of `I' type"
        U.Konst e1 ->
            case typ of
            SKonst typ1 -> Konst <$> checkType_ typ1 e1
            _           -> failwith "expected datum of `K' type"


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
    :: (ABT Term abt)
    => Sing a
    -> Sing b
    -> U.Branch
    -> TypeCheckMonad (Branch a abt b)
checkBranch patTyp bodyTyp (U.Branch pat body) = do
    SP pat' vars <- checkPattern patTyp pat
    Branch pat' <$> checkBinders vars bodyTyp body

checkPattern
    :: Sing a
    -> U.Pattern
    -> TypeCheckMonad (SomePattern a)
checkPattern = \typA pat ->
    case pat of
    U.PVar x -> return $ SP PVar (Cons1 (U.makeVar x typA) Nil1)
    U.PWild  -> return $ SP PWild Nil1
    U.PDatum hint pat1 ->
        case typA of
        SData _ typ1 -> do
            SPC pat1' xs <- checkPatternCode typA typ1 pat1
            return $ SP (PDatum hint pat1') xs
        _ -> typeMismatch (Right typA) (Left "HData")
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
            _            -> failwith "expected pattern of `sum' type"
        U.PInl pat1 ->
            case typ of
            SPlus typ1 _ -> do
                SPS pat1' xs <- checkPatternStruct typA typ1 pat1
                return $ SPC (PInl pat1') xs
            _ -> failwith "expected pattern of `zero' type"

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
            _ -> failwith "expected pattern of `et' type"
        U.PDone ->
            case typ of
            SDone -> return $ SPS PDone Nil1
            _     -> failwith "expected pattern of `done' type"

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
            _ -> failwith "expected pattern of `I' type"
        U.PKonst pat1 ->
            case typ of
            SKonst typ1 -> do
                SP pat1' xs <- checkPattern typ1 pat1
                return $ SPF (PKonst pat1') xs
            _ -> failwith "expected pattern of `K' type"

----------------------------------------------------------------
----------------------------------------------------------- fin.
