{-# LANGUAGE CPP
           , ScopedTypeVariables
           , GADTs
           , DataKinds
           , PolyKinds
           , GeneralizedNewtypeDeriving
           , TypeOperators
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.07.15
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
module Language.Hakaru.Syntax.TypeCheck where

import           Data.IntMap           (IntMap)
import qualified Data.IntMap           as IM
import qualified Data.Foldable         as F
#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..))
#endif
import Language.Hakaru.Syntax.Nat      (fromNat)
import Language.Hakaru.Syntax.DataKind (Hakaru(..), Code)
import Language.Hakaru.Syntax.TypeEq
import Language.Hakaru.Syntax.Coercion (singCoerceTo, singCoerceFrom)
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT

----------------------------------------------------------------
----------------------------------------------------------------

-- | Those terms from which we can synthesize a unique type. We are
-- also allowed to check them, via the change-of-direction rule.
inferable :: (ABT abt) => abt vars a -> Bool
inferable = not . mustCheck


-- | Those terms whose types must be checked analytically. We cannot
-- synthesize (unambiguous) types for these terms.
mustCheck :: (ABT abt) => abt vars a -> Bool
mustCheck = go . viewABT
    where
    go :: (ABT abt) => View abt vars a -> Bool
    go (Bind _ _) =
        error "mustCheck: you shouldn't be asking about Bind terms"
    go (Var  _)       = False

    go (Syn (Lam_ _)) = True

    -- In general, applications don't require checking; however,
    -- for fully saturated data constructors they do (according to
    -- neelk).
    go (Syn (App_ _ _)) = False

    -- We follow Dunfield & Pientka and \Pi\Sigma in inferring or
    -- checking depending on what the body requires. This is as
    -- opposed to the TLDI'05 paper, which always inders @e2@ but
    -- will check or infer the @e1@ depending on whether it has a
    -- type annotation or not.
    go (Syn (Let_ _ e2)) = mustCheck e2

    -- If our Fix_ had a type annotation on the variable, then we
    -- could infer the type by checking the body against that same
    -- type (just as if Lam_ had a type annotation on the variable).
    -- But for now we'll just have to check (again, just like Lam_).
    go (Syn (Fix_ _))          = True

    go (Syn (Ann_ _ _))        = False

    go (Syn (PrimOp_ _))       = False
    go (Syn (NaryOp_ _ _))     = False
    go (Syn (Value_ _))        = False

    -- TODO: I'm guessing for these two. Since the coercion stores
    -- concrete information about both the type of @e@ and the type
    -- of the whole expression, maybe this should behave more like
    -- 'Ann_'...?
    go (Syn (CoerceTo_   _ e)) = mustCheck e
    go (Syn (UnsafeFrom_ _ e)) = mustCheck e

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
    -- TODO: For 'Datum_', shouldn't we always be able to infer it
    -- correctly, supposing that the main components (the children
    -- of the 'HakaruFun' constructors) are all inferable? I suppose
    -- we would have some trouble inferring the tag\/name for the
    -- type...
    --
    -- In general (according to Dunfield & Pientka), we should be
    -- able to infer the result of a fully saturated primop by
    -- looking up it's type and then checking all the arguments.
    go (Syn Empty_)       = True
    go (Syn (Array_ _ _)) = True
    go (Syn (Datum_ _))   = True

    -- TODO: everyone says this, but it seems to me that if we can
    -- infer any of the branches (and check the rest to agree) then
    -- we should be able to infer the whole thing... Or maybe the
    -- problem is that the change-of-direction rule might send us
    -- down the wrong path?
    go (Syn (Case_ _ _))      = True

    go (Syn (Measure_ _))     = False
    -- TODO: I'm assuming this works like Let_, but we should make sure...
    go (Syn (Bind_ _ e2))     = mustCheck e2
    -- TODO: again, it seems like if we can infer one of the options, then we should be able to check the rest against it. But for now we'll assume we must check
    go (Syn (Superpose_ _))   = True


----------------------------------------------------------------
----------------------------------------------------------------

-- TODO: replace with an IntMap(SomeVariable), using the varID of the Variable
type Ctx = IntMap SomeVariable

data TypedPattern :: [Hakaru] -> * where
    TP  :: !(Pattern vars a)
        -> !(Sing a)
        -> TypedPattern vars
    TPC :: !(PDatumCode xss vars ('HData t (Code t)))
        -> !(Sing xss)
        -> !(Sing ('HData t (Code t)))
        -> TypedPattern vars
    TPS :: !(PDatumStruct xs vars ('HData t (Code t)))
        -> !(Sing xs)
        -> !(Sing ('HData t (Code t)))
        -> TypedPattern vars
    TPF :: !(PDatumFun x vars ('HData t (Code t)))
        -> !(Sing x)
        -> !(Sing ('HData t (Code t)))
        -> TypedPattern vars

-- We can't just use @[TypedPattern vars]@ because the @vars@ won't necessarily be constant for every element. Rather, what we want is \"@[TypedPattern] vars@\" where the @vars@ is collected over the whole list. That's what this type does.
data TypedPatternList :: [Hakaru] -> * where
    TPNil :: TypedPatternList '[]
    TPCons
        :: !(TypedPattern vars1)
        -> TypedPatternList vars2
        -> TypedPatternList (vars1 ++ vars2)

data TypedDatum (ast :: Hakaru -> *) where
    -- N.B., we do not require that @xss ~ Code t@; so we can
    -- perform induction on it!
    TDC :: !(DatumCode xss ast ('HData t (Code t)))
        -> !(Sing xss)
        -> !(Sing ('HData t (Code t)))
        -> TypedDatum ast
    TDS :: !(DatumStruct xs ast ('HData t (Code t)))
        -> !(Sing xs)
        -> !(Sing ('HData t (Code t)))
        -> TypedDatum ast
    TDF :: !(DatumFun x ast ('HData t (Code t)))
        -> !(Sing x)
        -> !(Sing ('HData t (Code t)))
        -> TypedDatum ast

----------------------------------------------------------------
type TypeCheckError = String -- TODO: something better

newtype TypeCheckMonad a =
    TCM { unTCM :: Ctx -> Either TypeCheckError a }

instance Functor TypeCheckMonad where
    fmap f m = TCM $ fmap f . unTCM m

instance Applicative TypeCheckMonad where
    pure      = TCM . const . Right
    mf <*> mx = mf >>= \f -> fmap f mx

-- TODO: ensure this instance has the appropriate strictness
instance Monad TypeCheckMonad where
    return   = pure
    mx >>= k = TCM $ \ctx -> unTCM mx ctx >>= \x -> unTCM (k x) ctx

-- | Extend the typing context, but only locally.
pushCtx :: SomeVariable -> TypeCheckMonad a -> TypeCheckMonad a
pushCtx tv@(Some x) (TCM m) =
    TCM $ \ctx -> m $ IM.insert (fromNat $ varID x) tv ctx

getCtx :: TypeCheckMonad Ctx
getCtx = TCM Right

failwith :: TypeCheckError -> TypeCheckMonad a
failwith = TCM . const . Left


----------------------------------------------------------------
----------------------------------------------------------------
-- | Given a typing environment and a term, synthesize the term's type.
inferType :: ABT abt => abt vars a -> TypeCheckMonad (Sing a)
inferType e0 =
    case viewABT e0 of
    Bind _ _  -> error "inferType: you shouldn't be asking about Bind terms"
    Var x     -> do
        ctx <- getCtx
        case IM.lookup (fromNat $ varID x) ctx of
            Just (Some x') ->
                case varEq x x' of
                Just Refl -> return (varType x')
                Nothing   -> failwith "type mismatch"
            Nothing       -> failwith "unbound variable"

    Syn (App_ e1 e2) -> do
        typ1 <- inferType e1
        case typ1 of
            SFun typ2 typ3 -> do
                checkType typ2 e2
                return typ3
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
    Syn (App_ (Syn (Lam_ e1)) e2) -> do
        typ2 <- inferType e2
        -- TODO: catch ExpectedBindException and convert it to a TypeCheckError
        caseBind e1 $ \x -> pushCtx (Some x typ2) . inferType
        -}

    Syn (Let_ e1 e2)
        | inferable e1 -> do
            typ1 <- inferType e1
            -- TODO: catch ExpectedBindException and convert it to a TypeCheckError
            caseBind e2 $ \x ->
                case jmEq typ1 (varType x) of
                Just Refl -> pushCtx (Some x) . inferType
                Nothing   -> const $ failwith "type mismatch"

    Syn (Ann_ typ1 e1) -> do
        -- N.B., this requires that @typ@ is a 'Sing' not a 'Proxy',
        -- since we can't generate a 'Sing' from a 'Proxy'.
        checkType typ1 e1
        return typ1

    Syn (PrimOp_ o) ->
        return $ sing_PrimOp o

    Syn (NaryOp_ o es) -> do
        let typ = sing_NaryOp o
        F.forM_ es $ checkType typ
        return typ

    Syn (Value_ v) ->
        -- BUG: need to finish implementing sing_Value for Datum
        return $ sing_Value v

    Syn (CoerceTo_ c e1)
        | inferable e1 -> do
            typ <- inferType e1
            return $ singCoerceTo c typ

    Syn (UnsafeFrom_ c e1)
        | inferable e1 -> do
            typ <- inferType e1
            return $ singCoerceFrom c typ

    Syn (Measure_ o) ->
        return $ sing_Measure o

    Syn (Bind_ e1 e2)
        | inferable e1 -> do
            typ1 <- inferType e1
            case typ1 of
                SMeasure typ2 ->
                    -- TODO: catch ExpectedBindException and convert it to a TypeCheckError
                    caseBind e2 $ \x ->
                        case jmEq typ2 (varType x) of
                        Just Refl -> pushCtx (Some x) . inferType
                        Nothing   -> const $ failwith "type mismatch"

    _   | mustCheck e0 -> failwith "Cannot infer types for checking terms; please add a type annotation"
        | otherwise    -> error "inferType: missing an inferable branch!"


----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: rather than returning (), we could return a fully type-annotated term...
-- | Given a typing environment, a term, and a type, check that the
-- term satisfies the type.
checkType :: ABT abt => Sing a -> abt vars a -> TypeCheckMonad ()
checkType typ0 e0 =
    case viewABT e0 of
    Bind _ _ -> error "checkType: you shouldn't be asking about Bind terms"
    Syn (Lam_ e1) ->
        case typ0 of
        SFun typ1 typ2 ->
            -- TODO: catch ExpectedBindException and convert it to a TypeCheckError
            caseBind e1 $ \x ->
                case jmEq typ1 (varType x) of
                Just Refl -> pushCtx (Some x) . checkType typ2
                Nothing   -> const $ failwith "type mismatch"
        _ -> failwith "expected function type"

    Syn (Let_ e1 e2)
        | inferable e1 -> do
            typ1 <- inferType e1
            -- TODO: catch ExpectedBindException and convert it to a TypeCheckError
            caseBind e2 $ \x ->
                case jmEq typ1 (varType x) of
                Just Refl -> pushCtx (Some x) . checkType typ0
                Nothing   -> const $ failwith "type mismatch"

    Syn (Fix_ e1) ->
        -- TODO: catch ExpectedBindException and convert it to a TypeCheckError
        caseBind e1 $ \x ->
            case jmEq typ0 (varType x) of
            Just Refl -> pushCtx (Some x) . checkType typ0
            Nothing   -> const $ failwith "type mismatch"

    Syn (CoerceTo_ c e1) ->
        checkType (singCoerceFrom c typ0) e1

    Syn (UnsafeFrom_ c e1) ->
        checkType (singCoerceTo c typ0) e1

    Syn Empty_ ->
        case typ0 of
        SArray typ1 -> return ()
            -- TODO: use jmEq to test that 'typ1' matches
        _ -> failwith "expected HArray type"

    Syn (Array_ n e1) ->
        case typ0 of
        SArray typ1 -> do
            checkType SNat n
            -- TODO: catch ExpectedBindException and convert it to a TypeCheckError
            caseBind e1 $ \x ->
                case jmEq SNat (varType x) of
                Just Refl -> pushCtx (Some x) . checkType typ1
                Nothing   -> const $ failwith "type mismatch"
        _ -> failwith "expected HArray type"

    Syn (Datum_ (Datum d)) ->
        case typ0 of
        SData _ typ2 -> checkDatum [TDC d typ2 typ0]
        _            -> failwith "expected HData type"

    Syn (Case_ e1 branches) -> do
        typ1 <- inferType e1
        F.forM_ branches $ \(Branch pat body) ->
            {-
            -- BUG: Could not deduce (xs ~ (xs ++ '[]))
            checkBranch typ0 body (TP pat typ1 `TPCons` TPNil)
            -}
            -- N.B., we need the call to 'checkBranch' to be outside the case analysis, otherwise we get some weird error about the return type being untouchable (and hence not matchable with @()@)
            checkBranch typ0 body $
                let p = TP pat typ1 in
                case eqAppendNil p of
                Refl -> TPCons p TPNil

    Syn (Bind_ e1 e2)
        | inferable e1 -> do
            typ1 <- inferType e1
            case typ1 of
                SMeasure typ2 ->
                    -- TODO: catch ExpectedBindException and convert it to a TypeCheckError
                    caseBind e2 $ \x ->
                        case jmEq typ2 (varType x) of
                        Just Refl -> pushCtx (Some x) . checkType typ0
                        Nothing   -> const $ failwith "type mismatch"

    Syn (Superpose_ pes) ->
        F.forM_ pes $ \(p,e) -> do
            checkType SProb p
            checkType typ0  e

    _   | inferable e0 -> do
            typ' <- inferType e0
            -- If we ever get evaluation at the type level, then
            -- (==) should be the appropriate notion of type
            -- equivalence. More generally, we should have that the
            -- inferred @typ'@ is a subtype of (i.e., subsumed by)
            -- the goal @typ@. This will be relevant to us for handling our coercion calculus :(
            case jmEq typ0 typ' of
                Just Refl -> return ()
                Nothing   -> failwith "Type mismatch"
        | otherwise -> error "checkType: missing an mustCheck branch!"


----------------------------------------------------------------
-- TODO: can we unify this with the last major case of 'checkBranch'?
checkDatum
    :: ABT abt
    => [TypedDatum (abt '[])]
    -> TypeCheckMonad ()
checkDatum = go
    where
    go []                     = return ()
    go (TDC d typ typA : dts) =
        case d of
        Inr d2 ->
            case typ of
            SPlus _ typ2  -> go (TDC d2 typ2 typA : dts)
            _             -> failwith "expected term of `inr' type"
        Inl d1 ->
            case typ of
            SPlus typ1 _  -> go (TDS d1 typ1 typA : dts)
            _             -> failwith "expected term of `inl' type"
    go (TDS d typ typA : dts) =
        case d of
        Et d1 d2 ->
            case typ of
            SEt typ1 typ2 -> go (TDF d1 typ1 typA : TDS d2 typ2 typA : dts)
            _             -> failwith "expected term of `et' type"
        Done ->
            case typ of
            SDone         -> go dts
            _             -> failwith "expected term of `done' type"
    go (TDF d typ typA : dts) =
        case d of
        Ident e1 ->
            case typ of
            SIdent        -> checkType typA e1 >> go dts
            _             -> failwith "expected term of `I' type"
        Konst e1 ->
            case typ of
            SKonst typ1   -> checkType typ1 e1 >> go dts
            _             -> failwith "expected term of `K' type"

----------------------------------------------------------------
checkBranch
    :: ABT abt
    => Sing b
    -> abt vars b
    -> TypedPatternList vars
    -> TypeCheckMonad ()
checkBranch body_typ body = go
    where
    go TPNil                     = checkType body_typ body
    go (TP pat typ `TPCons` pts) =
        case pat of
        PVar ->
            -- TODO: catch ExpectedBindException and convert it to a TypeCheckError
            caseBind body $ \x body' ->
                case jmEq typ (varType x) of
                Just Refl ->
                    pushCtx (Some x) $
                        checkBranch body_typ body' pts
                Nothing   -> failwith "type mismatch"

        PWild       -> go pts
        PDatum pat1 ->
            case typ of
            SData _ typ2 -> go (TPC pat1 typ2 typ `TPCons` pts)
            _ -> failwith "expected term of user-defined data type"

    -- TODO: verify that this all works the way it should!
    -- TODO: use @typA@ to provide better error messages; particularly, the first argument to its constructor 'SData'.
    go (TPC pat typ typA `TPCons` pts) =
        case pat of
        PInr pat2 ->
            case typ of
            SPlus _ typ2 -> go (TPC pat2 typ2 typA `TPCons` pts)
            _            -> failwith "expected term of `sum' type"
        PInl pat1 ->
            case typ of
            SPlus typ1 _ -> go (TPS pat1 typ1 typA `TPCons` pts)
            _            -> failwith "expected term of `zero' type"
    go (TPS pat typ typA `TPCons` pts) =
        case pat of
        PEt pat1 pat2 ->
            case typ of
            SEt typ1 typ2 -> go $
                {-
                -- BUG: Could not deduce (((vars3 ++ vars4) ++ vars2) ~ (vars3 ++ (vars4 ++ vars2)))
                ( TPCons (TPF pat1 typ1 typA)
                . TPCons (TPS pat2 typ2 typA)
                $ pts
                )
                -}
                let p1 = TPF pat1 typ1 typA
                    p2 = TPS pat2 typ2 typA
                in case eqAppendAssoc p1 p2 pts of
                    Refl -> TPCons p1 (TPCons p2 pts)
            _ -> failwith "expected term of `et' type"
        PDone ->
            case typ of
            SDone       -> go pts
            _           -> failwith "expected term of `done' type"
    go (TPF pat typ typA `TPCons` pts) =
        case pat of
        PIdent pat1 ->
            case typ of
            SIdent      -> go (TP pat1 typA `TPCons` pts)
            _           -> failwith "expected term of `I' type"
        PKonst pat1 ->
            case typ of
            SKonst typ1 -> go (TP pat1 typ1 `TPCons` pts)
            _           -> failwith "expected term of `K' type"

----------------------------------------------------------------
----------------------------------------------------------- fin.
