{-# LANGUAGE CPP
           , ScopedTypeVariables
           , GADTs
           , DataKinds
           , PolyKinds
           , GeneralizedNewtypeDeriving
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.06.30
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
import           Control.Monad         (forM_)
#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative)
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
inferable :: (ABT abt) => View abt a -> Bool
inferable = not . mustCheck



-- | Those terms whose types must be checked analytically. We cannot
-- synthesize (unambiguous) types for these terms.
mustCheck :: (ABT abt) => View abt a -> Bool

-- Actually, since we have the Proxy, we should be able to synthesize
-- here...
mustCheck (Syn (Lam_ _ _)) = True

-- In general, applications don't require checking; however, for
-- fully saturated data constructors they do (according to neelk).
-- Thus, we should beware of the 'Empty' primop. (Maybe we should
-- move it back to 'AST'?)
mustCheck (Syn (App_ _ _)) = False

-- N.B., the TLDI'05 paper says we'll always infer the @e2@ but
-- will check or infer the @e1@ depending on whether it has a type
-- annotation or not. However, Dunfield & Pientka have us always
-- inferring the @e1@ and then checking or inferring the @e2@ as
-- appropriate...
mustCheck (Syn (Let_ _ e2)) = mustCheck (viewABT e2)

-- If our Fix_ had a type annotation on the variable, then we could
-- infer the type by checking the body against that same type...
-- But for now, we'll just have to check.
mustCheck (Syn (Fix_ e))          = True

mustCheck (Syn (Ann_ _ _))        = False

mustCheck (Syn (PrimOp_ _))       = False
mustCheck (Syn (NaryOp_ _ _))     = False
mustCheck (Syn (Value_ _))        = False

-- TODO: I'm guessing for these two
mustCheck (Syn (CoerceTo_   _ e)) = mustCheck (viewABT e)
mustCheck (Syn (UnsafeFrom_ _ e)) = mustCheck (viewABT e)

-- I just say this because neelk says all data constructors mustCheck
-- (even though that doesn't seem right to me). TODO: Seems to me
-- that if we can infer the body, then we should be able to infer
-- the whole thing, right? Or maybe the problem is that the
-- change-of-direction rule might send us down the wrong path?
-- Usually I'd assume the binder is what does it, but here we know
-- the type of the bound variable, because it's the same for every
-- Array
mustCheck (Syn (Array_ _ _)) = True

-- I return true because most folks (neelk, Pfenning, Dunfield &
-- Pientka) say all data constructors mustCheck (even though that
-- doesn't seem right to me; also, cf.,
-- <http://jozefg.bitbucket.org/posts/2014-11-22-bidir.html>).
--
-- TODO: shouldn't we always be able to infer it correctly, supposing
-- that the main components (the children of the 'HakaruFun'
-- constructors) are all inferable? I suppose we would have some
-- trouble inferring the tag\/name for the type...
--
-- In general (according to Dunfield & Pientka), we should be able
-- to infer the result of a fully saturated primop by looking up
-- it's type and then checking all the arguments.
mustCheck (Syn (Datum_ _)) = True

-- TODO: everyone says this, but it seems to me that if we can infer
-- any of the branches (and check the rest to agree) then we should
-- be able to infer the whole thing... Or maybe the problem is that
-- the change-of-direction rule might send us down the wrong path?
mustCheck (Syn (Case_ _ _))      = True

mustCheck (Syn (Measure_ _))     = False
-- TODO: I'm assuming this works like Let_, but we should make sure...
mustCheck (Syn (Bind_ _ e2))     = mustCheck (viewABT e2)
mustCheck (Syn (Superpose_ pes)) = error "TODO: mustCheck(Superpose_)"
mustCheck (Syn (Lub_    e1 e2))  = error "TODO: mustCheck(Lub_)"
mustCheck (Syn Bot_)             = error "TODO: mustCheck(Bot_)"
mustCheck (Var  _ _)             = False
mustCheck (Open _ _)             = error "mustCheck: you shouldn't be asking about Open terms" -- Presumably this ought to be an error, rather than False (right?)


----------------------------------------------------------------
----------------------------------------------------------------

type TypeCheckError = String -- TODO: something better

newtype TypeCheckMonad a = TCM { unTCM :: Either TypeCheckError a }
    deriving (Functor, Applicative, Monad)
-- TODO: ensure that the monad instance has the appropriate strictness

failwith :: TypeCheckError -> TypeCheckMonad a
failwith = TCM . Left

data TypedVariable where
    TV :: {-# UNPACK #-} !Variable -> !(Sing (a :: Hakaru)) -> TypedVariable

data TypedPattern where
    TP  :: !(Pattern a) -> !(Sing a) -> TypedPattern
    TDP :: {-# UNPACK #-} !(TypedDatum Pattern) -> TypedPattern

data TypedDatum (abt :: Hakaru -> *) where
    -- N.B., we do not require that @sop ~ Code t@; so we can
    -- perform induction on it!
    TD  :: !(PartialDatum sop abt ('HData t (Code t)))
        -> !(Sing sop)
        -> !(Sing ('HData t (Code t)))
        -> TypedDatum abt

-- TODO: replace with an IntMap(TypedVariable), using the varID of the Variable
type Ctx = IntMap TypedVariable

pushCtx :: TypedVariable -> Ctx -> Ctx
pushCtx tv@(TV x _) = IM.insert (fromNat $ varID x) tv


----------------------------------------------------------------
----------------------------------------------------------------
-- | Given a typing environment and a term, synthesize the term's type.
inferType :: ABT abt => Ctx -> abt a -> TypeCheckMonad (Sing a)
inferType ctx e =
    case viewABT e of
    Var x typ ->
        case IM.lookup (fromNat $ varID x) ctx of
        Just (TV x' typ')
            | x' == x ->
                case jmEq typ typ' of
                Just Refl -> return typ'
                Nothing   -> failwith "type mismatch"
            | otherwise   -> error "inferType: bad context"
        Nothing           -> failwith "unbound variable"

    Syn (App_ e1 e2) -> do
        -- N.B., the SFun part is irrefutable\/complete
        SFun typ2 typ3 <- inferType ctx e1
        checkType ctx e2 typ2
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
    Syn (App_ (Syn (Lam_ p e1)) e2) -> do
        typ2 <- inferType ctx e2
        -- TODO: catch ExpectedOpenException and convert it to a TypeCheckError
        caseOpenABT e1 $ \x e' ->
            inferType (pushCtx (TV x typ2) ctx) e'
        -}

    Syn (Let_ e1 e2)
        | inferable (viewABT e1) -> do
            typ1 <- inferType ctx e1
            -- TODO: catch ExpectedOpenException and convert it to a TypeCheckError
            caseOpenABT e2 $ \x e' ->
                inferType (pushCtx (TV x typ1) ctx) e'
        | otherwise -> error "TODO: inferType{LetA}"
            {-
            -- TODO: this version of let-binding should come with @typ1@ annotation on the variable. That is, based on the TLDI'05 paper, I think we need two different AST constructors, one for inferable @e1@ and the other for mustCheck @e1@... But for now we can always fake that by putting an Ann_ on the @e1@ itself
            checkType ctx e1 typ1
            -- TODO: catch ExpectedOpenException and convert it to a TypeCheckError
            caseOpenABT e2 $ \x e' ->
                inferType (pushCtx (TV x typ1) ctx) e'
            -}

    Syn (Ann_ typ e') -> do
        -- N.B., this requires that @typ@ is a 'Sing' not a 'Proxy',
        -- since we can't generate a 'Sing' from a 'Proxy'.
        checkType ctx e' typ
        return typ

    Syn (PrimOp_ o) ->
        -- BUG: need to finish implementing singPrimOp
        return (singPrimOp o)

    Syn (NaryOp_ o es) -> do
        -- BUG: need to finish implementing singNaryOp
        let typ = singNaryOp o
        forM_ (F.toList es) $ \e' ->
            checkType ctx e' typ
        return typ

    Syn (Value_ v) ->
        return (singValue v)

    Syn (CoerceTo_ c e1)
        | inferable (viewABT e1) -> do
            typ <- inferType ctx e1
            return (singCoerceTo c typ)

    Syn (UnsafeFrom_ c e1)
        | inferable (viewABT e1) -> do
            typ <- inferType ctx e1
            return (singCoerceFrom c typ)

    Syn (Measure_ o) ->
        -- BUG: need to finish implementing singMeasure
        return (singMeasure o)

    Syn (Bind_ e1 e2)
        | inferable (viewABT e1) -> do
            -- N.B., that pattern is irrefutable\/complete
            SMeasure typ1 <- inferType ctx e1
            -- TODO: catch ExpectedOpenException and convert it to a TypeCheckError
            caseOpenABT e2 $ \x e' ->
                inferType (pushCtx (TV x typ1) ctx) e'
        | otherwise -> error "TODO: inferType{BindA}"

    t   | inferable t -> error "inferType: missing an inferable branch!"
        | otherwise   -> failwith "Cannot infer types for checking terms; please add a type annotation"


----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: rather than returning (), we could return a fully type-annotated term...
-- | Given a typing environment, a term, and a type, check that the
-- term satisfies the type.
checkType :: ABT abt => Ctx -> abt a -> Sing a -> TypeCheckMonad ()
checkType ctx e typ =
    case viewABT e of
    Syn (Lam_ _ e1) ->
        case typ of
        SFun typ1 typ2 ->
            -- TODO: catch ExpectedOpenException and convert it to a TypeCheckError
            caseOpenABT e1 $ \x e' ->
                checkType (pushCtx (TV x typ1) ctx) e' typ2
        _ -> failwith "expected function type"

    Syn (Let_ e1 e2)
        | inferable (viewABT e1) -> do
            typ1 <- inferType ctx e1
            -- TODO: catch ExpectedOpenException and convert it to a TypeCheckError
            caseOpenABT e2 $ \x e' ->
                checkType (pushCtx (TV x typ1) ctx) e' typ
        | otherwise -> error "TODO: checkType{LetA}"

    Syn (Fix_ e1) ->
        -- TODO: catch ExpectedOpenException and convert it to a TypeCheckError
        caseOpenABT e1 $ \x e' ->
            checkType (pushCtx (TV x typ) ctx) e' typ

    Syn (CoerceTo_ c e1) ->
        checkType ctx e1 (singCoerceFrom c typ)

    Syn (UnsafeFrom_ c e1) ->
        checkType ctx e1 (singCoerceTo c typ)

    Syn (Array_ n e1) ->
        case typ of
        SArray typ1 -> do
            checkType ctx n SNat
            -- TODO: catch ExpectedOpenException and convert it to a TypeCheckError
            caseOpenABT e1 $ \x e' ->
                checkType (pushCtx (TV x SNat) ctx) e' typ1
        _ -> failwith "expected HArray type"

    Syn (Datum_ (Datum d)) ->
        case typ of
        SData _ typ2 -> checkDatum ctx [TD d typ2 typ]
        _            -> failwith "expected HData type"

    Syn (Case_ e1 branches) -> do
        typ1 <- inferType ctx e1
        forM_ branches $ \(Branch pat body) ->
            checkBranch ctx body typ [TP pat typ1]

    Syn (Bind_ e1 e2)
        | inferable (viewABT e1) -> do
            -- N.B., that pattern is irrefutable\/complete
            SMeasure typ1 <- inferType ctx e1
            -- TODO: catch ExpectedOpenException and convert it to a TypeCheckError
            caseOpenABT e2 $ \x e' ->
                checkType (pushCtx (TV x typ1) ctx) e' typ
        | otherwise -> error "TODO: checkType{BindA}"

    t   | mustCheck t -> error "checkType: missing an mustCheck branch!"
        | otherwise   -> do
            typ' <- inferType ctx e
            -- If we ever get evaluation at the type level, then
            -- (==) should be the appropriate notion of type
            -- equivalence. More generally, we should have that the
            -- inferred @typ'@ is a subtype of (i.e., subsumed by)
            -- the goal @typ@. This will be relevant to us for handling our coercion calculus :(
            case jmEq typ typ' of
                Just Refl -> return ()
                Nothing   -> failwith "Type mismatch"


----------------------------------------------------------------
-- TODO: can we unify this with the last major case of 'checkBranch'?
checkDatum
    :: ABT abt
    => Ctx
    -> [TypedDatum abt]
    -> TypeCheckMonad ()
checkDatum ctx = go
    where
    go []                    = return ()
    go (TD d typ typA : dts) =
        case d of
        Done ->
            case typ of
            SDone `SPlus` SVoid -> go dts
            _                   -> failwith "expected term of `done' type"

        d1 `Et` d2 ->
            case typ of
            (typ1 `SEt` typ2) `SPlus` SVoid -> go
                ( TD d1 ((typ1 `SEt` SDone) `SPlus` SVoid) typA
                : TD d2 (typ2 `SPlus` SVoid) typA
                : dts
                )
            _ -> failwith "expected term of `et' type"

        Inl d1 ->
            case typ of
            typ1 `SPlus` _ -> go (TD d1 (typ1 `SPlus` SVoid) typA : dts)
            _              -> failwith "expected term of `inl' type"

        Inr d2 ->
            case typ of
            _ `SPlus` typ2 -> go (TD d2 typ2 typA : dts)
            _              -> failwith "expected term of `inr' type"

        Ident e1 ->
            case typ of
            (SIdent `SEt` SDone) `SPlus` SVoid -> do
                checkType ctx e1 typA
                go dts
            _ -> failwith "expected term of `I' type"

        Konst e1 ->
            case typ of
            (SKonst typ1 `SEt` SDone) `SPlus` SVoid -> do
                checkType ctx e1 typ1
                go dts
            _ -> failwith "expected term of `K' type"

----------------------------------------------------------------
checkBranch
    :: ABT abt
    => Ctx
    -> abt b
    -> Sing b
    -> [TypedPattern]
    -> TypeCheckMonad ()
checkBranch ctx body body_typ = go
    where
    go []                 = checkType ctx body body_typ
    go (TP pat typ : pts) =
        case pat of
        PVar ->
            -- TODO: catch ExpectedOpenException and convert it to a TypeCheckError
            caseOpenABT body $ \x body' ->
                checkBranch (pushCtx (TV x typ) ctx) body' body_typ pts

        PWild               -> go pts
        PDatum (Datum pat1) ->
            case typ of
            SData _ typ2 -> go (TDP (TD pat1 typ2 typ) : pts)
            _ -> failwith "expected term of user-defined data type"

    go (TDP (TD pat typ typA) : pts) =
        -- TODO: verify that this all works the way it should!
        -- TODO: use @typA@ to provide better error messages; particularly, the first argument to its constructor 'SData'.
        case pat of
        Done ->
            case typ of
            SDone `SPlus` SVoid -> go pts
            _                   -> failwith "expected term of `done' type"

        pat1 `Et` pat2 ->
            case typ of
            (typ1 `SEt` typ2) `SPlus` SVoid -> go
                ( TDP (TD pat1 ((typ1 `SEt` SDone) `SPlus` SVoid) typA)
                : TDP (TD pat2 (typ2 `SPlus` SVoid) typA)
                : pts
                )
            _ -> failwith "expected term of `et' type"

        Inl pat1 ->
            case typ of
            SPlus typ1 _ -> go (TDP (TD pat1 (SPlus typ1 SVoid) typA) : pts)
            _            -> failwith "expected term of `zero' type"

        Inr pat2 ->
            case typ of
            SPlus _ typ2 -> go (TDP (TD pat2 typ2 typA) : pts)
            _            -> failwith "expected term of `sum' type"

        Ident pat1 ->
            case typ of
            (SIdent `SEt` SDone) `SPlus` SVoid -> go (TP pat1 typA : pts)
            _ -> failwith "expected term of `I' type"

        Konst pat1 ->
            case typ of
            (SKonst typ1 `SEt` SDone) `SPlus` SVoid ->
                go (TP pat1 typ1 : pts)
            _ -> failwith "expected term of `K' type"

----------------------------------------------------------------
----------------------------------------------------------- fin.
