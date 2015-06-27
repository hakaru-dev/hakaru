{-# LANGUAGE ScopedTypeVariables
           , GADTs
           , DataKinds
           , PolyKinds
           , GeneralizedNewtypeDeriving
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.06.26
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

import           Data.IntMap       (IntMap)
import qualified Data.IntMap       as IM
import           Control.Monad     (forM_)

-- import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.TypeEq (Sing(..), TypeEq(Refl), jmEq)
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT

----------------------------------------------------------------
----------------------------------------------------------------


-- | Those terms from which we can synthesize a type. Via the
-- change-of-direction rule, we can also check their types.
isSynth :: View abt a -> Bool
isSynth = not . isCheck


-- | Those terms which /must/ be checked. We cannot synthesize
-- (unambiguous) types for these terms.
isCheck :: View abt a -> Bool
-- Actually, since we have the Proxy, we should be able to synthesize here...
isCheck (Syn (Lam_ _ _))           = True
-- TODO: all data constructors should return True (but why don't they synthesize?); thus, data constructors shouldn't be considered as primops... or at least, we need better pattern matching to grab them...
isCheck (Syn (App_ _ _))            = False -- In general, but not when a data-constructor primop is fully saturated! (or partially applied?)
isCheck (Syn (Let_ e1 e2))          = error "TODO: isCheck(Let_)"
isCheck (Syn (Fix_ e))              = error "TODO: isCheck(Fix_)"
isCheck (Syn (Ann_ _ _))            = False
isCheck (Syn (PrimOp_ o))           =
    case o of
    Unit -> True
    _    -> error "TODO: isCheck(PrimOp_)"
    -- TODO: presumably, all primops should be checkable & synthesizable
isCheck (Syn (NaryOp_ o es))        = error "TODO: isCheck(NaryOp_)"
isCheck (Syn (Integrate_ e1 e2 e3)) = error "TODO: isCheck(Integrate_)"
isCheck (Syn (Summate_   e1 e2 e3)) = error "TODO: isCheck(Summate_)"
isCheck (Syn (Value_ v))            = error "TODO: isCheck(Value_)"
isCheck (Syn (CoerceTo_   c e))     = error "TODO: isCheck(CoerceTo_)"
isCheck (Syn (UnsafeFrom_ c e))     = error "TODO: isCheck(UnsafeFrom_)"
isCheck (Syn (List_  es))           = error "TODO: isCheck(List_)"
isCheck (Syn (Maybe_ me))           = error "TODO: isCheck(Maybe_)"
isCheck (Syn (Case_  _ _))          = True
isCheck (Syn (Array_ _ _))          = True
isCheck (Syn (Bind_  e1 e2))        = error "TODO: isCheck(Bind_)"
isCheck (Syn (Superpose_ pes))      = error "TODO: isCheck(Superpose_)"
isCheck (Syn (Dp_    e1 e2))        = error "TODO: isCheck(Dp_)"
isCheck (Syn (Plate_ e))            = error "TODO: isCheck(Plate_)"
isCheck (Syn (Chain_ e))            = error "TODO: isCheck(Chain_)"
isCheck (Syn (Lub_ e1 e2))          = error "TODO: isCheck(Lub_)"
isCheck (Syn Bot_)                  = error "TODO: isCheck(Bot_)"
isCheck _                           = False -- Var is false; Open is (presumably) an error...

----------------------------------------------------------------

type TypeCheckError = String -- TODO: something better

newtype TypeCheckMonad a = TCM { unTCM :: Either TypeCheckError a }
    deriving (Functor, Applicative, Monad)
-- TODO: ensure that the monad instance has the appropriate strictness

failwith :: TypeCheckError -> TypeCheckMonad a
failwith = TCM . Left

data TypedVariable where
    TV :: {-# UNPACK #-} !Variable -> !(Sing a) -> TypedVariable

data TypedPattern where
    TP :: !(Pattern a) -> !(Sing a) -> TypedPattern

-- TODO: replace with an IntMap(TypedVariable), using the varId of the Variable
type Ctx = IntMap TypedVariable

pushCtx :: TypedVariable -> Ctx -> Ctx
pushCtx tv@(TV x _) = IM.insert (varId x) tv


-- | Given a typing environment and a term, synthesize the term's type.
synth :: ABT abt => Ctx -> abt a -> TypeCheckMonad (Sing a)
synth ctx e =
    case viewABT e of
    Var x typ ->
        case IM.lookup (varId x) ctx of
        Just (TV x' typ')
            | x' == x   ->
                case jmEq typ typ' of
                Just Refl -> return typ'
                Nothing   -> failwith "type mismatch"
            | otherwise -> error "synth: bad context"
        Nothing  -> failwith "unbound variable"
    
    Syn (Ann_ prox e) -> do
        -- TODO: generate a Sing from the Proxy; or store the Sing directly
        let typ = (error "TODO: Proxy to Sing") prox
        check ctx e typ
        return typ
    
    Syn (App_ e1 e2) -> do
        typ1 <- synth ctx e1
        case typ1 of
            SFun typ2 typ3 -> check ctx e2 typ2 >> return typ3
            -- IMPOSSIBLE: _ -> failwith "Applying a non-function!"
    
    t   | isSynth t -> error "synth: missing an isSynth branch!"
        | otherwise -> failwith "Cannot synthesize type for a checking term"


-- TODO: rather than returning (), we could return a fully type-annotated term...
-- | Given a typing environment, a term, and a type, check that the
-- term satisfies the type.
check :: ABT abt => Ctx -> abt a -> Sing a -> TypeCheckMonad ()
check ctx e typ =
    case viewABT e of
    Syn (Lam_ p e') ->
        case typ of
        SFun typ1 typ2 ->
            -- TODO: catch ExpectedOpenException and convert it to a TypeCheckError
            caseOpenABT e' $ \x t ->
            check (pushCtx (TV x typ1) ctx) t typ2
        _ -> failwith "expected HFun type"
    
    Syn (PrimOp_ Unit) ->
        case typ of
        SUnit -> return ()
        _     -> failwith "expected HUnit type"
    {-
    Syn (App_ (Syn (App_ (Syn (PrimOp_ Pair)) e1)) e2) ->
        case typ of
        SPair typ1 typ2 -> check ctx e1 typ1 >> check ctx e2 typ2
        _               -> failwith "expected HPair type"
    
    Syn (App_ (Syn (PrimOp_ Inl)) e) ->
        case typ of
        SEither typ1 _ -> check ctx e typ1
        _              -> failwith "expected HEither type"
        
    Syn (App_ (Syn (PrimOp_ Inr)) e) ->
        case typ of
        SEither _ typ2 -> check ctx e typ2
        _              -> failwith "expected HEither type"
    -}
    Syn (Case_ e' branches) -> do
        typ' <- synth ctx e'
        forM_ branches $ \(Branch pat body) ->
            checkBranch ctx [TP pat typ'] body typ
    
    Syn (Array_ n e') ->
        case typ of
        SArray typ1 ->
            -- TODO: catch ExpectedOpenException and convert it to a TypeCheckError
            caseOpenABT e' $ \x t ->
            check (pushCtx (TV x SNat) ctx) t typ1
        _ -> failwith "expected HArray type"
    
    t   | isCheck t -> error "check: missing an isCheck branch!"
        | otherwise -> do
            typ' <- synth ctx e
            if typ == typ' -- TODO: would using 'jmEq' be better?
            then return ()
            else failwith "Type mismatch"


checkBranch
    :: ABT abt
    => Ctx
    -> [TypedPattern]
    -> abt b
    -> Sing b
    -> TypeCheckMonad ()
checkBranch ctx []                 e body_typ = check ctx e body_typ
checkBranch ctx (TP pat typ : pts) e body_typ =
    case pat of
    PVar ->
        -- TODO: catch ExpectedOpenException and convert it to a TypeCheckError
        caseOpenABT e $ \x e' ->
        checkBranch (pushCtx (TV x typ) ctx) pts e' body_typ
    PWild ->
        checkBranch ctx pts e body_typ
    PTrue ->
        case typ of
        SBool -> checkBranch ctx pts e body_typ
        _     -> failwith "expected term of HBool type"
    PFalse ->
        case typ of
        SBool -> checkBranch ctx pts e body_typ
        _     -> failwith "expected term of HBool type"
    PUnit ->
        case typ of
        SUnit -> checkBranch ctx pts e body_typ
        _     -> failwith "expected term of HUnit type"
    PPair pat1 pat2 ->
        case typ of
        SPair typ1 typ2 ->
            checkBranch ctx (TP pat1 typ1 : TP pat2 typ2 : pts) e body_typ
        _ -> failwith "expected term of HPair type"
    PInl pat1 ->
        case typ of
        SEither typ1 _ ->
            checkBranch ctx (TP pat1 typ1 : pts) e body_typ
        _ -> failwith "expected HEither type"
    PInr pat2 ->
        case typ of
        SEither _ typ2 ->
            checkBranch ctx (TP pat2 typ2 : pts) e body_typ
        _ -> failwith "expected HEither type"

----------------------------------------------------------------
----------------------------------------------------------- fin.
