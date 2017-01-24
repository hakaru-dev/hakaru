{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE EmptyCase                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
module Language.Hakaru.Syntax.ANF where

--------------------------------------------------------------------------------
-- An implementation of A-normalization as described in
--   https://pdfs.semanticscholar.org/5da1/4c8b7851e56e4bf08e30db4ced54be989768.pdf
-- A-normalization is not strictly necessary, but make implementing later
-- transformations easy, as all non-trivial operations are assigned names.
--
-- The planned pipeline:
-- 1. ANF conversion
-- 2. Expression hoising (perform operations as soon as their data dependencies
--    are satisified)
-- 3. (Conditional hoisting)
-- 4. CSE (in order to clean up work duplicated by hoisting)
--------------------------------------------------------------------------------

import           Prelude                          hiding (product, (*), (+), (-), (==), (>>=), (<))

import qualified Data.IntMap                      as IM
import           Data.Number.Nat
import           Data.Sequence                    ((<|))
import qualified Data.Sequence                    as S

import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.Datum
import           Language.Hakaru.Syntax.DatumCase
import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Syntax.Variable
import           Language.Hakaru.Types.Coercion
import           Language.Hakaru.Types.DataKind
import           Language.Hakaru.Types.HClasses
import           Language.Hakaru.Types.Sing

import           Language.Hakaru.Syntax.Prelude

-- The renaming environment which maps variables in the original term to their
-- counterparts in the new term. This is needed since the mechanism which
-- ensures hygiene for the AST only factors in binders, but not free variables
-- in the expression being constructed. When we construct a new binding form, a
-- new variable is introduced and the variable in the old expression must be
-- mapped to the new one.

norm2 :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
norm2 =
    normal (real_ 3) (prob_ 2) >>= \x ->
    normal (real_ 5) (prob_ 4) >>= \y ->
    dirac $ if_ (x < y)
        (pair y x)
        (pair x x)

data EAssoc =
    forall (a :: Hakaru) . EAssoc {-# UNPACK #-} !(Variable a) {-# UNPACK #-} !(Variable a)

newtype Env = Env (IM.IntMap EAssoc)

emptyEnv :: Env
emptyEnv = Env IM.empty

updateEnv :: forall (a :: Hakaru) . Variable a -> Variable a -> Env -> Env
updateEnv vin vout = updateEnv' (EAssoc vin vout)

updateEnv' :: EAssoc -> Env -> Env
updateEnv' v@(EAssoc x _) (Env xs) =
    Env $ IM.insert (fromNat $ varID x) v xs

lookupVar :: forall (a :: Hakaru) . Variable a -> Env -> Maybe (Variable a)
lookupVar x (Env env) = do
    EAssoc v1 v2 <- IM.lookup (fromNat $ varID x) env
    Refl         <- varEq x v1
    return $ v2

-- | The context in which A-normalization occurs. Represented as a continuation,
-- the context expects an expression of a particular type (usually a variable)
-- and produces a new expression as a result.
type Context abt a b = abt '[] a -> abt '[] b

-- | Extract a variable from an abt. This function is partial
getVar :: (ABT Term abt) => abt xs a -> Variable a
getVar abt = case viewABT abt of
               Var v -> v
               _     -> error "getVar: not given a variable"

-- | Useful function for generating fresh variables from an existing variable by
-- wrapping @binder@.
freshVar
  :: (ABT Term abt)
  => Variable a
  -> (Variable a -> abt xs b)
  -> abt (a ': xs) b
freshVar var f = binder (varHint var) (varType var) (f . getVar)

-- | Entry point for the normalization process. Initializes normalize' with the
-- empty context.
normalize
  :: (ABT Term abt)
  => abt '[] a
  -> abt '[] a
normalize abt = normalize' abt emptyEnv id

normalize'
  :: (ABT Term abt)
  => abt '[] a
  -> Env
  -> Context abt a b
  -> abt '[] b
normalize' abt = caseVarSyn abt normalizeVar normalizeTerm

normalizeVar :: (ABT Term abt) => (Variable a) -> Env -> Context abt a b -> abt '[] b
normalizeVar v env ctxt =
  case lookupVar v env of
    Just v' -> ctxt (var v')
    Nothing -> ctxt (var v)

isValue
  :: (ABT Term abt)
  => abt xs a
  -> Bool
isValue abt =
  case viewABT abt of
    Var{}  -> True
    Bind{} -> False
    Syn s  -> isValueTerm s
  where
    isValueTerm Literal_{}  = True
    isValueTerm Datum_{}    = True
    isValueTerm (Lam_ :$ _) = True
    isValueTerm _           = False

normalizeTerm
  :: (ABT Term abt)
  => Term abt a
  -> Env
  -> Context abt a b
  -> abt '[] b
normalizeTerm (NaryOp_ op args) = normalizeNaryOp op args
normalizeTerm (x :$ args)       = normalizeSCon x args
normalizeTerm (Case_ c bs)      = normalizeCase c bs
normalizeTerm term              = const ($ syn term)

remapVar
  :: (ABT Term abt)
  => Variable a
  -> Env
  -> (Env -> abt xs b)
  -> abt (a ': xs) b
remapVar var env f = freshVar var $ \var' ->
  let env' = updateEnv var var' env
  in f env'

normalizeCase
  :: forall a b c abt . (ABT Term abt)
  => abt '[] a
  -> [Branch a abt b]
  -> Env
  -> Context abt b c
  -> abt '[] c
normalizeCase cond bs env ctxt =
  normalizeName cond env $ \ cond' ->
    let -- TODO: How do we deal with pattern variables?
        normalizeBranch :: Branch a abt b -> Branch a abt b
        normalizeBranch (Branch pat body) =
          case pat of
            PWild -> Branch PWild (normalize' body env id)
            PVar  -> caseBind body $ \v body' ->
                       Branch PVar $ remapVar v env $ \ env' ->
                         normalize' body' env' id

            -- Minimum needed to match True and False
            PDatum t (PInl PDone)        -> Branch pat (normalize' body env id)
            PDatum t (PInr (PInl PDone)) -> Branch pat (normalize' body env id)
            _     -> error "normalizeBranch: pattern variables not implemented"

        bs' = map normalizeBranch bs
    in ctxt $ syn (Case_ cond' bs')

normalizeName
  :: (ABT Term abt)
  => abt '[] a
  -> Env
  -> Context abt a b
  -> abt '[] b
normalizeName abt env ctxt = normalize' abt env giveName
  where
    giveName abt' | isValue abt' = ctxt abt'
                  | otherwise    = let_ abt' ctxt

normalizeNames
  :: (ABT Term abt)
  => S.Seq (abt '[] a)
  -> Env
  -> (S.Seq (abt '[] a) -> abt '[] b)
  -> abt '[] b
normalizeNames abts env = foldr f ($ S.empty) abts
  where
    f x acc ctxt = normalizeName x env $ \t -> acc (ctxt . (t <|))

{-normalizeSArgs-}
  {-:: forall (a :: Hakaru) abt args . (ABT Term abt)-}
  {-=> SArgs abt args-}
  {--> Env-}
  {--> (SArgs abt args -> abt '[] a)-}
  {--> abt '[] a-}
{-normalizeSArgs args env ctxt =-}
  {-case args of-}
    {-End     -> ctxt End-}
    {-x :* xs -> normalizeName x   $ \t ->-}
               {-normalizeSArgs xs $ \ts ->-}
               {-ctxt (t :* ts)-}

normalizeNaryOp
  :: (ABT Term abt)
  => NaryOp a
  -> S.Seq (abt '[] a)
  -> Env
  -> Context abt a b
  -> abt '[] b
normalizeNaryOp op args env ctxt = normalizeNames args env (ctxt . syn . NaryOp_ op)

normalizeSCon
  :: (ABT Term abt)
  => SCon args a
  -> SArgs abt args
  -> Env
  -> Context abt a b
  -> abt '[] b

normalizeSCon Lam_ =
  \(body :* End) env ctxt -> caseBind body $
    \v body' ->
      let f var = normalize' body' (updateEnv v var env) id
      in ctxt $ syn (Lam_ :$ freshVar v f :* End)

normalizeSCon Let_ =
  \(rhs :* body :* End) env ctxt -> caseBind body $
    \v body' ->
      normalize' rhs env $ \rhs' ->
        let_ rhs' $ \v' ->
          let var  = getVar v'
              env' = updateEnv v var env
          in normalize' body' env' ctxt

-- TODO: Remove code duplication between sum and product cases
normalizeSCon s@Summate{} =
  \(lo :* hi :* body :* End) env ctxt ->
    normalizeName lo env $ \lo' ->
    normalizeName hi env $ \hi' ->
    caseBind body $ \v body' ->
    let f var  = normalize' body' (updateEnv v var env) id
        body'' = freshVar v f
    in ctxt $ syn (s :$ lo' :* hi' :* body'' :* End)

normalizeSCon p@Product{} =
  \(lo :* hi :* body :* End) env ctxt ->
    normalizeName lo env $ \lo' ->
    normalizeName hi env $ \hi' ->
    caseBind body $ \v body' ->
    let f var  = normalize' body' (updateEnv v var env) id
        body'' = freshVar v f
    in ctxt $ syn (p :$ lo' :* hi' :* body'' :* End)

normalizeSCon MBind =
  \(ma :* b :* End) env ctxt ->
    normalize' ma env $ \ma' ->
    caseBind b $ \v b' ->
    let f var = normalize' b' (updateEnv v var env) id
        b''   = freshVar v f
    in ctxt $ syn (MBind :$ ma' :* b'' :* End)

normalizeSCon Dirac =
  \(e :* end) env ctxt -> normalize' e env (ctxt . dirac)

normalizeSCon (MeasureOp_ op) = normalizeMeasureOp op

normalizeSCon (ArrayOp_ _) = error "normalizeSCon: ArrayOp unimplemented" -- flattenArrayOp op
normalizeSCon (PrimOp_ op) = normalizePrimOp op
normalizeSCon op           = error $ "not implemented: normalizeSCon{" ++ show op ++ "}"

normalizePrimOp
  :: (ABT Term abt, args ~ LCs typs)
  => PrimOp typs a
  -> SArgs abt args
  -> Env
  -> Context abt a b
  -> abt '[] b
normalizePrimOp op xs env ctxt =
  case (op, xs) of
    -- Logical operatons
    (Not  ,      x :* End) -> normalizePrimOp1 op x env ctxt
    (Impl , x :* y :* End) -> normalizePrimOp2 op x y env ctxt
    (Diff , x :* y :* End) -> normalizePrimOp2 op x y env ctxt
    (Nand , x :* y :* End) -> normalizePrimOp2 op x y env ctxt
    (Nor  , x :* y :* End) -> normalizePrimOp2 op x y env ctxt

    -- Trig stuff
    (Pi  ,      End)      -> ctxt $ primOp0_ Pi
    (Sin , x :* End)      -> normalizePrimOp1 op x env ctxt
    (Cos , x :* End)      -> normalizePrimOp1 op x env ctxt
    (Tan , x :* End)      -> normalizePrimOp1 op x env ctxt

    -- Comparisons
    (Equal _ , x :* y :* End) -> normalizePrimOp2 op x y env ctxt
    (Less _  , x :* y :* End) -> normalizePrimOp2 op x y env ctxt

    -- HSemiring operations
    (NatPow _ , x :* y :* End) -> normalizePrimOp2 op x y env ctxt

    -- HRing operations
    (Negate _  ,      x :* End) -> normalizePrimOp1 op x env ctxt
    (Abs _     ,      x :* End) -> normalizePrimOp1 op x env ctxt
    (Signum _  ,      x :* End) -> normalizePrimOp1 op x env ctxt
    (Recip _   ,      x :* End) -> normalizePrimOp1 op x env ctxt
    (NatRoot _ , x :* y :* End) -> normalizePrimOp2 op x y env ctxt

normalizePrimOp1
  :: (ABT Term abt)
  => PrimOp '[ a ] r
  -> abt '[] a
  -> Env
  -> Context abt r r'
  -> abt '[] r'
normalizePrimOp1 op x env ctxt = normalizeName x env (ctxt . primOp1_ op)

normalizePrimOp2
  :: (ABT Term abt)
  => PrimOp '[ a, b ] r
  -> abt '[] a -> abt '[] b
  -> Env
  -> Context abt r r'
  -> abt '[] r'
normalizePrimOp2 op x y env ctxt =
  normalizeName x env $ \x' ->
  normalizeName y env $ \y' ->
  ctxt (primOp2_ op x' y')

normalizePrimOp3
  :: (ABT Term abt)
  => PrimOp '[ a, b, c ] r
  -> abt '[] a -> abt '[] b -> abt '[] c
  -> Env
  -> Context abt r r'
  -> abt '[] r'
normalizePrimOp3 op x y z env ctxt =
  normalizeName x env $ \x' ->
  normalizeName y env $ \y' ->
  normalizeName z env $ \z' ->
  ctxt (primOp3_ op x' y' z')

-- TODO: Would be nice to get this simple version working
{-normalizePrimOp-}
  {-:: (ABT Term abt, args ~ LCs typs, typs ~ UnLCs args, '[] ~ AllArgs args)-}
  {-=> PrimOp typs a-}
  {--> SArgs abt args-}
  {--> Env-}
  {--> Context abt a b-}
  {--> abt '[] b-}
{-normalizePrimOp op (x :* End)           = normalizePrimOp1 op x-}
{-normalizePrimOp op (x :* y :* End)      = normalizePrimOp2 op x y-}
{-normalizePrimOp op (x :* y :* z :* End) = normalizePrimOp3 op x y z-}

normalizeMeasureOp2
  :: (ABT Term abt)
  => MeasureOp '[ a, b ] r
  -> abt '[] a -> abt '[] b
  -> Env
  -> Context abt ('HMeasure r) r'
  -> abt '[] r'
normalizeMeasureOp2 op x y env ctxt =
  normalizeName x env $ \x' ->
  normalizeName y env $ \y' ->
  ctxt (measure2_ op x' y')

normalizeMeasureOp
  :: (ABT Term abt, args ~ LCs typs)
  => MeasureOp typs a
  -> SArgs abt args
  -> Env
  -> Context abt ('HMeasure a) b
  -> abt '[] b
normalizeMeasureOp op xs env ctxt =
  case (op, xs) of
    (Lebesgue    ,           End) -> ctxt $ measure0_ op
    (Counting    ,           End) -> ctxt $ measure0_ op
    (Categorical ,      x :* End) -> normalizeName x env (ctxt . measure1_ op)
    (Poisson     ,      x :* End) -> normalizeName x env (ctxt . measure1_ op)
    (Uniform     , x :* y :* End) -> normalizeMeasureOp2 op x y env ctxt
    (Normal      , x :* y :* End) -> normalizeMeasureOp2 op x y env ctxt
    (Gamma       , x :* y :* End) -> normalizeMeasureOp2 op x y env ctxt
    (Beta        , x :* y :* End) -> normalizeMeasureOp2 op x y env ctxt
