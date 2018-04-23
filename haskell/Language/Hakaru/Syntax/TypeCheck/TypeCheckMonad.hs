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
-- |
-- Module      :  Language.Hakaru.Syntax.TypeCheck
-- Copyright   :  Copyright (c) 2017 the Hakaru team
-- License     :  BSD3
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Bidirectional type checking for our AST.
----------------------------------------------------------------
module Language.Hakaru.Syntax.TypeCheck.TypeCheckMonad where

import           Prelude hiding (id, (.))
import           Control.Category
import           Data.Proxy            (KProxy(..))
import           Data.Text             (Text())
import qualified Data.Vector           as V
#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..), (<$>))
import           Data.Monoid           (Monoid(..))
#endif
import qualified Language.Hakaru.Parser.AST as U

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Types.DataKind (Hakaru(..), HData', HBool)
import Language.Hakaru.Types.Sing
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Types.HClasses
    ( HEq, hEq_Sing, HOrd, hOrd_Sing, HSemiring, hSemiring_Sing
    , hRing_Sing, sing_HRing, hFractional_Sing)
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.Reducer
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Pretty.Concrete (prettyTypeT)

-- | * Definition of the typechecking monad and related
-- types\/functions\/instances.

type Input = Maybe (V.Vector Text)

type Ctx = VarSet ('KProxy :: KProxy Hakaru)

data TypeCheckMode = StrictMode | LaxMode | UnsafeMode
    deriving (Read, Show)

type TypeCheckError = Text

newtype TypeCheckMonad a =
    TCM { unTCM :: Ctx
                -> Input
                -> TypeCheckMode
                -> Either TypeCheckError a }

runTCM :: TypeCheckMonad a -> Input -> TypeCheckMode -> Either TypeCheckError a
runTCM m = unTCM m emptyVarSet

instance Functor TypeCheckMonad where
    fmap f m = TCM $ \ctx input mode -> fmap f (unTCM m ctx input mode)

instance Applicative TypeCheckMonad where
    pure x    = TCM $ \_ _ _ -> Right x
    mf <*> mx = mf >>= \f -> fmap f mx

-- TODO: ensure this instance has the appropriate strictness
instance Monad TypeCheckMonad where
    return   = pure
    mx >>= k =
        TCM $ \ctx input mode ->
        unTCM mx ctx input mode >>= \x ->
        unTCM (k x) ctx input mode

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
getInput :: TypeCheckMonad Input
getInput = TCM $ \_ input _ -> Right input

-- | Return the mode in which we're checking\/inferring types.
getMode :: TypeCheckMonad TypeCheckMode
getMode = TCM $ \_ _ mode -> Right mode

-- | Extend the typing context, but only locally.
pushCtx
    :: Variable (a :: Hakaru)
    -> TypeCheckMonad b
    -> TypeCheckMonad b
pushCtx x (TCM m) = TCM (m . insertVarSet x)

getCtx :: TypeCheckMonad Ctx
getCtx = TCM $ \ctx _ _ -> Right ctx

failwith :: TypeCheckError -> TypeCheckMonad r
failwith e = TCM $ \_ _ _ -> Left e

failwith_ :: TypeCheckError -> TypeCheckMonad r
failwith_ = failwith

-- TODO: some day we may want a variant of this function which
-- returns the error message in the event that the computation fails
-- (e.g., to provide all of them if 'inferOneCheckOthers' ultimately
-- fails.
--
-- | a la @optional :: Alternative f => f a -> f (Maybe a)@ but
-- without needing the 'empty' of the 'Alternative' class.
try :: TypeCheckMonad a -> TypeCheckMonad (Maybe a)
try m = TCM $ \ctx input mode -> Right $
    case unTCM m ctx input mode of
    Left  _ -> Nothing -- Don't worry; no side effects to unwind
    Right e -> Just e

-- | Tries to typecheck in a given mode
tryWith :: TypeCheckMode -> TypeCheckMonad a -> TypeCheckMonad (Maybe a)
tryWith mode m = TCM $ \ctx input _ -> Right $
    case unTCM m ctx input mode of
    Left  _ -> Nothing
    Right e -> Just e

-- | * Helpers for constructing error messages

makeErrMsg
    :: Text
    -> Maybe U.SourceSpan
    -> Text
    -> TypeCheckMonad TypeCheckError
makeErrMsg header sourceSpan footer = do
  input_ <- getInput
  case (sourceSpan, input_) of
    (Just s, Just input) ->
          return $ mconcat [ header
                           , "\n"
                           , U.printSourceSpan s input
                           , footer
                           ]
    _                    ->
          return $ mconcat [ header, "\n", footer ]

-- | Fail with a type-mismatch error.
typeMismatch
    :: Maybe U.SourceSpan
    -> Either Text (Sing (a :: Hakaru))
    -> Either Text (Sing (b :: Hakaru))
    -> TypeCheckMonad r
typeMismatch s typ1 typ2 = failwith =<<
    makeErrMsg
     "Type Mismatch:"
     s
     (mconcat [ "expected "
              , msg1
              , ", found "
              , msg2
              ])
    where
    msg1 = case typ1 of { Left msg -> msg; Right typ -> prettyTypeT typ }
    msg2 = case typ2 of { Left msg -> msg; Right typ -> prettyTypeT typ }

missingInstance
    :: Text
    -> Sing (a :: Hakaru)
    -> Maybe U.SourceSpan
    -> TypeCheckMonad r
missingInstance clas typ s = failwith =<<
   makeErrMsg
    "Missing Instance:"
    s
    (mconcat $ ["No ", clas, " instance for type ", prettyTypeT typ])

missingLub
    :: Sing (a :: Hakaru)
    -> Sing (b :: Hakaru)
    -> Maybe U.SourceSpan
    -> TypeCheckMonad r
missingLub typ1 typ2 s = failwith =<<
    makeErrMsg
     "Missing common type:"
     s
     (mconcat ["No lub of types ", prettyTypeT typ1, " and ", prettyTypeT typ2])

-- we can't have free variables, so it must be a typo
ambiguousFreeVariable
    :: Text
    -> Maybe U.SourceSpan
    -> TypeCheckMonad r
ambiguousFreeVariable x s = failwith =<<
    makeErrMsg
     (mconcat $ ["Name not in scope: ", x])
     s
     "Perhaps it is a typo?"

ambiguousNullCoercion
    :: Maybe U.SourceSpan
    -> TypeCheckMonad r
ambiguousNullCoercion s = failwith =<<
    makeErrMsg
     "Cannot infer type for null-coercion over a checking term."
     s
     "Please add a type annotation to either the term being coerced or the result of the coercion."

ambiguousEmptyNary
    :: Maybe U.SourceSpan
    -> TypeCheckMonad r
ambiguousEmptyNary s = failwith =<<
    makeErrMsg
     "Cannot infer unambiguous type for empty n-ary operator."
     s
     "Try adding an annotation on the result of the operator."

ambiguousMustCheckNary
    :: Maybe U.SourceSpan
    -> TypeCheckMonad r
ambiguousMustCheckNary s = failwith =<<
    makeErrMsg
     "Could not infer any of the arguments."
     s
     "Try adding a type annotation to at least one of them."

ambiguousMustCheck
    :: Maybe U.SourceSpan
    -> TypeCheckMonad r
ambiguousMustCheck s = failwith =<<
    makeErrMsg
     "Cannot infer types for checking terms."
     s
     "Please add a type annotation."

argumentNumberError
     :: TypeCheckMonad r
argumentNumberError = failwith =<<
    makeErrMsg "Argument error:" Nothing "Passed wrong number of arguments"

-- | * Terms whose type is existentially quantified packed with a singleton for
-- the type.

-- BUG: haddock doesn't like annotations on GADT constructors. So
-- here we'll avoid using the GADT syntax, even though it'd make
-- the data type declaration prettier\/cleaner.
-- <https://github.com/hakaru-dev/hakaru/issues/6>
--
-- | The @e' ∈ τ@ portion of the inference judgement.
data TypedAST (abt :: [Hakaru] -> Hakaru -> *)
    = forall b. TypedAST !(Sing b) !(abt '[] b)

onTypedAST :: (forall b . abt '[] b -> abt '[] b) -> TypedAST abt -> TypedAST abt
onTypedAST f (TypedAST t p) = TypedAST t (f p)

onTypedASTM :: (Functor m)
            => (forall b . abt '[] b -> m (abt '[] b))
            -> TypedAST abt -> m (TypedAST abt)
onTypedASTM f (TypedAST t p) = TypedAST t <$> f p

elimTypedAST :: (forall b . Sing b -> abt '[] b -> x) -> TypedAST abt -> x 
elimTypedAST f (TypedAST t p) = f t p 

instance Show2 abt => Show (TypedAST abt) where
    showsPrec p (TypedAST typ e) =
        showParen_12 p "TypedAST" typ e


----------------------------------------------------------------
data TypedASTs (abt :: [Hakaru] -> Hakaru -> *)
    = forall b. TypedASTs !(Sing b) [abt '[] b]

{-
instance Show2 abt => Show (TypedASTs abt) where
    showsPrec p (TypedASTs typ es) =
        showParen_1x p "TypedASTs" typ es
-}

----------------------------------------------------------------
-- HACK: Passing this list of variables feels like a hack
-- it would be nice if it could be removed from this datatype
data TypedReducer (abt :: [Hakaru] -> Hakaru -> *)
                  (xs  :: [Hakaru])
    = forall b. TypedReducer !(Sing b) (List1 Variable xs) (Reducer abt xs b)

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

data SomeBranch a abt = forall b. SomeBranch !(Sing b) [Branch a abt b]

-- | * Misc.

makeVar :: forall (a :: Hakaru). Variable 'U.U -> Sing a -> Variable a
makeVar (Variable hintID nameID _) typ =
    Variable hintID nameID typ

make_NaryOp :: Sing a -> U.NaryOp -> TypeCheckMonad (NaryOp a)
make_NaryOp a U.And  = isBool a >>= \Refl -> return And
make_NaryOp a U.Or   = isBool a >>= \Refl -> return Or
make_NaryOp a U.Xor  = isBool a >>= \Refl -> return Xor
make_NaryOp a U.Iff  = isBool a >>= \Refl -> return Iff
make_NaryOp a U.Min  = Min  <$> getHOrd a
make_NaryOp a U.Max  = Max  <$> getHOrd a
make_NaryOp a U.Sum  = Sum  <$> getHSemiring a
make_NaryOp a U.Prod = Prod <$> getHSemiring a

isBool :: Sing a -> TypeCheckMonad (TypeEq a HBool)
isBool typ =
    case jmEq1 typ sBool of
    Just proof -> return proof
    Nothing    -> typeMismatch Nothing (Left "HBool") (Right typ)


jmEq1_ :: Sing (a :: Hakaru)
       -> Sing (b :: Hakaru)
       -> TypeCheckMonad (TypeEq a b)
jmEq1_ typA typB =
    case jmEq1 typA typB of
    Just proof -> return proof
    Nothing    -> typeMismatch Nothing (Right typA) (Right typB)


getHEq :: Sing a -> TypeCheckMonad (HEq a)
getHEq typ =
    case hEq_Sing typ of
    Just theEq -> return theEq
    Nothing    -> missingInstance "HEq" typ Nothing

getHOrd :: Sing a -> TypeCheckMonad (HOrd a)
getHOrd typ =
    case hOrd_Sing typ of
    Just theOrd -> return theOrd
    Nothing     -> missingInstance "HOrd" typ Nothing

getHSemiring :: Sing a -> TypeCheckMonad (HSemiring a)
getHSemiring typ =
    case hSemiring_Sing typ of
    Just theSemi -> return theSemi
    Nothing      -> missingInstance "HSemiring" typ Nothing

getHRing :: Sing a -> TypeCheckMode -> TypeCheckMonad (SomeRing a)
getHRing typ mode =
    case mode of
    StrictMode -> case hRing_Sing typ of
                    Just theRing -> return (SomeRing theRing CNil)
                    Nothing      -> missingInstance "HRing" typ Nothing
    LaxMode    -> case findRing typ of
                    Just proof   -> return proof
                    Nothing      -> missingInstance "HRing" typ Nothing
    UnsafeMode -> case findRing typ of
                    Just proof   -> return proof
                    Nothing      -> missingInstance "HRing" typ Nothing

getHFractional :: Sing a -> TypeCheckMode -> TypeCheckMonad (SomeFractional a)
getHFractional typ mode =
    case mode of
    StrictMode -> case hFractional_Sing typ of
                    Just theFrac -> return (SomeFractional theFrac CNil)
                    Nothing      -> missingInstance "HFractional" typ Nothing
    LaxMode    -> case findFractional typ of
                    Just proof   -> return proof
                    Nothing      -> missingInstance "HFractional" typ Nothing
    UnsafeMode -> case findFractional typ of
                    Just proof   -> return proof
                    Nothing      -> missingInstance "HFractional" typ Nothing

-- TODO: find a better name, and move to where 'LC_' is defined.
lc :: (LC_ abt a -> LC_ abt b) -> abt '[] a -> abt '[] b
lc f = unLC_ . f . LC_

coerceTo_nonLC :: (ABT Term abt) => Coercion a b -> abt xs a -> abt xs b
coerceTo_nonLC = underBinders . lc . coerceTo

coerceFrom_nonLC :: (ABT Term abt) => Coercion a b -> abt xs b -> abt xs a
coerceFrom_nonLC = underBinders . lc . coerceFrom

-- BUG: how to make this not an orphan, without dealing with cyclic imports between AST.hs (for the 'LC_' instance), Datum.hs, and Coercion.hs?
instance (ABT Term abt) => Coerce (Branch a abt) where
    coerceTo   c (Branch pat e) = Branch pat (coerceTo_nonLC   c e)
    coerceFrom c (Branch pat e) = Branch pat (coerceFrom_nonLC c e)
