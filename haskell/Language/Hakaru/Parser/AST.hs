{-# LANGUAGE CPP
           , GADTs
           , DataKinds
           , PolyKinds
           , ExistentialQuantification
           , StandaloneDeriving
           , TypeFamilies
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}

module Language.Hakaru.Parser.AST where

import           Control.Arrow ((***))

import qualified Data.Foldable       as F
import qualified Data.Number.Nat     as N
import qualified Data.Number.Natural as N
import           Data.Typeable       hiding (Refl)
import qualified Data.List.NonEmpty  as L

import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
    (Literal(..), MeasureOp(..), LCs(), UnLCs ())
import Language.Hakaru.Syntax.IClasses

#if __GLASGOW_HASKELL__ < 710
import Data.Monoid   (Monoid(..))
#endif

import Data.Text
import Text.Parsec (SourcePos)

-- N.B., because we're not using the ABT's trick for implementing a HOAS API, we can make the identifier strict.
data Name = Name {-# UNPACK #-}!N.Nat {-# UNPACK #-}!Text
    deriving (Read, Show, Eq, Ord)

nameID :: Name -> N.Nat
nameID (Name i _) = i

hintID :: Name -> Text
hintID (Name _ t) = t

----------------------------------------------------------------
----------------------------------------------------------------

type Name' = Text

data Branch' a
    = Branch'  (Pattern' Name') (AST' a)
    | Branch'' (Pattern' Name)  (AST' a)
    deriving (Eq, Show)

data Pattern' a
    = PVar'  a
    | PWild'
    | PData' (PDatum a)
    deriving (Eq, Show)

data PDatum a = DV Name' [Pattern' a]
    deriving (Eq, Show)

-- Meta stores start and end position for AST in source code
data SourceSpan = SourceSpan !SourcePos !SourcePos
    deriving (Eq, Show)

data Literal'
    = Nat  Integer
    | Int  Integer
    | Prob Rational
    | Real Rational
    deriving (Eq, Show)

data NaryOp
    = And | Or   | Xor
    | Iff | Min  | Max 
    | Sum | Prod
    deriving (Eq, Show)

data ArrayOp = Index_ | Size | Reduce

data TypeAST'
    = TypeVar Name'
    | TypeApp Name'    [TypeAST']
    | TypeFun TypeAST' TypeAST'
    deriving (Eq, Show)

data AST' a
    = Var a
    | Lam a TypeAST' (AST' a) 
    | App (AST' a) (AST' a)
    | Let a    (AST' a) (AST' a)
    | If  (AST' a) (AST' a) (AST' a)
    | Ann (AST' a) TypeAST'
    | Infinity'
    | ULiteral Literal'
    | NaryOp NaryOp [AST' a]
    | Unit
    | Empty
    | Pair (AST' a) (AST' a)
    | Array a (AST' a) (AST' a)
    | Index (AST' a) (AST' a)
    | Case  (AST' a) [(Branch' a)] -- match
    | Dirac (AST' a)
    | Bind  a  (AST' a) (AST' a)
    | Plate a  (AST' a) (AST' a)
    | Chain a  (AST' a) (AST' a) (AST' a)
    | Integrate a (AST' a) (AST' a) (AST' a)
    | Summate   a (AST' a) (AST' a) (AST' a)
    | Product   a (AST' a) (AST' a) (AST' a)
    | Expect a (AST' a) (AST' a)
    | Observe  (AST' a) (AST' a)
    | Msum  [AST' a]
    | Data  a [TypeAST']
    | WithMeta (AST' a) SourceSpan
    deriving (Eq, Show)

data Import a = Import a 

----------------------------------------------------------------
----------------------------------------------------------------

val :: Literal' -> Some1 Literal
val (Nat  n) = Some1 $ LNat  (N.unsafeNatural n)
val (Int  n) = Some1 $ LInt  n
val (Prob n) = Some1 $ LProb (N.unsafeNonNegativeRational n)
val (Real n) = Some1 $ LReal n

data PrimOp
    = Not | Impl | Diff   | Nand | Nor
    | Pi
    | Sin        | Cos    | Tan
    | Asin       | Acos   | Atan
    | Sinh       | Cosh   | Tanh
    | Asinh      | Acosh  | Atanh
    | RealPow    | NatPow
    | Exp        | Log    | Infinity
    | GammaFunc  | BetaFunc
    | Equal      | Less
    | Negate     | Recip
    | Abs        | Signum | NatRoot | Erf
    deriving (Eq, Show)

data SomeOp op where
    SomeOp
        :: (typs ~ UnLCs args, args ~ LCs typs)
        => !(op typs a)
        -> SomeOp op

data SSing =
    forall (a :: Hakaru). SSing !(Sing a)

data Branch_ abt = Branch_ Pattern (abt '[] 'U)

fmapBranch
    :: (f '[] 'U -> g '[] 'U)
    -> Branch_ f
    -> Branch_ g
fmapBranch f (Branch_ pat e) = Branch_ pat (f e)

foldBranch
    :: (abt '[] 'U -> m)
    -> Branch_ abt
    -> m
foldBranch f (Branch_ _ e) = f e

data Pattern
    = PWild
    | PVar Name
    | PDatum Text PCode

data PFun
    = PKonst Pattern
    | PIdent Pattern

data PStruct
    = PEt PFun PStruct
    | PDone

data PCode
    = PInr PCode
    | PInl PStruct

infixr 7 `Et`, `PEt`

data DFun abt
    = Konst (abt '[] 'U)
    | Ident (abt '[] 'U)

data DStruct abt
    = Et (DFun abt) (DStruct abt)
    | Done

data DCode abt
    = Inr (DCode   abt)
    | Inl (DStruct abt)

data Datum abt = Datum Text (DCode abt)

fmapDatum
    :: (f '[] 'U -> g '[] 'U)
    -> Datum f
    -> Datum g
fmapDatum f (Datum t dcode) = Datum t (fdcode f dcode)
   where fdcode   f' (Inr d)    = Inr (fdcode   f' d)
         fdcode   f' (Inl d)    = Inl (fdstruct f' d)
         fdstruct f' (Et df ds) = Et  (fdfun    f' df)
                                      (fdstruct f' ds)
         fdstruct _  Done       = Done
         fdfun    f' (Konst e)  = Konst (f' e)
         fdfun    f' (Ident e)  = Ident (f' e)

foldDatum
    :: (Monoid m)
    => (abt '[] 'U -> m)
    -> Datum abt
    -> m
foldDatum f (Datum _ dcode) = fdcode f dcode
   where fdcode   f' (Inr d)    = fdcode   f' d
         fdcode   f' (Inl d)    = fdstruct f' d
         fdstruct f' (Et df ds) = fdfun    f' df `mappend`
                                  fdstruct f' ds
         fdstruct _  Done       = mempty
         fdfun    f' (Konst e)  = f' e
         fdfun    f' (Ident e)  = f' e


-- | The kind containing exactly one type.
data Untyped = U
    deriving (Read, Show)

deriving instance Typeable 'U

data instance Sing (a :: Untyped) where
    SU :: Sing 'U

instance SingI 'U where
    sing = SU

instance Show (Sing (a :: Untyped)) where
    showsPrec = showsPrec1
    show      = show1

instance Show1 (Sing :: Untyped -> *) where
    showsPrec1 _ SU = ("SU" ++)

instance Eq (Sing (a :: Untyped)) where
    SU == SU = True

instance Eq1 (Sing :: Untyped -> *) where
    eq1 SU SU = True

instance JmEq1 (Sing :: Untyped -> *) where
    jmEq1 SU SU = Just Refl

nameToVar :: Name -> Variable 'U
nameToVar (Name i h) = Variable h i SU

data Term :: ([Untyped] -> Untyped -> *) -> Untyped -> * where
    Lam_       :: SSing            -> abt '[ 'U ] 'U  -> Term abt 'U
    App_       :: abt '[] 'U       -> abt '[]     'U  -> Term abt 'U
    Let_       :: abt '[] 'U       -> abt '[ 'U ] 'U  -> Term abt 'U
    Ann_       :: SSing            -> abt '[]     'U  -> Term abt 'U
    CoerceTo_  :: Some2 Coercion   -> abt '[]     'U  -> Term abt 'U
    UnsafeTo_  :: Some2 Coercion   -> abt '[]     'U  -> Term abt 'U
    PrimOp_    :: PrimOp           -> [abt '[] 'U]    -> Term abt 'U
    ArrayOp_   :: ArrayOp          -> [abt '[] 'U]    -> Term abt 'U
    MeasureOp_ :: SomeOp MeasureOp -> [abt '[] 'U]    -> Term abt 'U
    NaryOp_    :: NaryOp           -> [abt '[] 'U]    -> Term abt 'U
    Literal_   :: Some1 Literal                       -> Term abt 'U
    Empty_     ::                                        Term abt 'U
    Pair_      :: abt '[] 'U       -> abt '[]     'U  -> Term abt 'U
    Array_     :: abt '[] 'U       -> abt '[ 'U ] 'U  -> Term abt 'U
    Datum_     :: Datum abt                           -> Term abt 'U
    Case_      :: abt '[] 'U       -> [Branch_ abt]   -> Term abt 'U
    Dirac_     :: abt '[] 'U                          -> Term abt 'U
    MBind_     :: abt '[] 'U       -> abt '[ 'U ] 'U  -> Term abt 'U
    Plate_     :: abt '[] 'U       -> abt '[ 'U ] 'U  -> Term abt 'U
    Chain_     :: abt '[] 'U       -> abt '[]     'U  -> abt '[ 'U ] 'U -> Term abt 'U
    Integrate_ :: abt '[] 'U       -> abt '[]     'U  -> abt '[ 'U ] 'U -> Term abt 'U
    Summate_   :: abt '[] 'U       -> abt '[]     'U  -> abt '[ 'U ] 'U -> Term abt 'U
    Product_   :: abt '[] 'U       -> abt '[]     'U  -> abt '[ 'U ] 'U -> Term abt 'U
    Expect_    :: abt '[] 'U       -> abt '[ 'U ] 'U  -> Term abt 'U
    Observe_   :: abt '[] 'U       -> abt '[]     'U  -> Term abt 'U
    Superpose_ :: L.NonEmpty (abt '[] 'U, abt '[] 'U) -> Term abt 'U
    Reject_    ::                                        Term abt 'U


-- TODO: instance of Traversable21 for Term
instance Functor21 Term where
    fmap21 f (Lam_       typ e1)    = Lam_       typ    (f e1)
    fmap21 f (App_       e1  e2)    = App_       (f e1) (f e2)
    fmap21 f (Let_       e1  e2)    = Let_       (f e1) (f e2)
    fmap21 f (Ann_       typ e1)    = Ann_       typ    (f e1)
    fmap21 f (CoerceTo_  c   e1)    = CoerceTo_  c      (f e1)
    fmap21 f (UnsafeTo_  c   e1)    = UnsafeTo_  c      (f e1)
    fmap21 f (PrimOp_    op  es)    = PrimOp_    op     (fmap f es)
    fmap21 f (ArrayOp_   op  es)    = ArrayOp_   op     (fmap f es)
    fmap21 f (MeasureOp_ op  es)    = MeasureOp_ op     (fmap f es)
    fmap21 f (NaryOp_    op  es)    = NaryOp_    op     (fmap f es)
    fmap21 _ (Literal_   v)         = Literal_   v
    fmap21 _ Empty_                 = Empty_
    fmap21 f (Pair_      e1  e2)    = Pair_      (f e1) (f e2)
    fmap21 f (Array_     e1  e2)    = Array_     (f e1) (f e2)
    fmap21 f (Datum_     d)         = Datum_     (fmapDatum f d)
    fmap21 f (Case_      e1  bs)    = Case_      (f e1) (fmap (fmapBranch f) bs)
    fmap21 f (Dirac_     e1)        = Dirac_     (f e1)
    fmap21 f (MBind_     e1  e2)    = MBind_     (f e1) (f e2)
    fmap21 f (Plate_     e1  e2)    = Plate_     (f e1) (f e2)
    fmap21 f (Chain_     e1  e2 e3) = Chain_     (f e1) (f e2) (f e3)
    fmap21 f (Integrate_ e1  e2 e3) = Integrate_ (f e1) (f e2) (f e3)
    fmap21 f (Summate_   e1  e2 e3) = Summate_   (f e1) (f e2) (f e3)
    fmap21 f (Product_   e1  e2 e3) = Product_   (f e1) (f e2) (f e3)
    fmap21 f (Expect_    e1  e2)    = Expect_    (f e1) (f e2)
    fmap21 f (Observe_   e1  e2)    = Observe_   (f e1) (f e2)
    fmap21 f (Superpose_ es)        = Superpose_ (L.map (f *** f) es)
    fmap21 _ Reject_                = Reject_

instance Foldable21 Term where
    foldMap21 f (Lam_       _  e1)    = f e1
    foldMap21 f (App_       e1 e2)    = f e1 `mappend` f e2
    foldMap21 f (Let_       e1 e2)    = f e1 `mappend` f e2
    foldMap21 f (Ann_       _  e1)    = f e1
    foldMap21 f (CoerceTo_  _  e1)    = f e1
    foldMap21 f (UnsafeTo_  _  e1)    = f e1
    foldMap21 f (PrimOp_    _  es)    = F.foldMap f es
    foldMap21 f (ArrayOp_   _  es)    = F.foldMap f es
    foldMap21 f (MeasureOp_ _  es)    = F.foldMap f es
    foldMap21 f (NaryOp_    _  es)    = F.foldMap f es
    foldMap21 _ (Literal_   _)        = mempty
    foldMap21 _ Empty_                = mempty
    foldMap21 f (Pair_      e1 e2)    = f e1 `mappend` f e2
    foldMap21 f (Array_     e1 e2)    = f e1 `mappend` f e2
    foldMap21 f (Datum_     d)        = foldDatum f d
    foldMap21 f (Case_      e1 bs)    = f e1 `mappend` F.foldMap (foldBranch f) bs
    foldMap21 f (Dirac_     e1)       = f e1
    foldMap21 f (MBind_     e1 e2)    = f e1 `mappend` f e2
    foldMap21 f (Plate_     e1 e2)    = f e1 `mappend` f e2
    foldMap21 f (Chain_     e1 e2 e3) = f e1 `mappend` f e2 `mappend` f e3
    foldMap21 f (Integrate_ e1 e2 e3) = f e1 `mappend` f e2 `mappend` f e3
    foldMap21 f (Summate_   e1 e2 e3) = f e1 `mappend` f e2 `mappend` f e3
    foldMap21 f (Product_   e1 e2 e3) = f e1 `mappend` f e2 `mappend` f e3
    foldMap21 f (Expect_    e1 e2)    = f e1 `mappend` f e2
    foldMap21 f (Observe_   e1 e2)    = f e1 `mappend` f e2
    foldMap21 f (Superpose_ es)       = F.foldMap (\(e1,e2) -> f e1 `mappend` f e2) es
    foldMap21 _ Reject_               = mempty

type AST      = MetaABT SourceSpan Term '[] 'U
type MetaTerm = Term (MetaABT SourceSpan Term) 'U
type Branch   = Branch_ (MetaABT SourceSpan Term)

type DFun_    = DFun    (MetaABT SourceSpan Term)
type DStruct_ = DStruct (MetaABT SourceSpan Term)
type DCode_   = DCode   (MetaABT SourceSpan Term)

----------------------------------------------------------------
---------------------------------------------------------- fin.
