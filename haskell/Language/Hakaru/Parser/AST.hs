 {-# LANGUAGE CPP
           , GADTs
           , DataKinds
           , PolyKinds
           , ExistentialQuantification
           , StandaloneDeriving
           , TypeFamilies
           , TypeOperators
           , OverloadedStrings
           , DeriveDataTypeable
           , ScopedTypeVariables
           , RankNTypes
           , FlexibleContexts
           , LambdaCase
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}

module Language.Hakaru.Parser.AST where

import           Prelude       hiding (replicate, unlines)
import           Control.Arrow ((***))

import qualified Data.Foldable       as F
import qualified Data.Vector         as V
import qualified Data.Number.Nat     as N
import qualified Data.Number.Natural as N
import qualified Data.List.NonEmpty  as L

import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Syntax.ABT    hiding (Var, Bind)
import Language.Hakaru.Syntax.AST
    (Literal(..), MeasureOp(..), LCs(), UnLCs ())
import qualified Language.Hakaru.Syntax.AST as T
import Language.Hakaru.Syntax.IClasses

#if __GLASGOW_HASKELL__ < 710
import Data.Monoid   (Monoid(..))
#endif

import qualified Data.Text as T
import Text.Parsec (SourcePos)
import Text.Parsec.Pos
import Data.Generics hiding ((:~:)(..))

-- N.B., because we're not using the ABT's trick for implementing a HOAS API, we can make the identifier strict.
data Name = Name {-# UNPACK #-}!N.Nat {-# UNPACK #-}!T.Text
    deriving (Read, Show, Eq, Ord, Data, Typeable)

nameID :: Name -> N.Nat
nameID (Name i _) = i

hintID :: Name -> T.Text
hintID (Name _ t) = t

----------------------------------------------------------------
----------------------------------------------------------------

type Name' = T.Text

data Branch' a
    = Branch'  (Pattern' Name') (AST' a)
    | Branch'' (Pattern' Name)  (AST' a)
    deriving (Eq, Show, Data, Typeable)

data Pattern' a
    = PVar'  a
    | PWild'
    | PData' (PDatum a)
    deriving (Eq, Show, Data, Typeable)

data PDatum a = DV Name' [Pattern' a]
    deriving (Eq, Show, Data, Typeable)

-- Meta stores start and end position for AST in source code
data SourceSpan = SourceSpan !SourcePos !SourcePos
    deriving (Eq, Show, Data, Typeable)

printSourceSpan :: SourceSpan -> V.Vector T.Text -> T.Text
printSourceSpan (SourceSpan start stop) input
  = T.unlines (concatMap line [startLine..stopLine])
  where
  line :: Int -> [T.Text]
  line i | (sourceLine start, sourceColumn start) <= (i, 1) &&
           (i, eol) <= (sourceLine stop, sourceColumn stop)
         = [T.empty | i == startLine] ++
           [quote '>'] ++
           [T.empty | i == stopLine]
         | i == stopLine
         = [T.empty | i == startLine] ++
           [quote ' ',
            marking (if i == sourceLine start then sourceColumn start else 1)
                    (if i == sourceLine stop  then sourceColumn stop  else eol)
                    '^']
         | i == sourceLine start
         = [marking (sourceColumn start) eol '.',
            quote ' ']
         | otherwise
         = [quote ' ']
    where numbering = T.pack (show i)
          lining    = input V.! (i-1)
          eol       = T.length lining + 1
          quote c   = spacing (digits - T.length numbering)
                      `T.append` numbering
                      `T.append` T.singleton '|'
                      `T.append` T.singleton c
                      `T.append` lining
  spacing k     = T.replicate k (T.singleton ' ')
  marking l r c = spacing (digits + 1 + l)
                  `T.append` T.replicate (max 1 (r - l)) (T.singleton c)
  startLine     = max 1
                $ sourceLine start
  stopLine      = max startLine
                $ min (V.length input)
                $ (if sourceColumn stop == 1 then pred else id)
                $ sourceLine stop
  digits        = loop stopLine 1
    where loop i res | i < 10    = res
                     | otherwise = (loop $! div i 10) $! (res + 1)

data Literal'
    = Nat  Integer
    | Int  Integer
    | Prob Rational
    | Real Rational
    deriving (Eq, Show, Data, Typeable)

data NaryOp
    = And | Or   | Xor
    | Iff | Min  | Max
    | Sum | Prod
    deriving (Eq, Show, Data, Typeable)

data ArrayOp = Index_ | Size | Reduce deriving (Data, Typeable)

data TypeAST'
    = TypeVar Name'
    | TypeApp Name'    [TypeAST']
    | TypeFun TypeAST' TypeAST'
    deriving (Eq, Show, Data, Typeable)

data Reducer' a
    = R_Fanout (Reducer' a) (Reducer' a)
    | R_Index a (AST' a) (AST' a) (Reducer' a)
    | R_Split (AST' a) (Reducer' a) (Reducer' a)
    | R_Nop
    | R_Add (AST' a)
    deriving (Eq, Show, Data, Typeable)

data Transform'
    = Observe
    | MH
    | MCMC
    | Disint T.TransformImpl
    | Summarize
    | Simplify
    | Reparam
    | Expect
    deriving (Eq, Show, Data, Typeable)

trFromTyped :: T.Transform as x -> Transform'
trFromTyped = \case
  T.Observe   -> Observe
  T.MH        -> MH
  T.MCMC      -> MCMC
  T.Disint k  -> Disint k
  T.Summarize -> Summarize
  T.Simplify  -> Simplify
  T.Reparam   -> Reparam
  T.Expect    -> Expect

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
    | Pair (AST' a) (AST' a)
    | Array a (AST' a) (AST' a)
    | ArrayLiteral [AST' a]
    | Index (AST' a) (AST' a)
    | Case  (AST' a) [(Branch' a)] -- match
    | Bind  a  (AST' a) (AST' a)
    | Plate a  (AST' a) (AST' a)
    | Chain a  (AST' a) (AST' a) (AST' a)
    | Integrate a (AST' a) (AST' a) (AST' a)
    | Summate   a (AST' a) (AST' a) (AST' a)
    | Product   a (AST' a) (AST' a) (AST' a)
    | Bucket    a (AST' a) (AST' a) (Reducer' a)
    | Transform Transform' (SArgs' a)
    | Msum  [AST' a]
    | Data  a [a] [TypeAST'] (AST' a)
    | WithMeta (AST' a) SourceSpan
    deriving (Show, Data, Typeable)

newtype SArgs' a = SArgs' [ ([a], AST' a) ]
    deriving (Eq, Show, Data, Typeable)

-- For backwards compatibility
_Expect :: a -> AST' a -> AST' a -> AST' a
_Expect v a b = Transform Expect $ SArgs' $ [ ([], a), ([v], b) ]

withoutMeta :: AST' a -> AST' a
withoutMeta (WithMeta e _) = withoutMeta e
withoutMeta           e    =             e

withoutMetaE :: forall a . Data a => AST' a -> AST' a
withoutMetaE = everywhere (mkT (withoutMeta :: AST' a -> AST' a))

instance Eq a => Eq (AST' a) where
    (Var t)             == (Var t')                 = t    == t'
    (Lam n  e1 e2)      == (Lam n' e1' e2')         = n    == n'  &&
                                                      e1   == e1' &&
                                                      e2   == e2'
    (App    e1 e2)      == (App    e1' e2')         = e1   == e1' &&
                                                      e2   == e2'
    (Let n  e1 e2)      == (Let n' e1' e2')         = n    == n'  &&
                                                      e1   == e1' &&
                                                      e2   == e2'
    (If  c  e1 e2)      == (If  c' e1' e2')         = c    == c'  &&
                                                      e1   == e1' &&
                                                      e2   == e2'
    (Ann e typ)         == (Ann e' typ')            = e    == e'  &&
                                                      typ  == typ'
    Infinity'           == Infinity'                = True
    (ULiteral v)        == (ULiteral v')            = v    == v'
    (NaryOp op args)    == (NaryOp op' args')       = op   == op' &&
                                                      args == args'
    Unit                == Unit                     = True
    (Pair  e1 e2)       == (Pair   e1' e2')         = e1   == e1' &&
                                                      e2   == e2'
    (Array e1 e2 e3)    == (Array  e1' e2' e3')     = e1   == e1' &&
                                                      e2   == e2' &&
                                                      e3   == e3'
    (ArrayLiteral es)   == (ArrayLiteral es')       = es   == es'
    (Index e1 e2)       == (Index  e1' e2')         = e1   == e1' &&
                                                      e2   == e2'
    (Case  e1 bs)       == (Case   e1' bs')         = e1   == e1' &&
                                                      bs   == bs'
    (Bind  e1 e2 e3)    == (Bind   e1' e2' e3')     = e1   == e1' &&
                                                      e2   == e2' &&
                                                      e3   == e3'
    (Plate e1 e2 e3)    == (Plate  e1' e2' e3')     = e1   == e1' &&
                                                      e2   == e2' &&
                                                      e3   == e3'
    (Chain e1 e2 e3 e4) == (Chain  e1' e2' e3' e4') = e1   == e1' &&
                                                      e2   == e2' &&
                                                      e3   == e3' &&
                                                      e4   == e4'
    (Integrate a b c d) == (Integrate  a' b' c' d') = a    == a' &&
                                                      b    == b' &&
                                                      c    == c' &&
                                                      d    == d'
    (Summate   a b c d) == (Summate    a' b' c' d') = a    == a' &&
                                                      b    == b' &&
                                                      c    == c' &&
                                                      d    == d'
    (Product   a b c d) == (Product    a' b' c' d') = a    == a' &&
                                                      b    == b' &&
                                                      c    == c' &&
                                                      d    == d'
    (Bucket    a b c d) == (Bucket     a' b' c' d') = a    == a' &&
                                                      b    == b' &&
                                                      c    == c' &&
                                                      d    == d'
    (Transform t0 es0)  == (Transform t1 es1)       = t0   == t1 &&
                                                      es0  == es1
    (Msum  es)          == (Msum   es')             = es   == es'
    (Data  n ft ts e)   == (Data   n' ft' ts' e')   = n    == n'  &&
                                                      ft   == ft' &&
                                                      ts   == ts' &&
                                                      e    == e'
    (WithMeta e1 _ )    == e2                       = e1   == e2
    e1                  == (WithMeta e2 _)          = e1   == e2
    _                   == _                        = False

data Import a = Import a
     deriving (Eq, Show)
data ASTWithImport' a = ASTWithImport' [Import a] (AST' a)
     deriving (Eq, Show)

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
    | RealPow    | Choose | NatPow
    | Exp        | Log    | Infinity
    | GammaFunc  | BetaFunc
    | Equal      | Less
    | Negate     | Recip
    | Abs        | Signum | NatRoot | Erf
    | Floor
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
    | PDatum T.Text PCode

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

data Datum abt = Datum T.Text (DCode abt)

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


data Reducer (xs  :: [Untyped])
             (abt :: [Untyped] -> Untyped -> *)
             (a   :: Untyped) where
    R_Fanout_ :: Reducer xs abt 'U
              -> Reducer xs abt 'U
              -> Reducer xs abt 'U
    R_Index_  :: Variable 'U -- HACK: Shouldn't need to pass this argument
              -> abt xs 'U
              -> abt ( 'U ': xs) 'U
              -> Reducer ( 'U ': xs) abt 'U
              -> Reducer xs abt 'U
    R_Split_  :: abt ( 'U ': xs) 'U
              -> Reducer xs abt 'U
              -> Reducer xs abt 'U
              -> Reducer xs abt 'U
    R_Nop_    :: Reducer xs abt 'U
    R_Add_    :: abt ( 'U ': xs) 'U
              -> Reducer xs abt 'U

instance Functor21 (Reducer xs) where
    fmap21 f (R_Fanout_ r1 r2)       = R_Fanout_ (fmap21 f r1) (fmap21 f r2)
    fmap21 f (R_Index_  bv e1 e2 r1) = R_Index_ bv (f e1) (f e2) (fmap21 f r1)
    fmap21 f (R_Split_  e1 r1 r2)    = R_Split_ (f e1) (fmap21 f r1) (fmap21 f r2)
    fmap21 _ R_Nop_                  = R_Nop_
    fmap21 f (R_Add_    e1)          = R_Add_ (f e1)

instance Foldable21 (Reducer xs) where
    foldMap21 f (R_Fanout_ r1 r2)       = foldMap21 f r1 `mappend` foldMap21 f r2
    foldMap21 f (R_Index_  _  e1 e2 r1) =
        f e1 `mappend` f e2 `mappend` foldMap21 f r1
    foldMap21 f (R_Split_  e1 r1 r2)    =
        f e1 `mappend` foldMap21 f r1 `mappend` foldMap21 f r2
    foldMap21 _ R_Nop_                  = mempty
    foldMap21 f (R_Add_    e1)          = f e1

-- | The kind containing exactly one type.
data Untyped = U
    deriving (Read, Show)

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
    Lam_          :: SSing            -> abt '[ 'U ] 'U  -> Term abt 'U
    App_          :: abt '[] 'U       -> abt '[]     'U  -> Term abt 'U
    Let_          :: abt '[] 'U       -> abt '[ 'U ] 'U  -> Term abt 'U
    Ann_          :: SSing            -> abt '[]     'U  -> Term abt 'U
    CoerceTo_     :: Some2 Coercion   -> abt '[]     'U  -> Term abt 'U
    UnsafeTo_     :: Some2 Coercion   -> abt '[]     'U  -> Term abt 'U
    PrimOp_       :: PrimOp           -> [abt '[] 'U]    -> Term abt 'U
    ArrayOp_      :: ArrayOp          -> [abt '[] 'U]    -> Term abt 'U
    MeasureOp_    :: SomeOp MeasureOp -> [abt '[] 'U]    -> Term abt 'U
    NaryOp_       :: NaryOp           -> [abt '[] 'U]    -> Term abt 'U
    Literal_      :: Some1 Literal                       -> Term abt 'U
    Pair_         :: abt '[] 'U       -> abt '[]     'U  -> Term abt 'U
    Array_        :: abt '[] 'U       -> abt '[ 'U ] 'U  -> Term abt 'U
    ArrayLiteral_ :: [abt '[] 'U]                        -> Term abt 'U
    Datum_        :: Datum abt                           -> Term abt 'U
    Case_         :: abt '[] 'U       -> [Branch_ abt]   -> Term abt 'U
    Dirac_        :: abt '[] 'U                          -> Term abt 'U
    MBind_        :: abt '[] 'U       -> abt '[ 'U ] 'U  -> Term abt 'U
    Plate_        :: abt '[] 'U       -> abt '[ 'U ] 'U  -> Term abt 'U
    Chain_        :: abt '[] 'U       -> abt '[]     'U  -> abt '[ 'U ] 'U -> Term abt 'U
    Integrate_    :: abt '[] 'U       -> abt '[]     'U  -> abt '[ 'U ] 'U -> Term abt 'U
    Summate_      :: abt '[] 'U       -> abt '[]     'U  -> abt '[ 'U ] 'U -> Term abt 'U
    Product_      :: abt '[] 'U       -> abt '[]     'U  -> abt '[ 'U ] 'U -> Term abt 'U
    Bucket_       :: abt '[] 'U       -> abt '[]     'U  -> Reducer xs abt 'U -> Term abt 'U
    Transform_    :: T.Transform as x -> SArgs abt as    -> Term abt 'U
    Superpose_    :: L.NonEmpty (abt '[] 'U, abt '[] 'U) -> Term abt 'U
    Reject_       ::                                        Term abt 'U
    InjTyped      :: (forall abt . ABT T.Term abt
                                 => abt '[] x)           -> Term abt 'U

infixr 5 :*
data SArgs (abt :: [Untyped] -> Untyped -> *) (as :: [([k], k)]) where
  End :: SArgs abt '[]
  (:*) :: !(List2 ToUntyped vars varsu, abt varsu 'U)
       -> !(SArgs abt args)
       -> SArgs abt ( '(vars, a) ': args)

data ToUntyped (x :: k) (y :: Untyped) where
  ToU :: ToUntyped x 'U

instance Functor21 SArgs where
    fmap21 f = \case
      End          -> End
      (m, a) :* as -> (m, f a) :* fmap21 f as

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
    fmap21 f (Pair_      e1  e2)    = Pair_      (f e1) (f e2)
    fmap21 f (Array_     e1  e2)    = Array_     (f e1) (f e2)
    fmap21 f (ArrayLiteral_  es)    = ArrayLiteral_     (fmap f es)
    fmap21 f (Datum_     d)         = Datum_     (fmapDatum f d)
    fmap21 f (Case_      e1  bs)    = Case_      (f e1) (fmap (fmapBranch f) bs)
    fmap21 f (Dirac_     e1)        = Dirac_     (f e1)
    fmap21 f (MBind_     e1  e2)    = MBind_     (f e1) (f e2)
    fmap21 f (Plate_     e1  e2)    = Plate_     (f e1) (f e2)
    fmap21 f (Chain_     e1  e2 e3) = Chain_     (f e1) (f e2) (f e3)
    fmap21 f (Integrate_ e1  e2 e3) = Integrate_ (f e1) (f e2) (f e3)
    fmap21 f (Summate_   e1  e2 e3) = Summate_   (f e1) (f e2) (f e3)
    fmap21 f (Product_   e1  e2 e3) = Product_   (f e1) (f e2) (f e3)
    fmap21 f (Bucket_    e1  e2 e3) = Bucket_    (f e1) (f e2) (fmap21 f e3)
    fmap21 f (Transform_ t as)      = Transform_ t (fmap21 f as)
    fmap21 f (Superpose_ es)        = Superpose_ (L.map (f *** f) es)
    fmap21 _ Reject_                = Reject_
    fmap21 _ (InjTyped x)           = InjTyped x

instance Foldable21 SArgs where
    foldMap21 f = \case
      End          -> mempty
      (_, a) :* as -> f a `mappend` foldMap21 f as

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
    foldMap21 f (Pair_      e1 e2)    = f e1 `mappend` f e2
    foldMap21 f (Array_     e1 e2)    = f e1 `mappend` f e2
    foldMap21 f (ArrayLiteral_ es)    = F.foldMap f es
    foldMap21 f (Datum_     d)        = foldDatum f d
    foldMap21 f (Case_      e1 bs)    = f e1 `mappend` F.foldMap (foldBranch f) bs
    foldMap21 f (Dirac_     e1)       = f e1
    foldMap21 f (MBind_     e1 e2)    = f e1 `mappend` f e2
    foldMap21 f (Plate_     e1 e2)    = f e1 `mappend` f e2
    foldMap21 f (Chain_     e1 e2 e3) = f e1 `mappend` f e2 `mappend` f e3
    foldMap21 f (Integrate_ e1 e2 e3) = f e1 `mappend` f e2 `mappend` f e3
    foldMap21 f (Summate_   e1 e2 e3) = f e1 `mappend` f e2 `mappend` f e3
    foldMap21 f (Product_   e1 e2 e3) = f e1 `mappend` f e2 `mappend` f e3
    foldMap21 f (Bucket_    e1 e2 e3) = f e1 `mappend` f e2 `mappend` foldMap21 f e3
    foldMap21 f (Transform_ _ es)     = foldMap21 f es
    foldMap21 f (Superpose_ es)       = F.foldMap (\(e1,e2) -> f e1 `mappend` f e2) es
    foldMap21 _ Reject_               = mempty
    foldMap21 _ InjTyped{}            = mempty

type U_ABT    = MetaABT SourceSpan Term
type AST      = U_ABT '[] 'U
type MetaTerm = Term U_ABT 'U
type Branch   = Branch_ U_ABT

type DFun_    = DFun    U_ABT
type DStruct_ = DStruct U_ABT
type DCode_   = DCode   U_ABT

----------------------------------------------------------------
---------------------------------------------------------- fin.
