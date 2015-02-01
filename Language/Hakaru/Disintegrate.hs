{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances,
             RankNTypes, GADTs, StandaloneDeriving #-}
{-# OPTIONS -Wall -fno-warn-incomplete-patterns #-}

module Language.Hakaru.Disintegrate (Disintegrate, Disintegration(..),
       runDisintegrate, disintegrations, condition, density, resetDisint,
       Eq'(..), eq'List, Ord'(..), ord'List, Show'(..), Tree(..), Selector(..),
       Op0(..), Op1(..), Op2(..), Expr(..), Name, Loc, Void,
       if', max_, stdRandom, run, disintegrate, emptyEnv) where

import Prelude hiding (mapM, lookup, (!!), Real)
import Data.Either (partitionEithers)
import Data.Maybe (isJust, fromMaybe)
import Data.Monoid (Monoid (mempty, mappend, mconcat))
import Data.Graph (graphFromEdges, topSort)
import Data.List (tails)
import qualified Data.Set as S
import Control.Applicative (Applicative(pure, (<*>)), Const(Const),
        WrappedMonad(WrapMonad, unwrapMonad))
import Control.Monad.Trans.RWS (runRWS, get, put, tell)
import Control.Monad (mapM, liftM2)
import Control.Monad.Trans.Cont (Cont, cont, runCont)
import Language.Hakaru.Util.Pretty (Pretty (pretty),
        prettyPair, prettyParen, prettyFun, prettyOp)
import Text.PrettyPrint (Doc, text, char, int, integer, comma, semi, brackets,
        parens, (<>), (<+>), nest, fsep, sep, punctuate, render)
import Language.Hakaru.Syntax (Real, Prob, Measure,
        EqType(Refl), Order_(..), Number(..),
        Fraction(fractionCase, fractionRepr),
        Order(..), Base(..), Mochastic(..), factor, liftM,
        Lambda(..), Integrate(..))
import Language.Hakaru.Expect (Expect(Expect), Expect', total)
import Unsafe.Coerce (unsafeCoerce)
import Data.Ratio (numerator, denominator)

------- Tracing

--import Debug.Trace (traceShow)
traceShow :: (Show a) => a -> b -> b
traceShow _ = id

------- Lift common type-classes from kind * to kind "HakaruType -> *"
-- Variables are typed in environments, and locations are typed in heaps.

class Eq' a where
  eq' :: a t -> a t -> Bool

eq'List :: (Eq' a) => [a t] -> [a t] -> Bool
eq'List []     []     = True
eq'List (x:xs) (y:ys) = eq' x y && eq'List xs ys
eq'List []     (_:_)  = False
eq'List (_:_)  []     = False

class (Eq' a) => Ord' a where
  ord' :: a t -> a t -> Ordering

ord'List :: (Ord' a) => [a t] -> [a t] -> Ordering
ord'List []     []     = EQ
ord'List (x:xs) (y:ys) = ord' x y `mappend` ord'List xs ys
ord'List []     (_:_)  = LT
ord'List (_:_)  []     = GT

class Show' a where
  show'       :: Int -> a t -> ShowS
  show'   p a = showString (render (pretty' p a))
  pretty'     :: Int -> a t -> Doc
  pretty' p a = text (show' p a "")

class Functor' f where
  fmap' :: (forall t. a t -> b t) -> f a t' -> f b t'

class Foldable' f where
  foldMap' :: (Monoid m) => (forall t. a t -> m) -> f a t' -> m

class (Functor' f, Foldable' f) => Traversable' f where
  traverse' :: (Applicative m) =>
               (forall t. a t -> m (b t)) -> f a t' -> m (f b t')
  mapM'     :: (Monad m) =>
               (forall t. a t -> m (b t)) -> f a t' -> m (f b t')
  mapM' f = unwrapMonad . traverse' (WrapMonad . f)

------- Trees, which form the left-hand-sides of bindings

data Tree a t where
  Branch :: Tree a t1 -> Tree a t2 -> Tree a (t1, t2)
  UnaryL :: Tree a t1 -> Tree a (Either t1 t2)
  UnaryR :: Tree a t2 -> Tree a (Either t1 t2)
  LNil   :: Tree a [t]
  LCons  :: Tree a t -> Tree a [t] -> Tree a [t]
  Nil    :: Tree a ()
  BoolT  :: Tree a Bool
  BoolF  :: Tree a Bool
  Leaf   :: a t -> Tree a t

instance (Show' a) => Show' (Tree a) where
  pretty' _ (Branch a b) = prettyPair (pretty' 0 a) (pretty' 0 b)
  pretty' p (UnaryL a)   = prettyFun (p > 10) "L" (pretty' 11 a)
  pretty' p (UnaryR b)   = prettyFun (p > 10) "R" (pretty' 11 b)
  pretty' p (Leaf a)     = pretty' p a
  pretty' _ LNil         = text "[]"
  pretty' p (LCons a as) = prettyFun (p > 10) "LCons" $
                           pretty' 11 a <+> pretty' 11 as
  pretty' _ BoolT        = text "true"
  pretty' _ BoolF        = text "false"
  pretty' _ Nil          = text "()"

instance Functor' Tree where
  fmap' f (Branch a b) = fmap' f a `Branch` fmap' f b
  fmap' f (UnaryL a)   = UnaryL (fmap' f a)
  fmap' f (UnaryR b)   = UnaryR (fmap' f b)
  fmap' _ LNil         = LNil
  fmap' f (LCons a as) = LCons (fmap' f a) (fmap' f as)
  fmap' _ Nil          = Nil
  fmap' _ BoolT        = BoolT
  fmap' _ BoolF        = BoolF
  fmap' f (Leaf a)     = Leaf (f a)

instance Foldable' Tree where
  foldMap' f (Branch a b) = foldMap' f a `mappend` foldMap' f b
  foldMap' f (UnaryL a)   = foldMap' f a
  foldMap' f (UnaryR b)   = foldMap' f b
  foldMap' _ LNil         = mempty
  foldMap' f (LCons a as) = foldMap' f a `mappend` foldMap' f as
  foldMap' _ Nil          = mempty
  foldMap' _ BoolT        = mempty
  foldMap' _ BoolF        = mempty
  foldMap' f (Leaf a)     = f a

instance Traversable' Tree where
  traverse' f (Branch a b) = fmap Branch (traverse' f a) <*> traverse' f b
  traverse' f (UnaryL a)   = fmap UnaryL (traverse' f a)
  traverse' f (UnaryR b)   = fmap UnaryR (traverse' f b)
  traverse' _ LNil         = pure LNil
  traverse' f (LCons a as) = fmap LCons (traverse' f a) <*> traverse' f as
  traverse' _ Nil          = pure Nil
  traverse' _ BoolT        = pure BoolT
  traverse' _ BoolF        = pure BoolF
  traverse' f (Leaf a)     = fmap Leaf (f a)

------- Selectors, which name a part of an algebraic data type to evaluate
-- For example, evaluating at Root is evaluating to whnf.
-- To take another example, disintegrating at Root is calculating density.

data Selector to t where
  Fst  :: Selector to t   -> Selector to (t, t')
  Snd  :: Selector to t   -> Selector to (t', t)
  Car  :: Selector to t   -> Selector to [t]
  Cdr  :: Selector to [t] -> Selector to [t]
  Unl  :: Selector to t   -> Selector to (Either t t')
  Unr  :: Selector to t   -> Selector to (Either t' t)
  Root :: Selector to to

instance Show' (Selector to) where
  pretty' p (Fst s) = prettyFun (p > 10) "Fst" (pretty' 11 s)
  pretty' p (Snd s) = prettyFun (p > 10) "Snd" (pretty' 11 s)
  pretty' p (Car s) = prettyFun (p > 10) "Car" (pretty' 11 s)
  pretty' p (Cdr s) = prettyFun (p > 10) "Cdr" (pretty' 11 s)
  pretty' p (Unl s) = prettyFun (p > 10) "Unl" (pretty' 11 s)
  pretty' p (Unr s) = prettyFun (p > 10) "Unr" (pretty' 11 s)
  pretty' _ Root    = text "Root"

locate :: (Eq a, Show a) =>
          Const a to -> Tree (Const a) t -> Maybe (Selector to t)
locate x (Branch a b) =
  case (locate x a, locate x b) of
  (Just _ , Just _ ) -> error ("Duplicate " ++ case x of Const x' -> show x')
  (Just s , Nothing) -> Just (Fst s)
  (Nothing, Just s ) -> Just (Snd s)
  (Nothing, Nothing) -> Nothing
locate x (UnaryL a) = fmap Unl (locate x a)
locate x (UnaryR a) = fmap Unr (locate x a)
locate _ LNil    = Nothing
locate x (LCons a as) =
  case (locate x a, locate x as) of
  (Just _ , Just _ ) -> error ("Duplicate " ++ case x of Const x' -> show x')
  (Just s , Nothing) -> Just (Car s)
  (Nothing, Just s ) -> Just (Cdr s)
  (Nothing, Nothing) -> Nothing
locate _ Nil        = Nothing
locate _ BoolT      = Nothing
locate _ BoolF      = Nothing
locate x (Leaf a)   = do Refl <- unsafeJmEq x a
                         Just Root

compose :: Selector t2 t3 -> Selector t1 t2 -> Selector t1 t3
compose (Fst s1) s2 = Fst (compose s1 s2)
compose (Snd s1) s2 = Snd (compose s1 s2)
compose (Car s1) s2 = Car (compose s1 s2)
compose (Cdr s1) s2 = Cdr (compose s1 s2)
compose (Unl s1) s2 = Unl (compose s1 s2)
compose (Unr s1) s2 = Unr (compose s1 s2)
compose Root     s2 = s2

------- Names (variables in the input) and locations (variables in the output)

type Name = Const String
type Loc  = Const Int

instance (Eq  a) => Eq'  (Const a) where eq'  (Const x) (Const y) = x == y
instance (Ord a) => Ord' (Const a) where ord' (Const x) (Const y) = compare x y
instance Show' Name where pretty' _ (Const n) = text n
instance Show' Loc  where pretty' _ (Const l) = char '_' <> int l

unsafeJmEq :: (Eq a) => Const a t1 -> Const a t2 -> Maybe (EqType t1 t2)
unsafeJmEq (Const t1) (Const t2) = if t1 == t2 then Just (unsafeCoerce Refl)
                                               else Nothing

-- An empty type constructor to express the invariant that values (expressions
-- produced by evaluation) never use Bind to bind any variables (locations):

data Void t

exFalso :: Void t -> a
exFalso _ = error "quodlibet"

instance Eq'   Void where eq'       = exFalso
instance Ord'  Void where ord'      = exFalso
instance Show' Void where show'   _ = exFalso
                          pretty' _ = exFalso

------- An entry in an environment or heap, containing run-time type information
-- An existential quantifier over a product, similar to Coq's "exists2".

data Binding a b where Binding :: a t -> b t -> Binding a b

instance (Eq a) => Eq (Binding (Const a) (Const ())) where
  Binding (Const x) (Const ()) == Binding (Const y) (Const ()) = x == y

instance (Ord a) => Ord (Binding (Const a) (Const ())) where
  compare (Binding (Const x) (Const ())) (Binding (Const y) (Const ())) =
    compare x y

instance (Show' a, Show' b) => Show (Binding a b) where
  showsPrec p = showsPrec p . pretty

instance (Show' a, Show' b) => Pretty (Binding a b) where
  pretty (Binding a b) = prettyPair (pretty' 0 a) (pretty' 0 b)

------- Environments map names (input variables) to locations (output variables)

type Env = [Binding Name Loc]

emptyEnv :: Env
emptyEnv = []

lookup :: (Eq a) => [Binding (Const a) b] -> Const a t -> Maybe (b t)
lookup [] _ = Nothing
lookup (Binding a b : bindings) a' = case unsafeJmEq a a' of
  Just Refl -> Just b
  Nothing   -> lookup bindings a'

(!!) :: (Eq a, Show' (Const a)) => [Binding (Const a) b] -> Const a t -> b t
env !! n = fromMaybe (error ("Unbound name " ++ show' 0 n "")) (lookup env n)

unique :: (Eq a) => [Binding (Const a) b] -> Bool
unique env = and [ x /= y | Binding (Const x) _ : bs <- tails env
                          , Binding (Const y) _ <- bs ]

------- Mochastic expressions!
-- Boilerplate galore.

data Op0 t where
  Lebesgue         :: Op0 (Measure Real)
  Counting         :: Op0 (Measure Int)
  Pi               :: (Fraction t) => Op0 t
  Infinity         :: Op0 Real
  NegativeInfinity :: Op0 Real
  Unit             :: Op0 ()
  EmptyList        :: Op0 [t]
  True_            :: Op0 Bool
  False_           :: Op0 Bool

data Op1 t1 t where
  Exp        :: (Fraction t) => Op1 Real t
  Log        :: (Fraction t) => Op1 t Real
  Neg        :: (Number   t) => Op1 t t
  Inv        :: (Fraction t) => Op1 t t
  Sin        :: Op1 Real Real
  Cos        :: Op1 Real Real
  Tan        :: Op1 Real Real
  ASin       :: Op1 Real Real
  ACos       :: Op1 Real Real
  ATan       :: Op1 Real Real
  Weight     :: Op1 Prob (Measure ())
  UnsafeProb :: Op1 Real Prob
  FromProb   :: Op1 Prob Real
  FromInt    :: Op1 Int  Real
  GammaFunc  :: Op1 Real Prob
  Erf        :: (Fraction t) => Op1 t t

data Op2 t1 t2 t where
  Add      :: (Number t) => Op2 t t t
  Mul      :: (Number t) => Op2 t t t
  Less     :: (Number t) => Op2 t t Bool
  Equal    :: (Number t) => Op2 t t Bool
  BetaFunc :: Op2 Prob Prob Prob

deriving instance Eq (Op0 t)
deriving instance Eq (Op1 t1 t)
deriving instance Eq (Op2 t1 t2 t)

deriving instance Ord (Op0 t)
deriving instance Ord (Op1 t1 t)
deriving instance Ord (Op2 t1 t2 t)

deriving instance Show (Op0 t)
deriving instance Show (Op1 t1 t)
deriving instance Show (Op2 t1 t2 t)

fixity :: Op2 t1 t2 t -> (Int, String, Ordering)
fixity Add      = (6, "+", LT)
fixity Mul      = (7, "*", LT)
fixity Less     = (4, "<", EQ)
fixity Equal    = (4, "=", EQ)
fixity BetaFunc = (9, "`Beta`", EQ)

data Dict t = Dict
  { unsafeProbFraction :: forall b u. Expr b u t -> Expr b u Prob
  , piFraction         :: forall repr. (Base repr) => repr t
  , expFraction        :: forall repr. (Base repr) => repr Real -> repr t
  , logFraction        :: forall repr. (Base repr) => repr t -> repr Real
  , erfFraction        :: forall repr. (Base repr) => repr t -> repr t }
dict :: (Fraction t) => Dict t
dict = fractionCase (Dict (Op1 UnsafeProb) pi exp log erf)
                    (Dict id pi_ exp_ log_ erf_)

data Expr b u t where -- b = bound variables; u = used variables
  Op0     :: Op0 t ->                                     Expr b u t
  Op1     :: Op1 t1 t -> Expr b u t1 ->                   Expr b u t
  Op2     :: Op2 t1 t2 t -> Expr b u t1 -> Expr b u t2 -> Expr b u t
  Lit     :: (Number t) => Integer ->                     Expr b u t
  Var     :: u t ->                                       Expr b u t
  Choice  :: [Expr b u (Measure t)] ->                    Expr b u (Measure t)
  Bind    :: Tree b t -> Expr b u (Measure t) -> Expr b u (Measure t') ->
                                                          Expr b u (Measure t')
  Dirac   :: Expr b u t ->                                Expr b u (Measure t)
  Pair    :: Expr b u t -> Expr b u t' ->                 Expr b u (t, t')
  Inl     :: Expr b u t ->                                Expr b u (Either t t')
  Inr     :: Expr b u t ->                                Expr b u (Either t' t)
  Cons    :: Expr b u t -> Expr b u [t] ->                Expr b u [t]
  -- The Closure constructor below is for internal use
  -- and should not appear in the final output.
  Closure :: Expr Name Name (Measure t) -> [Binding Name u] ->
                                                          Expr b u (Measure t)

instance (Show' b, Show' u) => Show' (Expr b u) where
  pretty' _ (Op0 o)         = text (show o)
  pretty' p (Op1 o e)       = prettyFun (p > 10) (show o) (pretty' 11 e)
  pretty' p (Op2 o e1 e2)   = let (q, s, a) = fixity o in
    prettyOp (p > q) s (pretty' (if a == LT then q else succ q) e1)
                       (pretty' (if a == GT then q else succ q) e2)
  pretty' _ (Lit x)         = integer x
  pretty' p (Var u)         = pretty' p u
  pretty' _ (Choice es)     =
    brackets (nest 1 (fsep (punctuate comma (map (pretty' 0) es))))
  pretty' p e@(Bind _ _ _)  = prettyParen (p > 10) (sep (loop e))
    where loop (Bind lhs rhs body) = pretty' 0 lhs <+> text "<-" <+>
                                     pretty' 0 rhs <> semi
                                   : loop body
          loop body = [pretty' 0 body]
  pretty' p (Dirac e)       = prettyFun (p > 10) "Dirac" (pretty' 11 e)
  pretty' _ (Pair e1 e2)    = prettyPair (pretty' 0 e1) (pretty' 0 e2)
  pretty' p (Inl e)         = prettyFun (p > 10) "L" (pretty' p e)
  pretty' p (Inr e)         = prettyFun (p > 10) "R" (pretty' p e)
  pretty' p (Cons a as)     = prettyFun (p > 10) "Cons" $
                              pretty' 11 a <+> pretty' 11 as
  pretty' p (Closure e env) = prettyParen (p > 0)
                                (sep [pretty' 0 e, text "@" <+> pretty env])

bimap' :: (forall t. a t -> b t) ->
          (forall t. c t -> d t) ->
          (forall t. Expr Name Name (Measure t) ->
                     [Binding Name d] -> Expr b d (Measure t)) ->
          Expr a c t' -> Expr b d t'
bimap' _ _ _ (Op0 o)         = Op0 o
bimap' f g h (Op1 o e)       = Op1 o (bimap' f g h e)
bimap' f g h (Op2 o e1 e2)   = Op2 o (bimap' f g h e1) (bimap' f g h e2)
bimap' _ _ _ (Lit x)         = Lit x
bimap' _ g _ (Var    u)      = Var    (g u)
bimap' f g h (Choice es)     = Choice (map (bimap' f g h) es)
bimap' f g h (Bind l r e)    = Bind (fmap' f l) (bimap' f g h r)
                                                (bimap' f g h e)
bimap' f g h (Dirac e)       = Dirac (bimap' f g h e)
bimap' f g h (Pair e1 e2)    = Pair  (bimap' f g h e1) (bimap' f g h e2)
bimap' f g h (Cons a as)     = Cons  (bimap' f g h a)  (bimap' f g h as)
bimap' f g h (Inl e)         = Inl   (bimap' f g h e)
bimap' f g h (Inr e)         = Inr   (bimap' f g h e)
bimap' _ g h (Closure e env) = h e [ Binding name (g u)
                                   | Binding name u <- env ]

vars :: (Monoid m) =>
        (forall tb. Tree b tb ->
                    (forall tu. u tu -> m) ->
                    (forall tu. u tu -> m)) ->
        (forall tu. u tu -> m) -> Expr b u t -> m
vars _ _ (Op0 _)             = mempty
vars b f (Op1 _ e)           = vars b f e
vars b f (Op2 _ e1 e2)       = vars b f e1 `mappend` vars b f e2
vars _ _ (Lit _)             = mempty
vars _ f (Var u)             = f u
vars b f (Choice es)         = mconcat (map (vars b f) es)
vars b f (Bind lhs rhs body) = vars b f rhs `mappend` vars b (b lhs f) body
vars b f (Dirac e)           = vars b f e
vars b f (Pair e1 e2)        = vars b f e1 `mappend` vars b f e2
vars b f (Cons a as)         = vars b f a  `mappend` vars b f as
vars b f (Inl e)             = vars b f e
vars b f (Inr e)             = vars b f e
vars _ f (Closure e env)     = vars hideUse (\u -> f (env !! u)) e

hideUse :: (Monoid m) => Tree Name t' ->
           (forall t. Name t -> m) -> (forall t. Name t -> m)
hideUse lhs = \f u -> if S.member (Binding u (Const ())) bs then mempty else f u
  where bs = foldMap' (\u -> S.singleton (Binding u (Const ()))) lhs

instance Foldable' (Expr b) where foldMap' = vars (\_ f -> f)

------- Macros to make expressions more concise to write

stdRandom :: Expr Name Name (Measure Real)
stdRandom = Bind (Leaf u) (Op0 Lebesgue)
                 (condLess 0 (Var u) (condLess (Var u) 1 (Dirac (Var u))))
  where u :: Name Real
        u = Const "u"

condLess :: (Number t) => Expr b u t -> Expr b u t ->
            Expr b u (Measure t') -> Expr b u (Measure t')
condLess e1 e2 = Bind BoolT (Dirac (Op2 Less e1 e2))

weight :: Expr b u Prob -> Expr b u (Measure t) -> Expr b u (Measure t)
weight (Lit 0) = const (Choice []) -- simplification
weight (Lit 1) = id -- simplification
weight e = Bind Nil (Op1 Weight e)

power :: Expr b u Prob -> Expr b u Real -> Expr b u Prob
power p r = Op1 Exp (Op1 Log p * r)

-- TODO: Add pure `case' construct
if' :: Expr b u Bool ->
       Expr b u (Measure t) -> Expr b u (Measure t) -> Expr b u (Measure t)
if' e et ee = Choice [ Bind BoolT (Dirac e) et
                     , Bind BoolF (Dirac e) ee ]

max_ :: (Number t) => Expr b u t -> Expr b u t -> Expr b u (Measure t)
max_ e1 e2 = if' (Op2 Less e1 e2) (Dirac e2) (Dirac e1)

instance (Number t) => Num (Expr b u t) where
  (+)         = Op2 Add
  (*)         = Op2 Mul
  negate      = Op1 Neg
  abs         = error "TODO: Add pure `case' construct"
                -- \x -> if_ (Less 0 x) x (-x)
  signum      = error "TODO: Add pure `case' construct"
                -- \x -> if_ (Less 0 x) 1 (if_ (Less x 0) (-1) 0)
  fromInteger = Lit

instance (Fraction t) => Fractional (Expr b u t) where
  recip          = Op1 Inv
  fromRational x = Lit (numerator x) / Lit (denominator x)

ex :: Expr Void Loc t -> Expr Loc Loc t
ex = bimap' exFalso id Closure

------- The heap binds thunks to trees of locations

data Thunk t where
  Delayed :: Expr Name Name (Measure t) -> Env -> Thunk t
  Forced  :: Expr Void Loc t ->                   Thunk t

instance Show' Thunk where
  pretty' p (Delayed e env) = prettyFun (p > 10) "Delayed" $ parens
                            $ sep [pretty' 0 e, text "@" <+> pretty env]
  pretty' p (Forced e)      = prettyFun (p > 10) "Forced" $ pretty' 11 e

force :: (Expr Name Name (Measure t) -> Env -> a) ->
         (Expr Void Loc           t  -> ()  -> a) ->
         Thunk t -> a
force go _  (Delayed e env) = go e env
force _  go (Forced e)      = go e ()

data Heap = Heap { fresh :: Int, bound :: [Binding (Tree Loc) Thunk] }
  deriving (Show)

instance Pretty Heap where
  pretty h = text "Heap" <+> sep [pretty (fresh h), pretty (bound h)]

------- Monad with nondeterminism (making multiple attempts at disintegration),
------- state (threading the heap along), and continuation (for Bind-insertion)

newtype M a = M { unM :: forall w.
                         (a -> Heap -> [Expr Loc Loc (Measure w)])
                            -> Heap -> [Expr Loc Loc (Measure w)] }

instance Monad M where
  return a = M (\c -> c a)
  m >>= k  = M (\c -> unM m (\a -> unM (k a) c))

instance Functor M where fmap f m = m >>= return . f

instance Monoid (M a) where
  mempty                = M (\_ _ -> [])
  mappend (M m1) (M m2) = M (\c h -> m1 c h ++ m2 c h)
  mconcat ms            = M (\c h -> concatMap (\(M m) -> m c h) ms)

reject :: M a
reject = M (\_ _ -> [Choice []])

insert :: (forall w. Expr Loc Loc (Measure w) -> Expr Loc Loc (Measure w)) ->
          M ()
insert f = M (\c h -> map f' (c () h))
  where f' :: forall w. Expr Loc Loc (Measure w) -> Expr Loc Loc (Measure w)
        f' e@(Choice []) = e -- simplification
        f' e             = f e

gensym :: M (Loc t)
gensym = M (\c h -> c (Const (fresh h)) h{fresh = succ (fresh h)})

------- Overload the evaluation and disintegration of input expressions
------- (Expr Name Name t) and output expressions (Expr Void Loc t)

class (Pretty env, Show' u) => Use env u where
  (!) :: env -> u t -> Loc t
  close :: Expr Name Name (Measure t) -> [Binding Name u] -> env ->
           (Expr Name Name (Measure t), Env)

instance Use Env Name where
  (!) = (!!)
  close e env = (,) (rename env (\lhs rhs -> Bind lhs (Dirac rhs) e)) where
    rename :: [Binding Name Name] ->
              (forall t. Tree Name t -> Expr Name Name t -> w) -> w
    rename [] k = k Nil (Op0 Unit)
    rename (Binding a b : bindings) k =
      rename bindings (\lhs rhs -> k (Branch (Leaf a) lhs) (Pair (Var b) rhs))

instance Use () Loc where
  _ ! l = l
  close e env () = (e, env)

class (Use env u, Show' b) => Delay env b u where
  delay    :: Expr b u t -> env -> M (Expr Void Loc t)
  allocate :: Tree b t -> Expr b u (Measure t) -> env -> M env
  measure  :: Expr b u (Measure t) -> env -> Expr Void Loc (Measure t)

instance Delay Env Name Name where
  delay e env = M (\c h ->
    let l = Const (fresh h)
    in c (Var l)
         h{fresh = succ (fresh h),
           bound = Binding (Leaf l) (Delayed (Dirac e) env) : bound h})
  allocate lhs rhs env = M (\c h ->
    let step b = do loc <- get
                    put (succ loc)
                    tell [Binding b (Const loc)]
                    return (Const loc)
        (lhs', fresh', bindings) = runRWS (mapM' step lhs) () (fresh h)
        env' | unique bindings = bindings ++ env
             | otherwise = error ("Duplicate variable in " ++ show bindings)
    in c env'
         h{fresh = fresh',
           bound = Binding lhs' (Delayed rhs env) : bound h})
  measure = Closure

instance Delay () Void Loc where
  delay e () = return e
  allocate lhs rhs () = insert (Bind (fmap' exFalso lhs) (ex rhs)) >> return ()
  measure e () = e

------- Retrieving thunks from, and storing results in, the heap

data Retrieval to where
  Retrieval :: Selector to t -> Tree Loc t -> Thunk t -> Retrieval to

retrieve :: Loc to -> M (Maybe (Retrieval to))
retrieve loc = M (\c h ->
  case partitionEithers [ case locate loc lhs of
                                 Just s  -> Right (Retrieval s lhs thunk)
                                 Nothing -> Left entry
                        | entry@(Binding lhs thunk) <- bound h ] of
    (_   , []   ) -> c Nothing h
    (left, [r]  ) -> c (Just r) h{bound=left}
    (_   , _:_:_) -> error ("Duplicate heap entry " ++ show' 0 loc ""))

store :: Tree Loc t -> Expr Void Loc t -> M ()
store (Branch t1 t2) (Pair e1 e2)    = store t1 e1 >> store t2 e2
store (UnaryL t)     (Inl e)         = store t e
store (UnaryL _)     (Inr _)         = reject
store (UnaryR t)     (Inr e)         = store t e
store (UnaryR _)     (Inl _)         = reject
store Nil            (Op0 Unit)      = return ()
store LNil           (Op0 EmptyList) = return ()
store LNil           (Cons _ _)      = reject
store (LCons a as)   (Cons e es)     = store a e >> store as es
store (LCons _ _)    (Op0 EmptyList) = reject
store lhs            rhs             =
  M (\c h -> c () h{bound = Binding lhs (Forced rhs) : bound h})

value :: Loc t -> M (Expr Void Loc t)
value l = M (\c h ->
  let err = error ("Location " ++ show' 0 l " unexpectedly not bound alone") in
  case [ entry | entry@(Binding lhs _) <- bound h, isJust (locate l lhs) ] of
    [Binding (Leaf l') (Forced rhs)] ->
      case unsafeJmEq l l' of Just Refl -> c rhs h
                              _ -> err
    _ -> err)

------- Main evaluator

determine :: (Delay env b u) => Expr b u (Measure t) ->
             env -> Selector to t -> M (Expr Void Loc t)
determine e env s
  | traceShow (prettyFun False "determine"
                (sep [pretty' 11 e, pretty env, pretty' 11 s]))
              False = undefined
determine (Op0 Lebesgue) _ Root = do
  l <- gensym
  insert (Bind (Leaf l) (Op0 Lebesgue))
  return (Var l)
determine (Op0 Counting) _ Root = do
  l <- gensym
  insert (Bind (Leaf l) (Op0 Counting))
  return (Var l)
determine (Op1 Weight e) env Root = do
  x <- evaluate e env Root
  insert (weight (ex x))
  return (Op0 Unit)
determine e@(Var _) env s = do
  v <- evaluate e env Root
  case v of Var l -> do l' <- gensym
                        insert (Bind (Leaf l') (Var l))
                        return (Var l')
            _ -> determine v () s
determine (Choice es) env s =
  M (\c h -> fmap Choice (mapM (\e -> unM (determine e env s) c h) es))
determine (Bind lhs rhs body) env s = do
  env' <- allocate lhs rhs env
  determine body env' s
determine (Dirac e) env s = evaluate e env s
determine (Closure e' env') env s = uncurry determine (close e' env' env) s

evaluate :: (Delay env b u) => Expr b u t ->
            env -> Selector to t -> M (Expr Void Loc t)
evaluate e env s
  | traceShow (prettyFun False "evaluate"
                (sep [pretty' 11 e, pretty env, pretty' 11 s]))
              False = undefined
evaluate (Op0 o)       _   _ = return (Op0 o)
evaluate e@(Op1 Weight _) env Root = return (measure e env)
evaluate (Op1 o e)     env _ = fmap   (Op1 o) (evaluate e  env Root)
evaluate (Op2 o e1 e2) env _ = liftM2 (Op2 o) (evaluate e1 env Root)
                                              (evaluate e2 env Root)
evaluate (Lit x) _ Root = return (Lit x)
evaluate (Var v) env s = do
  let l = env ! v
  retrieval <- retrieve l
  case retrieval of Nothing -> conjure s l
                    Just (Retrieval s' lhs thunk) -> do
                      rhs <- force determine evaluate thunk (compose s' s)
                      store lhs rhs
                      value l
evaluate e@(Choice _)   env Root = return (measure e env)
evaluate e@(Bind _ _ _) env Root = return (measure e env)
evaluate e@(Dirac _)    env Root = return (measure e env)
evaluate (Pair e1 e2) env Root    = liftM2 Pair (delay e1 env) (delay e2 env)
evaluate (Pair e1 e2) env (Fst s) = liftM2 Pair (evaluate e1 env s)
                                                (delay e2 env)
evaluate (Pair e1 e2) env (Snd s) = liftM2 Pair (delay e1 env)
                                                (evaluate e2 env s)
evaluate (Inl e')     env Root    = fmap Inl (delay e' env)
evaluate (Inl e')     env (Unl s) = fmap Inl (evaluate e' env s)
evaluate (Inl _)      _   (Unr _) = reject
evaluate (Inr e')     env Root    = fmap Inr (delay e' env)
evaluate (Inr e')     env (Unr s) = fmap Inr (evaluate e' env s)
evaluate (Inr _)      _   (Unl _) = reject
evaluate (Cons a as)  env Root    = liftM2 Cons (delay a env) (delay as env)
evaluate (Cons a as)  env (Car s) = liftM2 Cons (evaluate a env s)
                                                (delay as env)
evaluate (Cons a as)  env (Cdr s) = liftM2 Cons (delay a env)
                                                (evaluate as env s)
evaluate (Closure e' env') env Root =
  return (uncurry Closure (close e' env' env))

conjure :: Selector to t -> Loc t -> M (Expr Void Loc t)
conjure Root l = return (Var l)
conjure (Fst s) l = do
  l1 <- gensym
  l2 <- gensym
  insert (Bind (Branch (Leaf l1) (Leaf l2)) (Dirac (Var l)))
  fmap (`Pair` Var l2) (conjure s l1)
conjure (Snd s) l = do
  l1 <- gensym
  l2 <- gensym
  insert (Bind (Branch (Leaf l1) (Leaf l2)) (Dirac (Var l)))
  fmap (Var l1 `Pair`) (conjure s l2)
conjure (Car s) l = do
  l1 <- gensym
  l2 <- gensym
  insert (Bind (LCons (Leaf l1) (Leaf l2)) (Dirac (Var l)))
  fmap (`Cons` Var l2) (conjure s l1)
conjure (Cdr s) l = do
  l1 <- gensym
  l2 <- gensym
  insert (Bind (LCons (Leaf l1) (Leaf l2)) (Dirac (Var l)))
  fmap (Var l1 `Cons`) (conjure s l2)
conjure _ _ = mempty

------- Main disintegrator

disintegrate :: (Delay env b u) => Expr b u (Measure t) ->
                env -> Selector to t -> Expr Void Loc to -> M (Expr Void Loc t)
disintegrate e env s t
  | traceShow (prettyFun False "disintegrate"
                (sep [pretty' 11 e, pretty env, pretty' 11 s, pretty' 11 t]))
              False = undefined
disintegrate (Op0 Lebesgue) _ Root t = return t
disintegrate (Op0 Counting) _ Root t = return t
disintegrate e@(Op1 Weight _) env Root _ = determine e env Root
disintegrate e@(Var _) env s t = do
  v <- evaluate e env Root
  case v of Var _ -> mempty
            _ -> disintegrate v () s t
disintegrate (Choice es) env s t =
  M (\c h -> fmap Choice (mapM (\e -> unM (disintegrate e env s t) c h) es))
disintegrate (Bind lhs rhs body) env s t = do
  env' <- allocate lhs rhs env
  disintegrate body env' s t
disintegrate (Dirac e) env s t = propagate e env s t
disintegrate (Closure e' env') env s t =
  uncurry disintegrate (close e' env' env) s t

propagate :: (Delay env b u) => Expr b u t ->
             env -> Selector to t -> Expr Void Loc to -> M (Expr Void Loc t)
propagate e env s t
  | traceShow (prettyFun False "propagate"
                (sep [pretty' 11 e, pretty env, pretty' 11 s, pretty' 11 t]))
              False = undefined
propagate (Op0 Lebesgue) _ _ _ = mempty
propagate (Op0 Counting) _ _ _ = mempty
propagate (Op0 Pi) _ _ _ = mempty
propagate (Op0 Infinity) _ _ _ = mempty
propagate (Op0 NegativeInfinity) _ _ _ = mempty
propagate (Op0 Unit) _ _ _ = return (Op0 Unit)
propagate (Op0 EmptyList) _ Root t = do
  insert (Bind LNil (Dirac (ex t)))
  return (Op0 EmptyList)
propagate (Op0 EmptyList) _ (Car _) _ = reject
propagate (Op0 EmptyList) _ (Cdr _) _ = reject
propagate (Op0 True_) _ Root t = do
  insert (Bind BoolT (Dirac (ex t)))
  return (Op0 True_)
propagate (Op0 False_) _ Root t = do
  insert (Bind BoolF (Dirac (ex t)))
  return (Op0 False_)
propagate (Op1 Exp e) env Root t = do
  insert (condLess 0 (ex t) . weight (recip (unsafeProbFraction dict (ex t))))
  fmap (Op1 Exp) (propagate e env Root (Op1 Log t))
propagate (Op1 Log e) env Root t = do
  insert (weight (Op1 Exp (ex t)))
  fmap (Op1 Log) (propagate e env Root (Op1 Exp t))
propagate (Op1 Neg e) env Root t =
  fmap negate (propagate e env Root (-t))
propagate (Op1 Inv e) env Root t = do
  insert (weight (recip (unsafeProbFraction dict (ex t * ex t))))
  fmap recip (propagate e env Root (recip t))
propagate (Op1 Sin e) env Root t = do
  ln <- gensym
  lt <- gensym
  insert (condLess (-1) (ex t) .
          condLess (ex t) 1 .
          weight (power (Op1 UnsafeProb (1 - ex t * ex t)) (1/2)) .
          Bind (Leaf ln) (Op0 Counting) .
          Bind (Leaf lt) (Choice [ Dirac (Op1 FromInt (f (2 * Var ln)) * Op0 Pi
                                          + g (Op1 ASin (ex t)))
                                 | (f,g) <- [(id, id), ((1+), negate)] ]))
  fmap (Op1 Sin) (propagate e env Root (Var lt))
propagate (Op1 Cos e) env Root t = do
  ln <- gensym
  lt <- gensym
  insert (condLess (-1) (ex t) .
          condLess (ex t) 1 .
          weight (power (Op1 UnsafeProb (1 - ex t * ex t)) (1/2)) .
          Bind (Leaf ln) (Op0 Counting) .
          Bind (Leaf lt) (Choice [ Dirac (Op1 FromInt (2 * Var ln) * Op0 Pi
                                          + g (Op1 ACos (ex t)))
                                 | g <- [id, negate] ]))
  fmap (Op1 Cos) (propagate e env Root (Var lt))
propagate (Op1 Tan e) env Root t = do
  ln <- gensym
  insert (weight (recip (Op1 UnsafeProb (1 + ex t * ex t))) .
          Bind (Leaf ln) (Op0 Counting))
  fmap (Op1 Tan) (propagate e env Root (Op1 FromInt (Var ln) * Op0 Pi
                                        + Op1 ATan t))
propagate (Op1 ASin e) env Root t = do
  insert (condLess (- Op0 Pi / 2) (ex t) .
          condLess (ex t) (Op0 Pi / 2) .
          weight (Op1 UnsafeProb (Op1 Cos (ex t))))
  fmap (Op1 ASin) (propagate e env Root (Op1 Sin t))
propagate (Op1 ACos e) env Root t = do
  insert (condLess 0 (ex t) .
          condLess (ex t) (Op0 Pi) .
          weight (Op1 UnsafeProb (Op1 Sin (ex t))))
  fmap (Op1 ACos) (propagate e env Root (Op1 Cos t))
propagate (Op1 ATan e) env Root t = do
  insert (condLess (- Op0 Pi / 2) (ex t) .
          condLess (ex t) (Op0 Pi / 2) .
          weight (recip (Op1 UnsafeProb (Op1 Cos (ex t) * Op1 Cos (ex t)))))
  fmap (Op1 ATan) (propagate e env Root (Op1 Tan t))
propagate (Op1 Weight _) _ Root _ = mempty
propagate (Op1 UnsafeProb e) env Root t =
  fmap (Op1 UnsafeProb) (propagate e env Root (Op1 FromProb t))
propagate (Op1 FromProb e) env Root t = do
  insert (condLess 0 (ex t))
  fmap (Op1 FromProb) (propagate e env Root (Op1 UnsafeProb t))
propagate (Op1 FromInt _) _ Root _ = mempty
propagate (Op1 GammaFunc _) _ Root _ = mempty
propagate (Op1 Erf _) _ Root _ = mempty -- need InvErf to disintegrate Erf
propagate (Op2 Add e1 e2) env Root t = mappend (go e1 e2) (go e2 e1)
  where go e e' = do x1 <- evaluate e env Root
                     fmap (x1 +) (propagate e' env Root (t - x1))
propagate (Op2 Mul e1 e2) env Root t = r e1 e2 env t where
  PropagateMul r = numberCase propagateMulInt
                              propagateMulFractions
                              propagateMulFractions
propagate e@(Op2 Less  _ _) env s t = propagateBool e env s t
propagate e@(Op2 Equal _ _) env s t = propagateBool e env s t
propagate (Op2 BetaFunc _ _) _ Root _ = mempty
propagate (Lit x) _ Root _ = return (Lit x) -- HACK! pretends dirac has density!
propagate (Var v) env s t = do
  let l = env ! v
  retrieval <- retrieve l
  case retrieval of Nothing -> conjure s l -- HACK! pretends dirac has density!
                    Just (Retrieval s' lhs thunk) -> do
                      rhs <- force disintegrate propagate thunk (compose s' s) t
                      store lhs rhs
                      value l
propagate (Choice _) _ Root _ = mempty
propagate (Bind _ _ _) _ Root _ = mempty
propagate (Dirac _) _ Root _ = mempty
propagate (Pair e1 e2) env Root t = do
  l1 <- gensym
  l2 <- gensym
  insert (Bind (Branch (Leaf l1) (Leaf l2)) (Dirac (ex t)))
  liftM2 Pair (propagate e1 env Root (Var l1))
              (propagate e2 env Root (Var l2))
propagate (Pair e1 e2) env (Fst s) t =
  liftM2 Pair (propagate e1 env s t) (delay e2 env)
propagate (Pair e1 e2) env (Snd s) t =
  liftM2 Pair (delay e1 env) (propagate e2 env s t)
propagate (Inl e) env Root t = do
  l <- gensym
  insert (Bind (UnaryL (Leaf l)) (Dirac (ex t)))
  fmap Inl (propagate e env Root (Var l))
propagate (Inl e) env (Unl s) t =
  fmap Inl (propagate e env s t)
propagate (Inl _) _   (Unr _) _ = reject
propagate (Inr e) env Root t = do
  l <- gensym
  insert (Bind (UnaryR (Leaf l)) (Dirac (ex t)))
  fmap Inr (propagate e env Root (Var l))
propagate (Inr e) env (Unr s) t =
  fmap Inr (propagate e env s t)
propagate (Inr _) _   (Unl _) _ = reject
propagate (Cons a as) env Root t = do
  l1 <- gensym
  l2 <- gensym
  insert (Bind (LCons (Leaf l1) (Leaf l2)) (Dirac (ex t)))
  liftM2 Cons (propagate a  env Root (Var l1))
              (propagate as env Root (Var l2))
propagate (Cons a as) env (Car s) t =
  liftM2 Cons (propagate a env s t) (delay as env)
propagate (Cons a as) env (Cdr s) t =
  liftM2 Cons (delay a env) (propagate as env s t)
propagate (Closure _ _) _ Root _ = mempty

propagateBool :: (Delay env b u) => Expr b u Bool ->
                 env -> Selector to Bool -> Expr Void Loc to ->
                 M (Expr Void Loc Bool)
propagateBool e env Root t = do
  x <- evaluate e env Root
  M (\c h -> let ets = c (Op0 True_) h
                 efs = c (Op0 False_) h
             in [ if' (ex x) (Bind BoolT (Dirac (ex t)) et)
                             (Bind BoolF (Dirac (ex t)) ef)
                | et <- ets, ef <- efs ])

newtype PropagateMul env b u t = PropagateMul
  (Expr b u t -> Expr b u t -> env -> Expr Void Loc t -> M (Expr Void Loc t))
propagateMulInt :: (Delay env b u) => PropagateMul env b u Int
propagateMulInt = PropagateMul (\_ _ _ _ -> mempty) -- TODO
propagateMulFractions :: (Delay env b u, Fraction t) => PropagateMul env b u t
propagateMulFractions = PropagateMul f
  where f e1 e2 env t = mappend (go e1 e2 env t) (go e2 e1 env t)
        go e e' env t = do x1 <- evaluate e env Root
                           insert (Bind Nil (if' (Op2 Less 0 (ex x1))
                                                 (use (ex x1))
                                                 (use (-(ex x1)))))
                           fmap (x1 *) (propagate e' env Root (t/x1))
        use poz = Op1 Weight (recip (unsafeProbFraction dict poz))

------- To finish off evaluation or disintegration, we need to turn residual
------- heap entries into bindings and closures into monadic expressions

run :: M (Expr Void Loc t) -> [Expr Loc Loc (Measure t)]
run = run' 1

data Node = LHS Int | RHS Int deriving (Eq, Ord)

run' :: Int -> M (Expr Void Loc t) -> [Expr Loc Loc (Measure t)]
run' l m = unM (do e <- m
                   traceHeap "Before determineHeap:"
                   determineHeap
                   traceHeap "After determineHeap:"
                   return (Dirac (ex e)))
               finish
               Heap{fresh = l, bound = []}
  where finish e0 h = [determineClosures (foldl f e0 bindings)]
          where f e (Binding lhs rhs) = Bind lhs (Dirac (ex rhs)) e
                bindings = [ node | (node, LHS _, _) <- map v (topSort g) ]
                (g,v,_) = graphFromEdges (concat
                  [ (Binding lhs e,
                     LHS n,
                     foldMap' (\(Const loc) -> [RHS loc]) e)
                  : foldMap' (\(Const loc) -> [(undefined, RHS loc, [LHS n])])
                             lhs
                  | (n, Binding lhs (Forced e)) <- zip [0..] (bound h) ])

traceHeap :: String -> M ()
traceHeap label = M (\c h -> traceShow (text label <+> pretty h) (c () h))

data RetrievalThunk where
  RetrievalThunk :: Tree Loc t ->
                    Expr Name Name (Measure t) -> Env -> RetrievalThunk

retrieveThunk :: [Binding (Tree Loc) Thunk] ->
                 Maybe (RetrievalThunk, [Binding (Tree Loc) Thunk])
retrieveThunk [] = Nothing
retrieveThunk (b : bs) = case b of
  Binding lhs (Delayed e env) -> Just (RetrievalThunk lhs e env, bs)
  _ -> fmap (fmap (b:)) (retrieveThunk bs)

determineHeap :: M ()
determineHeap = M (\c h ->
  case retrieveThunk (bound h) of
    Nothing -> c () h
    Just (RetrievalThunk lhs e env, bs) ->
      unM (determine e env Root >>= store lhs >> determineHeap)
          c h{bound = bs})

newtype Max a = Max { getMax :: a }
instance (Ord a, Bounded a) => Monoid (Max a) where
  mempty = Max minBound
  mappend (Max a) (Max b) = Max (max a b)
  mconcat = Max . maximum . map getMax

determineClosures :: Expr Loc Loc t -> Expr Loc Loc t
determineClosures = bimap' id id $ \e env ->
  let f (Const n') = Max n'
      n = succ (max 0 (getMax (vars hideUse (\u -> f (env !! u)) e)))
      -- TODO: is the list below really always singleton?
      [result] = run' n (determine e env Root)
  in result

------- Conversion to Hakaru

newtype Nullary repr a = Nullary { unNullary :: repr a }
newtype Unary   repr a = Unary   { unUnary   :: repr a -> repr a }
newtype Binary  repr a = Binary  { unBinary  :: repr a -> repr a -> repr a }
newtype Boolean repr a = Boolean { unBoolean :: repr a -> repr a -> repr Bool }

nullary :: (Number   a, Base repr) => ((Order repr a, Num (repr a)) =>
           repr a) -> repr a
unaryN  :: (Number   a, Base repr) => ((Order repr a, Num (repr a)) =>
           repr a -> repr a) -> repr a -> repr a
unary   :: (Fraction a, Base repr) => ((Order repr a, Fractional (repr a)) =>
           repr a -> repr a) -> repr a -> repr a
binaryN :: (Number   a, Base repr) => ((Order repr a, Num (repr a)) =>
           repr a -> repr a -> repr a) -> repr a -> repr a -> repr a
binary  :: (Fraction a, Base repr) => ((Order repr a, Fractional (repr a)) =>
           repr a -> repr a -> repr a) -> repr a -> repr a -> repr a
boolean :: (Number   a, Base repr) => ((Order repr a, Num (repr a)) =>
           repr a -> repr a -> repr Bool) -> repr a -> repr a -> repr Bool

nullary x = unNullary (numberRepr   (Nullary x))
unaryN  x = unUnary   (numberRepr   (Unary   x))
unary   x = unUnary   (fractionRepr (Unary   x))
binaryN x = unBinary  (numberRepr   (Binary  x))
binary  x = unBinary  (fractionRepr (Binary  x))
boolean x = unBoolean (numberRepr   (Boolean x))

toHakaru :: (Eq a, Show' (Const a), Mochastic repr) =>
            Expr (Const a) (Const a) t' ->
            (forall t. Const a t -> repr t) -> repr t'
toHakaru (Op0 Lebesgue)            _   = lebesgue
toHakaru (Op0 Counting)            _   = counting
toHakaru (Op0 Pi)                  _   = piFraction dict
toHakaru (Op0 Infinity)            _   = infinity
toHakaru (Op0 NegativeInfinity)    _   = negativeInfinity
toHakaru (Op0 Unit)                _   = unit
toHakaru (Op0 EmptyList)           _   = nil
toHakaru (Op0 True_)               _   = true
toHakaru (Op0 False_)              _   = false
toHakaru (Op1 Exp e)               env = expFraction dict (toHakaru e  env)
toHakaru (Op1 Log e)               env = logFraction dict (toHakaru e  env)
toHakaru (Op1 Neg e)               env = unaryN negate    (toHakaru e  env)
toHakaru (Op1 Inv e)               env = unary recip      (toHakaru e  env)
toHakaru (Op1 Sin e)               env = sin              (toHakaru e  env)
toHakaru (Op1 Cos e)               env = cos              (toHakaru e  env)
toHakaru (Op1 Tan e)               env = tan              (toHakaru e  env)
toHakaru (Op1 ASin e)              env = asin             (toHakaru e  env)
toHakaru (Op1 ACos e)              env = acos             (toHakaru e  env)
toHakaru (Op1 ATan e)              env = atan             (toHakaru e  env)
toHakaru (Op1 Weight e)            env = factor           (toHakaru e  env)
toHakaru (Op1 UnsafeProb e)        env = unsafeProb       (toHakaru e  env)
toHakaru (Op1 FromProb e)          env = fromProb         (toHakaru e  env)
toHakaru (Op1 FromInt e)           env = fromInt          (toHakaru e  env)
toHakaru (Op1 GammaFunc e)         env = gammaFunc        (toHakaru e  env)
toHakaru (Op1 Erf e)               env = erfFraction dict (toHakaru e  env)
toHakaru (Op2 Add e1 (Op1 Neg e2)) env = binaryN (-)      (toHakaru e1 env)
                                                          (toHakaru e2 env)
toHakaru (Op2 Add e1 e2)  env          = binaryN (+)      (toHakaru e1 env)
                                                          (toHakaru e2 env)
toHakaru (Op2 Mul e1 (Op1 Inv e2)) env = binary (/)       (toHakaru e1 env)
                                                          (toHakaru e2 env)
toHakaru (Op2 Mul e1 e2)           env = binaryN (*)      (toHakaru e1 env)
                                                          (toHakaru e2 env)
toHakaru (Op2 Less e1 e2)          env = boolean less     (toHakaru e1 env)
                                                          (toHakaru e2 env)
toHakaru (Op2 Equal e1 e2)         env = boolean equal    (toHakaru e1 env)
                                                          (toHakaru e2 env)
toHakaru (Op2 BetaFunc e1 e2)      env = betaFunc         (toHakaru e1 env)
                                                          (toHakaru e2 env)
toHakaru (Lit x)                   _   = nullary (fromInteger x)
toHakaru (Var u)                   env = env u
toHakaru (Choice [e])              env = toHakaru e env -- simplification
toHakaru (Choice es)               env = superpose [ (1, toHakaru e env)
                                                   | e <- es ]
toHakaru e@(Bind lhs rhs body)     env =
  toHakaru rhs env `bind` \x ->
  matchHakaru lhs x (\bindings ->
  if unique bindings
  then toHakaru body (\v -> fromMaybe (env v) (lookup bindings v))
  else error ("Duplicate variable in " ++ show' 0 e ""))
toHakaru (Dirac e)                 env = dirac (toHakaru e  env)
toHakaru (Pair e1 e2)              env = pair  (toHakaru e1 env)
                                               (toHakaru e2 env)
toHakaru (Inl e)                   env = inl   (toHakaru e  env)
toHakaru (Inr e)                   env = inr   (toHakaru e  env)
toHakaru (Cons a as)               env = cons  (toHakaru a  env)
                                               (toHakaru as env)
toHakaru (Closure e env) f             = toHakaru e (f . (env !!))

matchHakaru :: (Mochastic repr) => Tree u t -> repr t ->
               ([Binding u repr] -> repr (Measure w)) -> repr (Measure w)
matchHakaru (Branch t1 t2) x k =
  unpair x (\x1 x2 ->
  matchHakaru t1 x1 (\b1 ->
  matchHakaru t2 x2 (\b2 -> k (b1 ++ b2))))
matchHakaru (UnaryL t') x k =
  uneither x (\x' -> matchHakaru t' x' k) (\_ -> superpose [])
matchHakaru (UnaryR t') x k =
  uneither x (\_ -> superpose []) (\x' -> matchHakaru t' x' k)
matchHakaru LNil x k =
  unlist x (k []) (\_ _ -> superpose [])
matchHakaru (LCons a as) x k =
  unlist x (superpose []) (\a' as' ->
  matchHakaru a  a'  (\b1 ->
  matchHakaru as as' (\b2 -> k (b1 ++ b2))))
matchHakaru Nil   _ k = k []
matchHakaru BoolT x k = if_ x (k []) (superpose [])
matchHakaru BoolF x k = if_ x (superpose []) (k [])
matchHakaru (Leaf u) x k = k [Binding u x]

------- Conversion from Hakaru

newtype Disintegrate a = Disint
  (forall w. Cont (Int -> Expr Loc Loc (Measure w)) (Expr Loc Loc a))

newtype Disintegration env a b = Disintegration
  (forall repr. (Mochastic repr) => repr env -> repr a -> repr (Measure b))

disintegrations :: (Order_ a) =>
                   (Disintegrate env -> Disintegrate (Measure (a, b))) ->
                   [Disintegration env a b]
disintegrations m =
  case Const (-1) of { envLoc -> case Const 0 of { aLoc ->
  let nameOfLoc :: Loc t -> Name t
      nameOfLoc (Const i) = Const ('x' : show i)
      expr = bimap' nameOfLoc nameOfLoc Closure
        $ unDisint (m (Disint (return (Var envLoc)))) (\w _ -> w) 1
  in [ Disintegration (\env a ->
       toHakaru dis ([Binding envLoc env, Binding aLoc a] !!) `bind` \ab ->
       unpair ab (\a' b' ->
       if_ (equal_ a a') (dirac b') (superpose [])))
     | dis <- run (disintegrate expr
                                [Binding (nameOfLoc envLoc) envLoc]
                                (Fst Root)
                                (Var aLoc)) ] } }

runDisintegrate :: (Mochastic repr, Order_ a) =>
                   (Disintegrate env -> Disintegrate (Measure (a, b))) ->
                   [repr env -> repr a -> repr (Measure b)]
runDisintegrate m = [ d | Disintegration d <- disintegrations m ]

condition :: (Mochastic repr, Order_ a) => Disintegrate (Measure (a, b)) ->
                                 repr a -> repr (Measure b)
condition d = head (runDisintegrate (\ _ -> d)) unit

density :: (Integrate repr, Mochastic repr, Lambda repr, Order_ a) =>
           (Disintegrate env -> Disintegrate (Measure a)) ->
           [repr (Expect' env) -> repr (Expect' a) -> repr Prob]
density m = [ \e o -> total (f (Expect e) (Expect o))
            | f <- runDisintegrate (liftM (`pair` unit) . m) ]

unDisint :: Disintegrate a ->
            (Expr Loc Loc a -> Int -> Expr Loc Loc (Measure w))
                            -> Int -> Expr Loc Loc (Measure w)
unDisint (Disint m) = runCont m

insertDisint :: Disintegrate t
             -> (forall w. Expr Loc Loc t ->
                  (Expr Loc Loc a -> Int -> Expr Loc Loc (Measure w))
                                  -> Int -> Expr Loc Loc (Measure w))
             -> Disintegrate a
insertDisint (Disint x) f = Disint (x >>= cont . f)

resetDisint :: Disintegrate t -> Disintegrate t
resetDisint d = Disint (cont (\c i ->
  Bind (Leaf (Const i)) (unDisint d (\w _ -> Dirac w) i)
       (c (Var (Const i)) (succ i))))

instance (Number t) => Order Disintegrate t where
  less  (Disint x) (Disint y) = Disint (fmap (Op2 Less)  x <*> y)
  equal (Disint x) (Disint y) = Disint (fmap (Op2 Equal) x <*> y)

instance (Number t) => Num (Disintegrate t) where
  Disint x + Disint y = Disint (fmap (+) x <*> y)
  Disint x * Disint y = Disint (fmap (*) x <*> y)
  negate (Disint x)   = Disint (fmap negate x)
  abs x = insertDisint x (\e c i ->
    Bind (Leaf (Const i))
         (if' (Op2 Less 0 e) (Dirac e) (Dirac (-e)))
         (c (Var (Const i)) (succ i)))
  signum x = insertDisint x (\e c i ->
    Bind (Leaf (Const i))
         (if' (Op2 Less 0 e) (Dirac (1 `asTypeOf` e)) (Dirac (-1)))
         (c (Var (Const i)) (succ i)))
  fromInteger x = Disint (return (fromInteger x))

instance (Fraction t) => Fractional (Disintegrate t) where
  recip (Disint x) = Disint (fmap recip x)
  fromRational x   = Disint (return (fromRational x))

instance Floating (Disintegrate Real) where
  pi              = Disint (return (Op0 Pi))
  exp  (Disint x) = Disint (fmap (Op1 Exp) x)
  log  (Disint x) = Disint (fmap (Op1 Log) x)
  sin  (Disint x) = Disint (fmap (Op1 Sin) x)
  cos  (Disint x) = Disint (fmap (Op1 Cos) x)
  tan  (Disint x) = Disint (fmap (Op1 Tan) x)
  asin (Disint x) = Disint (fmap (Op1 ASin) x)
  acos (Disint x) = Disint (fmap (Op1 ACos) x)
  atan (Disint x) = Disint (fmap (Op1 ATan) x)
  -- TODO: Disintegrate {,a}{sin,cos,tan}h directly
  sinh  x         = (exp x - exp (-x)) / 2
  cosh  x         = (exp x + exp (-x)) / 2
  tanh  x         = (exp x - exp (-x)) / (exp x + exp (-x))
  asinh x         = log (x + sqrt (x * x + 1))
  acosh x         = log (x + sqrt (x * x - 1))
  atanh x         = log ((1 + x) / (1 - x)) / 2

instance Base Disintegrate where
  unit                           = Disint (return (Op0 Unit))
  pair (Disint x) (Disint y)     = Disint (fmap Pair x <*> y)
  nil                            = Disint (return (Op0 EmptyList))
  cons (Disint a) (Disint as)    = Disint (fmap Cons a <*> as)
  inl (Disint x)                 = Disint (fmap Inl x)
  inr (Disint x)                 = Disint (fmap Inr x)
  true                           = Disint (return (Op0 True_))
  false                          = Disint (return (Op0 False_))
  unsafeProb (Disint x)          = Disint (fmap (Op1 UnsafeProb) x)
  fromProb (Disint x)            = Disint (fmap (Op1 FromProb) x)
  fromInt (Disint x)             = Disint (fmap (Op1 FromInt) x)
  pi_                            = Disint (return (Op0 Pi))
  exp_ (Disint x)                = Disint (fmap (Op1 Exp) x)
  erf (Disint x)                 = Disint (fmap (Op1 Erf) x)
  erf_ (Disint x)                = Disint (fmap (Op1 Erf) x)
  log_ (Disint x)                = Disint (fmap (Op1 Log) x)
  infinity                       = Disint (return (Op0 Infinity))
  negativeInfinity               = Disint (return (Op0 NegativeInfinity))
  gammaFunc (Disint x)           = Disint (fmap (Op1 GammaFunc) x)
  betaFunc (Disint a) (Disint b) = Disint (fmap (Op2 BetaFunc) a <*> b)

  unpair xy k = insertDisint xy (\e c i ->
    let x = Const i
        y = Const (i+1)
    in Bind (Branch (Leaf x) (Leaf y)) (Dirac e)
            (unDisint (k (Disint (return (Var x))) (Disint (return (Var y))))
                      c
                      (i+2)))

  unlist aas kn kc = insertDisint aas (\e c i ->
    Choice [ Bind LNil (Dirac e) (unDisint kn c i)
           , let a  = Const i
                 as = Const (i+1)
             in Bind (LCons (Leaf a) (Leaf as)) (Dirac e)
                     (unDisint (kc (Disint (return (Var a)))
                                   (Disint (return (Var as))))
                               c
                               (i+2)) ])

  uneither xy kx ky = insertDisint xy (\e c i ->
    Choice [ let x = Const i
             in Bind (UnaryL (Leaf x)) (Dirac e)
                     (unDisint (kx (Disint (return (Var x)))) c (i+1))
           , let y = Const i
             in Bind (UnaryR (Leaf y)) (Dirac e)
                     (unDisint (ky (Disint (return (Var y)))) c (i+1)) ])

  if_ cy ty ey = insertDisint cy (\e c i ->
    Choice [ Bind BoolT (Dirac e) (unDisint ty c i)
           , Bind BoolF (Dirac e) (unDisint ey c i) ])

instance Mochastic Disintegrate where
  dirac x = Disint (cont (\c i -> c (unDisint x (\w _ -> Dirac w) i) i))
  bind (Disint x) k = Disint (cont (\c i ->
    c (Bind (Leaf (Const i))
            (runCont x (\w _ -> w) i)
            (unDisint (k (Disint (return (Var (Const i)))))
                      (\w _ -> w)
                      (i+1)))
      i))
  lebesgue = Disint (return (Op0 Lebesgue))
  counting = Disint (return (Op0 Counting))
  superpose pms = Disint (cont (\c i ->
    c (Choice
       [ Bind Nil
              (runCont p (\w _ -> Op1 Weight w) i)
              (runCont m (\w _ -> w) i)
       | (Disint p, Disint m) <- pms ])
      i))
