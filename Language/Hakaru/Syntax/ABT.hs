-- TODO: <https://git-scm.com/book/en/v2/Git-Branching-Basic-Branching-and-Merging>
{-# LANGUAGE RankNTypes
           , ScopedTypeVariables
           , GADTs
           , TypeFamilies
           , DataKinds
           , DeriveDataTypeable
           #-}

module Language.Hakaru.Syntax.ABT where

import           Data.Proxy
import           Data.Typeable     (Typeable)
import           Data.Set          (Set)
import qualified Data.Set          as Set
import           Control.Exception (Exception, throw)

import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.AST

----------------------------------------------------------------
-- TODO: will we want to make this polykinded instead of restricting to the @Hakaru*@ kind?
-- | A functor on the category of @Hakaru*@-indexed types.
class HakaruFunctor (f :: (Hakaru * -> *) -> Hakaru * -> *) where
    hmap :: (forall b. g b -> g' b) -> f g a -> f g' a 


newtype HakaruMonoid (m :: *) (a :: Hakaru *) =
    HakaruMonoid { unHakaruMonoid :: m }
instance Monoid m => Monoid (HakaruMonoid m a) where
    mempty = HakaruMonoid mempty
    mappend (HakaruMonoid m) (HakaruMonoid n) = HakaruMonoid (mappend m n)
    mconcat ms = HakaruMonoid (mconcat $ map unHakaruMonoid ms)

class HakaruFunctor f
    => HakaruFoldable (f :: (Hakaru * -> *) -> Hakaru * -> *)
    where
    hfold :: (Monoid m) => f (HakaruMonoid m) a -> m
    hfold = hfoldMap unHakaruMonoid
    
    hfoldMap :: (Monoid m) => (forall b. g b -> m) -> f g a -> m
    hfoldMap f = hfold . hmap (HakaruMonoid . f)

instance HakaruFunctor AST where
    hmap = error "TODO"
    
instance HakaruFoldable AST where
    hfold = error "TODO"

----------------------------------------------------------------
-- TODO: actually define 'Variable'
-- TODO: have @Variable a@ instead, with @SomeVariable@ to package up the existential? This would allow us to preserve type safety in 'subst'

newtype Variable = Variable String
    deriving (Eq, Ord, Read, Show)


-- TODO: go back to the name \"Abs\"(traction), and figure out some other name for the \"Abs\"(olute value) PrimOp to avoid conflict. Or maybe call it \"Bind\"(er) and then come up with some other name for the HMeasure monadic bind operator?
-- <http://semantic-domain.blogspot.co.uk/2015/03/abstract-binding-trees.html>
-- <http://semantic-domain.blogspot.co.uk/2015/03/abstract-binding-trees-addendum.html>
-- <https://gist.github.com/neel-krishnaswami/834b892327271e348f79>
-- TODO: abstract over 'AST' like neelk does for @signature@?
-- TODO: remove the proxy type for 'Var', and infer it instead?
-- | Abstract binding trees, to separate out variables and binders
-- from the rest of syntax.
data View :: (Hakaru * -> *) -> Hakaru * -> * where
    Var  :: !Variable -> !(Proxy a) -> View abt a
    Open :: !Variable -> abt a -> View abt a
    Syn  :: !(AST abt a) -> View abt a


instance HakaruFunctor View where
    hmap f (Var  x p) = Var  x p
    hmap f (Open x e) = Open x (f e)
    hmap f (Syn  t)   = Syn (hmap f t)


-- TODO: neelk includes 'toABT' and 'subst' in the signature. Should we?
-- TODO: add a function for checking alpha-equivalence?
class ABT (abt :: Hakaru * -> *) where
    var      :: Variable -> Proxy a -> abt a
    open     :: Variable -> abt a -> abt a
    syn      :: AST abt a -> abt a
    fromABT  :: abt a -> View abt a
    freeVars :: abt a -> Set Variable

toABT :: (ABT abt) => View abt a -> abt a
toABT (Var  x p) = var  x p
toABT (Open x e) = open x e
toABT (Syn  t)   = syn  t


data ABTException = UnOpenException | UnVarSynException
    deriving (Show, Typeable)

instance Exception ABTException

-- We could render this function safe by further indexing @abt@
-- with a tag to say whether it's Open or Var/Syn. But that may be
-- overkill, especially once we start handling more complicated
-- binders. This only throws an error if the ABT the parser generates
-- is malformed, we can trust/check the parser rather than complicating
-- the types further.
unOpen :: ABT abt => abt a -> (Variable, abt a)
unOpen e =
    case fromABT e of
    Open x e' -> (x, e')
    _         -> throw UnOpenException -- TODO: add info about the call-site

unVarSyn :: ABT abt => abt a -> Either (Variable, Proxy a) (AST abt a)
unVarSyn e =
    case fromABT e of
    Var  x p -> Left (x,p)
    Open x e -> throw UnVarSynException -- TODO: add call-site info
    Syn  t   -> Right t


----------------------------------------------------------------
-- A trivial ABT with no annotations
newtype TrivialABT (a :: Hakaru *) = TrivialABT (View TrivialABT a)

instance ABT TrivialABT where
    var  x p = TrivialABT (Var  x p)
    open x e = TrivialABT (Open x e)
    syn  t   = TrivialABT (Syn  t)

    fromABT  (TrivialABT v) = v
    
    -- This is very expensive! use 'FreeVarsABT' to fix that
    freeVars (TrivialABT v) =
        case v of
        Var  x p -> Set.singleton x
        Open x e -> Set.delete x (freeVars e)
        Syn  t   -> hfoldMap freeVars t


----------------------------------------------------------------
-- TODO: replace @Set Variable@ with @Map Variable (Hakaru Star)@; though that belongs more in the type-checking than in this FreeVarsABT itself...
-- TODO: generalize this pattern for any monoidal annotation?
-- | An ABT which keeps track of free variables.
data FreeVarsABT (a :: Hakaru *)
    = FreeVarsABT !(Set Variable) !(View FreeVarsABT a)
    -- N.B., Set is a monoid with {Set.empty; Set.union; Set.unions}

instance ABT FreeVarsABT where
    var  x p = FreeVarsABT (Set.singleton x)           (Var  x p)
    open x e = FreeVarsABT (Set.delete x $ freeVars e) (Open x e)
    syn  t   = FreeVarsABT (hfoldMap freeVars t)       (Syn  t)

    fromABT  (FreeVarsABT _  v) = v

    freeVars (FreeVarsABT xs _) = xs


----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: something smarter
freshen :: Variable -> Set Variable -> Variable
freshen x@(Variable x0) xs
    | x `Set.member` xs = freshen (Variable $ x0 ++"'") xs
    | otherwise         = x

-- | Rename a free variable. Does nothing if the variable is bound.
rename :: forall abt a. (ABT abt) => Variable -> Variable -> abt a -> abt a
rename x y = go
    where
    go :: forall a. abt a -> abt a
    go e =
        case fromABT e of
        Var z p
            | x == z    -> var y p
            | otherwise -> e
        Open z e'
            | x == z    -> e
            | otherwise -> open z (go e')
        Syn t           -> syn (hmap go t)


-- N.B., is not guaranteed to preserve type safety!
subst :: forall abt a b. (ABT abt) => Variable -> abt a -> abt b -> abt b
subst x e = go
    where
    go :: forall b. abt b -> abt b
    go body =
        case fromABT body of
        Var z p
            | x == z    -> undefined p e -- BUG: need to check that @e@ and @p@ are indexed by the same type. If so then the substitution is type-safe, as checked/guaranteed by GHC. If not, then we'll need to throw some sort of error (or return @Nothing@, but that makes the recursive calls trickier...)
            | otherwise -> body
        Open z body'
            | x == z    -> body
            | otherwise ->
                let z' = freshen z (freeVars e `mappend` freeVars body)
                in  open z' (go (rename z z' body'))
        Syn body' -> syn (hmap go body')

----------------------------------------------------------------
----------------------------------------------------------- fin.