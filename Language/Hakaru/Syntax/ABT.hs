-- TODO: <https://git-scm.com/book/en/v2/Git-Branching-Basic-Branching-and-Merging>
{-# LANGUAGE RankNTypes, TypeFamilies, DataKinds #-}

module Language.Hakaru.Syntax.ABT where

import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.AST

----------------------------------------------------------------
-- TODO: will we want to make this polykinded instead of restricting to the @Hakaru*@ kind?
-- | A functor on the category of @Hakaru*@-indexed types.
class HakaruFunctor (f :: (Hakaru * -> *) -> Hakaru * -> *) where
    hmap :: (forall b. g b -> g' b) -> f g a -> f g' a 


newtype HakaruMonoid (m :: *) (a :: Hakaru *) = HM { unHM :: m }
instance Monoid m => Monoid (HakaruMonoid m a) where
    mempty = HM mempty
    mappend (HM m) (HM n) = HM (mappend m n)
    mconcat ms = HM (mconcat $ map unHM ms)

class HakaruFunctor f
    => HakaruFoldable (f :: (Hakaru * -> *) -> Hakaru * -> *)
    where
    hfold :: (Monoid m) => f (HakaruMonoid m) a -> m
    
    hfoldMap :: (Monoid m) => (forall b. g b -> m) -> f g a -> m
    hfoldMap f = hfold . hmap (HM . f)

instance HakaruFunctor AST where
    hmap = error "TODO"
    
instance HakaruFoldable AST where
    hfold = error "TODO"

----------------------------------------------------------------
-- TODO: have @Variable a@ instead, with @SomeVariable@ to backage up the existential? This would allow us to preserve type safety in 'subst'

-- <http://semantic-domain.blogspot.co.uk/2015/03/abstract-binding-trees.html>
-- <http://semantic-domain.blogspot.co.uk/2015/03/abstract-binding-trees-addendum.html>
-- <https://gist.github.com/neel-krishnaswami/834b892327271e348f79>
-- TODO: abstract over 'AST' like neelk does for @signature@?
-- TODO: remove the proxy type for 'Var', and just infer it?
-- | Abstract binding trees, to separate out variables/binders from the rest of the syntax.
data View :: (Hakaru * -> *) -> Hakaru * -> * where
    Var  :: !Variable -> !(Proxy a) -> View abt a
    Open :: !Variable -> abt a -> View abt a
    Syn  :: !(AST abt a) -> View abt a

instance HakaruFunctor AST => HakaruFunctor View where
    hmap f (Var  x p) = Var  x p
    hmap f (Open x t) = Open x (f t)
    hmap f (Syn  t)   = Syn (hmap f t)

-- TODO: neelk includes 'toABT', 'freeVars', and 'subst' in the signature. Should we?
-- TODO: add a function for checking alpha-equivalence?
class ABT (abt :: Hakaru * -> *) where
    var     :: Variable -> Proxy a -> abt a
    open    :: Variable -> abt a -> abt a
    syn     :: AST abt a -> abt a
    fromABT :: abt a -> View abt a

toABT :: (ABT abt) => View abt a -> abt a
toABT (Var  x p) = var  x p
toABT (Open x t) = open x t
toABT (Syn  t)   = syn  t


data ABTException = UnOpenException
    deriving (Show, Typeable)

instance Exception ABTException

-- We could render this function safe by further indexing @abt@ with a tag to say whether it's Open or Var/Syn. But that may be overkill, especially once we start handling more complicated binders. This only throws an error if the ABT the parser generates is malformed, we can trust/check the parser rather than complicating the types further.
unOpen :: ABT abt => abt a -> (Variable, abt a)
unOpen e =
    case fromABT e of
    Open x t -> (x,t)
    _         -> throw UnOpenException -- TODO: add info about the call-site


----------------------------------------------------------------
-- A trivial ABT with no annotations
newtype TrivialABT (a :: Hakaru *) = TrivialABT (View TrivialABT a)

instance ABT TrivialABT where
    var x p  = TrivialABT (Var x p)
    open x e = TrivialABT (Open x e)
    syn e    = TrivialABT (Syn e)
    
    fromABT (TrivialABT e) = e

    
----------------------------------------------------------------
-- TODO: replace @Set Variable@ with @Map Variable (Hakaru Star)@; though that belongs more in the type-checking than in this FreeVarsABT itself...
-- TODO: generalize this pattern for any monoidal annotation?
-- | An ABT which keeps track of free variables.
data FreeVarsABT (a :: Hakaru *)
    = FreeVarsABT !(Set Variable) !(View FreeVarsABT a)
    -- N.B., Set is a monoid with {Set.empty; Set.union; Set.unions}

instance ABT FreeVarsABT where
    var x p  = FreeVarsABT (Set.singleton x) (Var x p)
    open x e = FreeVarsABT (Set.delete x $ freeVars e) (Open x e)
    syn e    = FreeVarsABT (hfoldMap freeVars e) (Syn e)
    
    fromABT (FreeVarsABT _ e) = e


freeVars :: FreeVarsABT a -> Set Variable
freeVars (FreeVarsABT vs _) = vs

-- TODO: something smarter
freshen :: Variable -> Set Variable -> Variable
freshen v vs
    | v `Set.member` vs = freshen (v ++"'") vs
    | otherwise         = v

-- | Rename a free variable. Does nothing if the variable is bound.
rename :: Variable -> Variable -> ABT a -> ABT a
rename x y = go
    where
    go e =
        case fromABT e of
        Var z p
            | x == z    -> var y p
            | otherwise -> e
        Open z e'
            | x == z    -> e
            | otherwise -> open z (go e')
        Syn e'          -> syn (hmap go e')

-- N.B., is not guaranteed to preserve type safety!
subst :: Variable -> ABT a -> ABT b -> ABT b
subst x e = go
    where
    go body = 
        case fromABT body of
        Var z p
            | x == z    -> e -- TODO: could preserve type-safety if we check that @typeOf e == typeOf p@. Of course, if that fails, then we'd have to return @Nothing@, which will make the recursive calls trickier...
            | otherwise -> body
        Open z body'
            | x == z    -> body
            | otherwise -> 
                let z' = freshen z (freeVars e `mappend` freeVars body)
                in  open z' (go (rename z z' body'))
        Syn body' -> syn (hmap go body')

----------------------------------------------------------------
----------------------------------------------------------- fin.