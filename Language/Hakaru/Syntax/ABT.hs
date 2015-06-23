-- TODO: <https://git-scm.com/book/en/v2/Git-Branching-Basic-Branching-and-Merging>
{-# LANGUAGE RankNTypes, TypeFamilies, DataKinds #-}

module Language.Hakaru.Syntax.ABT where

import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.AST

----------------------------------------------------------------
-- <http://semantic-domain.blogspot.co.uk/2015/03/abstract-binding-trees.html>
-- <http://semantic-domain.blogspot.co.uk/2015/03/abstract-binding-trees-addendum.html>
-- <https://gist.github.com/neel-krishnaswami/834b892327271e348f79>
-- | Abstract binding trees, to separate out variables/binders from the rest of the syntax.
data View :: (Hakaru * -> *) -> Hakaru * -> * where
    Var  :: Variable -> Proxy a -> View abt a
    Open :: Variable -> abt a -> View abt a
    Syn  :: AST abt a -> View abt a

-- TODO: what was this used for...?
vmap :: (forall b. abt b -> abt' b) -> View abt a -> View abt' a
vmap f (Var  x p) = Var  x p
vmap f (Open x t) = Open x (f t)
vmap f (Syn  t)   = Syn (fmap f t) -- BUG: AST is not a Functor...

-- a~la neelk
-- TODO: replace @Set Variable@ with @Map Variable (Hakaru Star)@; though that belongs more in the type-checking than in this simple ABT itself...
data ABT (a :: Hakaru *) = ABT (Set Variable) (View ABT a)
-- N.B., Set is a monoid with {Set.empty; Set.union; Set.unions}
    
freeVars :: ABT a -> Set Variable
freeVars (ABT vs _) = vs

fromABT :: ABT a -> View ABT a
fromABT (ABT _ e) = e

toABT :: View ABT a -> ABT a
toABT (Var  x p) = var  x p
toABT (Open x t) = open x t
toABT (Syn  t)   = syn  t

var :: Variable -> Proxy a -> ABT a
var x p = ABT (Set.singleton x) (Var x p)

open :: Variable -> ABT a -> ABT a
open x e = ABT (Set.delete x $ freeVars e) (Open x e)

syn :: AST ABT a -> ABT a
syn e = ABT (foldMap freeVars e) (Syn e) -- TODO: define our own foldMap (for AST) at the appropriate kind...

-- TODO: something smarter
freshen :: Variable -> Set Variable -> Variable
freshen v vs
    | v `Set.member` vs = freshen (v ++"'") vs
    | otherwise         = v

-- | Rename a free variable. Does nothing if the variable is bound.
rename :: Variable -> Variable -> ABT a -> ABT a
rename x y e =
    case fromABT e of
    Var z p
        | x == z    -> var y p
        | otherwise -> e
    Open z e'
        | x == z    -> e
        | otherwise -> open z (rename x y e')
    Syn e'          -> syn (fmap (rename x y) e') -- BUG: AST is not Functor...

-- N.B., is not guaranteed to preserve type safety!
subst :: Variable -> ABT a -> ABT b
subst x e body = 
    case fromABT body of
    Var z p
        | x == z    -> e
        | otherwise -> body
    Open z body'
        | x == z    -> e
        | otherwise -> 
            let z' = freshen z (freeVars e `mappend` freeVars body)
            in  open z' (subst x t (rename z z' body'))
    Syn body' -> syn (fmap (subst t x) body') -- BUG: AST is not Functor...

----------------------------------------------------------------
----------------------------------------------------------- fin.