-- TODO: <https://git-scm.com/book/en/v2/Git-Branching-Basic-Branching-and-Merging>
{-# LANGUAGE RankNTypes, TypeFamilies, DataKinds #-}

module Language.Hakaru.Syntax.ABT where

import Language.Hakaru.Syntax.DataKind

----------------------------------------------------------------
-- <http://semantic-domain.blogspot.co.uk/2015/03/abstract-binding-trees.html>
-- <http://semantic-domain.blogspot.co.uk/2015/03/abstract-binding-trees-addendum.html>
-- <https://gist.github.com/neel-krishnaswami/834b892327271e348f79>
-- | Abstract binding trees, to separate out variables/binders from the rest of the syntax.
data View :: (Hakaru * -> *) -> Hakaru * -> * where
    Var  :: Variable -> Proxy a -> View rec a
    Open :: Variable -> rec a -> View rec a
    Syn  :: AST (rec a) -> View rec a

vmap :: (forall b. rec b -> rec' b) -> View rec a -> View rec' a
vmap f (Var  x p) = Var  x p
vmap f (Open x t) = Open x (f t)
vmap f (Syn  t)   = Syn  (fmap f t)

-- a~la neelk
-- TODO: replace @Set Variable@ with @Map Variable (Hakaru Star)@; though that belongs more in the type-checking than in the ABT itself...
data ABT (a :: Hakaru *) = ABT (Set Variable) (View (ABT a) a)

freeVars :: ABT a -> Set Variable
freeVars (ABT vs _) = vs

fromABT :: ABT a -> View (ABT a) a
fromABT (ABT _ e) = e

toABT :: View (ABT a) a -> ABT a
toABT (Var  x p) = var  x p
toABT (Open x t) = open x t
toABT (Syn  t)   = syn  t

var :: Variable -> Proxy a -> ABT a
var x p = ABT (Set.singleton x) (Var x p)

open :: Variable -> ABT a -> ABT a
open x e = ABT (Set.remove z (freeVars e)) (Open x e)

syn :: AST (ABT a) -> ABT a
syn e = ABT (Set.union (fmap freeVars e)) (Syn e)

freshen :: Set Variable -> Variable -> Variable
freshen v vs
    | v `elem` vs = freshen (v ++"'") vs
    | otherwise   = v

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
    Syn e'          -> syn (fmap (rename x y) e')

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
            let z' = freshen z (Set.union (freeVars e) (freeVars body))
            in  open z' (subst x t (rename z z' body'))
    Syn body' -> syn (F.map (subst t x) body')

----------------------------------------------------------------
----------------------------------------------------------- fin.