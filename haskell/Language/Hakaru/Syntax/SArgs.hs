{-# LANGUAGE CPP
           , DataKinds
           , PolyKinds
           , GADTs
           , RankNTypes
           , TypeOperators
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
module Language.Hakaru.Syntax.SArgs
  ( module Language.Hakaru.Syntax.SArgs
  ) where

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative (pure,(<$>),(<*>))
#endif

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing


-- | Locally closed values (i.e., not binding forms) of a given type.
-- TODO: come up with a better name
type LC (a :: Hakaru) = '( '[], a )

----------------------------------------------------------------
-- TODO: ideally we'd like to make SArgs totally flat, like tuples and arrays. Is there a way to do that with data families?
-- TODO: is there any good way to reuse 'List1' instead of defining 'SArgs' (aka @List2@)?

-- TODO: come up with a better name for 'End'
-- TODO: unify this with 'List1'? However, strictness differences...
--
-- | The arguments to a @(':$')@ node in the 'Term'; that is, a list
-- of ASTs, where the whole list is indexed by a (type-level) list
-- of the indices of each element.
data SArgs :: ([Hakaru] -> Hakaru -> *) -> [([Hakaru], Hakaru)] -> *
    where
    End :: SArgs abt '[]
    (:*) :: !(abt vars a)
        -> !(SArgs abt args)
        -> SArgs abt ( '(vars, a) ': args)

infixr 5 :* -- Chosen to match (:)

-- TODO: instance Read (SArgs abt args)

instance Show2 abt => Show1 (SArgs abt) where
    showsPrec1 _ End       = showString "End"
    showsPrec1 p (e :* es) =
        showParen (p > 5)
            ( showsPrec2 (p+1) e
            . showString " :* "
            . showsPrec1 (p+1) es
            )

instance Show2 abt => Show (SArgs abt args) where
    showsPrec = showsPrec1
    show      = show1

instance Eq2 abt => Eq1 (SArgs abt) where
    eq1 End       End       = True
    eq1 (x :* xs) (y :* ys) = eq2 x y && eq1 xs ys

instance Eq2 abt => Eq (SArgs abt args) where
    (==) = eq1

instance Functor21 SArgs where
    fmap21 f (e :* es) = f e :* fmap21 f es
    fmap21 _ End       = End

instance Foldable21 SArgs where
    foldMap21 f (e :* es) = f e `mappend` foldMap21 f es
    foldMap21 _ End       = mempty

instance Traversable21 SArgs where
    traverse21 f (e :* es) = (:*) <$> f e <*> traverse21 f es
    traverse21 _ End       = pure End


type SArgsSing = SArgs (Pointwise (Lift1 ()) Sing)

getSArgsSing
    :: forall abt xs m
     . (Applicative m)
    => (forall ys a . abt ys a -> m (Sing a))
    -> SArgs abt xs
    -> m (SArgsSing xs)
getSArgsSing k = traverse21 $ \x -> Pw (Lift1 ()) <$> k x
