{-# LANGUAGE CPP
           , DataKinds
           , GADTs
           , KindSignatures
           , Rank2Types
           , TypeOperators
           #-}

module Language.Hakaru.Syntax.Reducer where

import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Syntax.IClasses

#if __GLASGOW_HASKELL__ < 710
import           Data.Monoid   (Monoid(..))
#endif

data Reducer (abt :: [Hakaru] -> Hakaru -> *)
             (xs  :: [Hakaru])
             (a :: Hakaru) where
     Red_Fanout
         :: Reducer abt xs a
         -> Reducer abt xs b
         -> Reducer abt xs (HPair a b)
     Red_Index
         :: abt xs 'HNat                 -- size of resulting array
         -> abt ( 'HNat ': xs) 'HNat     -- index into array (bound i)
         -> Reducer abt ( 'HNat ': xs) a -- reduction body (bound b)
         -> Reducer abt xs ('HArray a)
     Red_Split
         :: abt ( 'HNat ': xs) HBool     -- (bound i)
         -> Reducer abt xs a
         -> Reducer abt xs b
         -> Reducer abt xs (HPair a b)
     Red_Nop
         :: Reducer abt xs HUnit
     Red_Add
         :: HSemiring a
         -> abt ( 'HNat ': xs) a         -- (bound i)
         -> Reducer abt xs a

instance Functor31 Reducer where
    fmap31 _ Red_Nop       = Red_Nop
    fmap31 f (Red_Add h e) = Red_Add h (f e)

instance Foldable31 Reducer where
    foldMap31 f (Red_Fanout r1 r2)  = foldMap31 f r1 `mappend` foldMap31 f r2
    foldMap31 f (Red_Index n ix r)  = f n `mappend` f ix `mappend` foldMap31 f r
    foldMap31 f (Red_Split b r1 r2) = f b `mappend` foldMap31 f r1 `mappend` foldMap31 f r2
    foldMap31 _ Red_Nop             = mempty
    foldMap31 f (Red_Add _ e)       = f e
