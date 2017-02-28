{-# LANGUAGE CPP
           , DataKinds
           , InstanceSigs
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
    fmap31 f (Red_Fanout r1 r2)  = Red_Fanout (fmap31 f r1) (fmap31 f r2)
    fmap31 f (Red_Index n ix r)  = Red_Index (f n) (f ix) (fmap31 f r)
    fmap31 f (Red_Split b r1 r2) = Red_Split (f b) (fmap31 f r1) (fmap31 f r2)
    fmap31 _ Red_Nop             = Red_Nop
    fmap31 f (Red_Add h e)       = Red_Add h (f e)

instance Foldable31 Reducer where
    foldMap31 f (Red_Fanout r1 r2)  = foldMap31 f r1 `mappend` foldMap31 f r2
    foldMap31 f (Red_Index n ix r)  = f n `mappend` f ix `mappend` foldMap31 f r
    foldMap31 f (Red_Split b r1 r2) = f b `mappend` foldMap31 f r1 `mappend` foldMap31 f r2
    foldMap31 _ Red_Nop             = mempty
    foldMap31 f (Red_Add _ e)       = f e

instance Traversable31 Reducer where
    traverse31 f (Red_Fanout r1 r2)  = Red_Fanout <$> traverse31 f r1 <*> traverse31 f r2
    traverse31 f (Red_Index n ix r)  = Red_Index  <$> f n <*> f ix <*> traverse31 f r
    traverse31 f (Red_Split b r1 r2) = Red_Split <$> f b <*> traverse31 f r1 <*> traverse31 f r2
    traverse31 f Red_Nop             = pure Red_Nop
    traverse31 f (Red_Add h e)       = Red_Add h <$> f e


instance Eq2 abt => Eq1 (Reducer abt xs) where
    eq1 (Red_Fanout r1 r2)  (Red_Fanout r1' r2')   = eq1 r1 r1' && eq1 r2 r2'
    eq1 (Red_Index n ix r)  (Red_Index n' ix' r')  = eq2 n n' && eq2 ix ix' && eq1 r r'
    eq1 (Red_Split b r1 r2) (Red_Split b' r1' r2') = eq2 b b' && eq1 r1 r1' && eq1 r2 r2'
    eq1 Red_Nop             Red_Nop                = True
    eq1 (Red_Add _ e)       (Red_Add _ e')         = eq2 e e'
    eq1 _ _ = False

instance JmEq2 abt => JmEq1 (Reducer abt xs) where
    jmEq1 = jmEqReducer

jmEqReducer
  :: (JmEq2 abt)
  => Reducer abt xs a
  -> Reducer abt xs b
  -> Maybe (TypeEq a b)
jmEqReducer (Red_Fanout a b) (Red_Fanout a' b') = do
  Refl <- jmEqReducer a a'
  Refl <- jmEqReducer b b'
  return Refl
jmEqReducer (Red_Index s i r) (Red_Index s' i' r') = do
  (Refl, Refl) <- jmEq2 s s'
  (Refl, Refl) <- jmEq2 i i'
  Refl         <- jmEqReducer r r'
  return Refl
jmEqReducer (Red_Split b r s) (Red_Split b' r' s') = do
  (Refl, Refl) <- jmEq2 b b'
  Refl         <- jmEqReducer r r'
  Refl         <- jmEqReducer s s'
  return Refl
jmEqReducer Red_Nop Red_Nop = return Refl
jmEqReducer (Red_Add _ x) (Red_Add _ x') = do
  (Refl, Refl) <- jmEq2 x x'
  return Refl
jmEqReducer _ _ = Nothing

