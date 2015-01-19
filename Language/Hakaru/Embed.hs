{-# LANGUAGE 
    DeriveGeneric
  , ScopedTypeVariables
  , PolyKinds 
  , DeriveFunctor 
  , StandaloneDeriving
  , InstanceSigs 
  , UndecidableInstances
  #-}

module Language.Hakaru.Embed
  ( module Language.Hakaru.Syntax
  -- , module Generics.SOP 
  , module Language.Hakaru.Embed 
  ) where 

import Language.Hakaru.Syntax
import Prelude hiding (Real (..))
import Data.Proxy
import Control.Applicative
import Generics.SOP 
import qualified GHC.Generics as GHC 
import GHC.Exts (Constraint)

type family NAryFun (r :: * -> *) o (xs :: [*])  :: * 
type instance NAryFun r o '[]  = r o 
type instance NAryFun r o (x ': xs) = r x -> NAryFun r o xs 

newtype NFn r o x = NFn { unFn :: NAryFun r o x } 

type HRep repr a = NS (NP repr) (Code a) 

class Base repr => Embed (repr :: * -> *) where
  type Ctx repr t :: Constraint 

  hRep :: (Ctx repr t, Generic t) => repr (HRep repr t) -> repr t
  unHRep :: (Ctx repr t, Generic t) => repr t -> repr (HRep repr t) 

  sop' :: (xss ~ Code t, HasDatatypeInfo t) => Proxy t -> NS (NP repr) xss -> repr (NS (NP repr) xss)
  case' :: (xss ~ Code t, HasDatatypeInfo t) => Proxy t -> repr (NS (NP repr) xss) -> NP (NFn repr o) xss -> repr o 

case_ :: forall repr t o . (Ctx repr t, Embed repr, GenericInfo t) => repr t -> NP (NFn repr o) (Code t) -> repr o
case_ x f = case' (Proxy :: Proxy t) (unHRep x) f

sop :: forall repr t . (Ctx repr t, Embed repr, GenericInfo t) => NS (NP repr) (Code t) -> repr t 
sop x = hRep (sop' (Proxy :: Proxy t) x) 

type Embeddable r a = (Embed r, Ctx r a, GenericInfo a)
type GenericInfo x = (Generic x, HasDatatypeInfo x)

apNAry' :: NP f xs -> NAryFun f o xs -> f o 
apNAry' Nil z = z
apNAry' (x :* xs) f = apNAry' xs (f x) 

apNAry :: NS (NP f) xss -> NP (NFn f o) xss -> f o
apNAry (Z x) (NFn f :* _) = apNAry' x f 
apNAry (S x) (_ :* fs) = apNAry x fs 
apNAry _ Nil = error "type error" 
{-
apNAry (Z _) Nil = error "type error" 
apNAry (S _) Nil = error "type error" 
-}

ctrInfo :: DatatypeInfo xss -> NP ConstructorInfo xss 
ctrInfo (ADT _ _ c) = c
ctrInfo (Newtype _ _ c) = c :* Nil

data Dict p where Dict :: p => Dict p

ciSing :: ConstructorInfo xs -> Dict (SingI xs) 
ciSing (Infix {}) = Dict  
ciSing (Constructor {}) = Dict 
ciSing (Record {}) = Dict 

diSing :: DatatypeInfo xss -> Dict (SingI xss)
diSing (ADT _ _ cts) = go cts where 
  go :: NP ConstructorInfo xss -> Dict (SingI xss) 
  go Nil = Dict 
  go (x :* xs) = case (go xs, ciSing x) of (Dict, Dict) -> Dict  
diSing (Newtype {}) = Dict 

unprod :: (HCollapse h, HAp h, SingI xs) => (forall a . f a -> b) -> h f xs -> CollapseTo h b
unprod f = hcollapse . hliftA (K . f)

singTail :: Sing (x ': xs) -> Sing xs 
singTail SCons = sing 
