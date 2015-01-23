{-# LANGUAGE 
    CPP
  , DeriveGeneric
  , ScopedTypeVariables
  , PolyKinds 
  , DeriveFunctor 
  , StandaloneDeriving
  , InstanceSigs 
  , UndecidableInstances
  , DataKinds
  , TypeOperators
  , TypeFamilies
  , ConstraintKinds 
  , GADTs
  , RankNTypes 
  , QuasiQuotes 
  , TemplateHaskell
  #-}

module Language.Hakaru.Embed where

import Language.Hakaru.Syntax
import Prelude hiding (Real (..))
import Data.Proxy
import Control.Applicative
import Generics.SOP 
import qualified GHC.Generics as GHC 
import GHC.Exts (Constraint)
-- import qualified Language.Haskell.TH as TH
-- import Language.Haskell.TH (Name, Q, Dec(..), Type(..), Info (..), TyVarBndr(..), reify, TySynEqn(..))
import Language.Haskell.TH 
import GHC.Prim (Any)
import Unsafe.Coerce

type family NAryFun (r :: * -> *) o (xs :: [*])  :: * 
type instance NAryFun r o '[]  = r o 
type instance NAryFun r o (x ': xs) = r x -> NAryFun r o xs 

newtype NFn r o x = NFn { unFn :: NAryFun r o x } 

type HRep repr a = NS (NP repr) (Code a) 

class (Ctx repr Any, Base repr) => Embed (repr :: * -> *) where
  type Ctx repr t :: Constraint 

  hRep :: (Embeddable t, Generic t, Ctx repr t) => repr (HRep repr t) -> repr t
  unHRep :: (Embeddable t, Generic t, Ctx repr t) => repr t -> repr (HRep repr t) 

  sop' :: (xss ~ Code t, Embeddable t) => Proxy t -> NS (NP repr) xss -> repr (NS (NP repr) xss)
  case' :: (xss ~ Code t, Embeddable t) => Proxy t -> repr (NS (NP repr) xss) -> NP (NFn repr o) xss -> repr o 

case_ :: forall repr t o . (Embed repr, Embeddable t) => repr t -> NP (NFn repr o) (Code t) -> repr o
case_ x f = case ctxAny (Proxy :: Proxy repr) (Proxy :: Proxy t) Dict of 
              Dict -> case' (Proxy :: Proxy t) (unHRep x) f

sop :: forall repr t . (Embed repr, Embeddable t) => NS (NP repr) (Code t) -> repr t 
sop x = case ctxAny (Proxy :: Proxy repr) (Proxy :: Proxy t) Dict of 
          Dict -> hRep (sop' (Proxy :: Proxy t) x) 

class (Generic t, HasDatatypeInfo t) => Embeddable t where 
  -- Unsafely produce the constraint `Ctx r t' for any `t' given that
  -- there is a `Ctr r Any'.  This is only correct if `Ctx r t' doesn't
  -- pattern match on `t', and there is a `Ctx r t' for every `Embeddable t'
  ctxAny :: Proxy r -> Proxy t -> Dict (Ctx r Any) -> Dict (Ctx r t)
  ctxAny _ _ x = unsafeCoerce x 

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

ctrNames :: DatatypeInfo xss -> [ConstructorName]
ctrNames d = case diSing d of Dict -> unprod ctrName (ctrInfo d)

ctrName :: ConstructorInfo x -> ConstructorName
ctrName (Constructor x) = x
ctrName (Infix x _ _) = x
ctrName (Record x _) = x 

deriveEmbed :: Name -> Q [Dec] 
deriveEmbed ty = do 
  d0 <- emptyInstance ty (mkName "Generics.SOP.Generic")
  d1 <- emptyInstance ty (mkName "Generics.SOP.HasDatatypeInfo")
  d2 <- typeFamInstance (mkName "Language.Hakaru.Expect.Expect'")
                        []
                        ty
                        (ConT (mkName "Language.Hakaru.Expect.Expect") `AppT` 
                         ConT (mkName "Language.Hakaru.Maple.Maple"))

  v <- VarT <$> newName "v"
  d3 <- typeFamInstance (mkName "Language.Hakaru.Sample.Sample'")
                        [v]
                        ty
                        (ConT (mkName "Language.Hakaru.Sample.Sample") `AppT` v)

  d4 <- emptyInstance ty (mkName "Language.Hakaru.Embed.Embeddable")

  return [d0, d1, d2, d3, d4]


bndrName :: TyVarBndr -> Name
bndrName (PlainTV n) = n
bndrName (KindedTV n _) = n

tyReal :: Name -> Q (Type, [Type])
tyReal ty = do 
  info <- reify ty  
  return $ case info of 
    TyConI (DataD _ n tv _ _)    -> 
      let tv' = map (VarT . bndrName) tv in (foldl AppT (ConT n) tv', tv')
    TyConI (NewtypeD _ n tv _ _) -> 
      let tv' = map (VarT . bndrName) tv in (foldl AppT (ConT n) tv', tv')
    _ -> error "tyReal: supplied name not a plain datatype"

tyAny :: Name -> Q Type 
tyAny ty = do 
  (_, tvs) <- tyReal ty
  let tvsAny = replicate (length tvs) [t| GHC.Prim.Any |] 
  foldl appT (return $ ConT ty) tvsAny 

-- Generates an `instance C (T a0 a1 .. an)`, where a0 .. an are fresh.
emptyInstance :: Name   -- ^ Type name
              -> Name   -- ^ Type class name
              -> Q Dec  
emptyInstance ty cl = do
  (tyR, _) <- tyReal ty
  return $ InstanceD [] (AppT (ConT cl) tyR) []

-- Generates an instance like `type instance Ty TAuxs T = NS (NP (Ty' @ TAuxs)) (Code T)`. 
typeFamInstance :: Name -- ^ Ty
                -> [Type] -- ^ TAuxs
                -> Name -- ^ T
                -> Type -- ^ Ty' 
                -> Q Dec 
typeFamInstance tyFam tAuxs ty tyF = do
  (tyR, _) <- tyReal ty 
  t <- [t| NS (NP $(return tyF)) (Code $(return tyR)) |]
  return $ tySynInstantiate tyFam (tAuxs ++ [ tyR ]) t
  where
    tySynInstantiate fam ts r =
#if __GLASGOW_HASKELL__ >= 708
      -- GHC >= 7.8
      TySynInstD fam $ TySynEqn ts r
#elif __GLASGOW_HASKELL__ >= 706
      -- GHC >= 7.6 && < 7.8
      TySynInstD fam ts r
#else
#error "don't know how to compile for template-haskell < 2.7 (aka GHC < 7.6)"
#endif
