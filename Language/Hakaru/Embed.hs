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
  , DefaultSignatures
  , FlexibleContexts
  #-}

module Language.Hakaru.Embed (
    module Language.Hakaru.Embed 
  , NP(..), NS(..), SingI(..), ConstructorInfo(..)
  , Sing(..), DatatypeInfo(..), FieldInfo(..), Proxy(..), lengthSing
  ) where

import Language.Hakaru.Syntax
import Prelude hiding (Real (..))
import Data.Proxy
import Control.Applicative
import Generics.SOP hiding (Code, Rep, datatypeInfo, Shape)
import qualified Generics.SOP as SOP 
import qualified GHC.Generics as GHC 
import GHC.Exts (Constraint)
-- import qualified Language.Haskell.TH as TH
-- import Language.Haskell.TH (Name, Q, Dec(..), Type(..), Info (..), TyVarBndr(..), reify, TySynEqn(..))
import Language.Haskell.TH 



type family NAryFun (r :: * -> *) o (xs :: [*])  :: * 
type instance NAryFun r o '[]  = r o 
type instance NAryFun r o (x ': xs) = r x -> NAryFun r o xs 

newtype NFn r o x = NFn { unFn :: NAryFun r o x } 

-- HRep = Hakaru Representation 
data HRep (t :: *) 

type family Shape (xs :: [k]) :: [k]  
type instance Shape '[] = '[]
type instance Shape (x ': xs) = (Shape x ': Shape xs) 
type instance Shape (x ': xs) = (() ': Shape xs) 

{-
-- This bunch of hideous boilerplate is because we want to avoid unsafeCoerce
-- (but it really is safe here)! All of "DataTypeInfo" and the like only pattern
-- match on the *shape* of the contents, not the actual types, so the following
-- is safe:
diToShape :: DatatypeInfo xss -> DatatypeInfo (Shape xss) 
diToShape = unsafeCoerce
diFromShape :: DatatypeInfo (Shape xss) -> DatatypeInfo xss
diFromShape = unsafeCoerce
-}

singShape :: forall (xs :: [*]) . Sing xs -> Dict (SingI (Shape xs))
singShape SNil = Dict 
singShape s@SCons = case singShape (singTail s) of Dict -> Dict 

singShape' :: forall (xs :: [[*]]) . Sing xs -> Dict (SingI (Shape xs))
singShape' SNil = Dict 
singShape' s@SCons = 
  case singShape' (singTail s) of { Dict -> 
  case singShape  (singHead s) of { Dict -> Dict }}

diInfoShape :: DatatypeInfo xss -> DatatypeInfo (Shape xss) 
diInfoShape (ADT x y xs) = ADT x y (npciInfoShape xs)
diInfoShape (Newtype x y xs) = Newtype x y (ciInfoShape xs)  

npciInfoShape :: NP ConstructorInfo xss -> NP ConstructorInfo (Shape xss)
npciInfoShape Nil = Nil 
npciInfoShape (x :* xs) = ciInfoShape x :* npciInfoShape xs 

npfiInfoShape :: NP FieldInfo xss -> NP FieldInfo (Shape xss)
npfiInfoShape Nil = Nil
npfiInfoShape (FieldInfo x :* xs) = FieldInfo x :* npfiInfoShape xs 

ciInfoShape :: forall xs . ConstructorInfo xs -> ConstructorInfo (Shape xs)
ciInfoShape (Constructor n) = case singShape (sing :: Sing xs) of 
                                Dict -> Constructor n 
ciInfoShape (Infix c a f) = Infix c a f 
ciInfoShape (Record n x) = case singShape (sing :: Sing xs) of 
                             Dict -> Record n (npfiInfoShape x)


-- 't' is really just a "label" - 't' and 'Code t' are completely unrelated.
class (SingI (Code t), SingI (Shape (Code t))) => Embeddable (t :: *) where 
  type Code t :: [[*]]
  datatypeInfo :: Proxy t -> DatatypeInfo (Shape (Code t))
  default datatypeInfo :: (HasDatatypeInfo t, Shape (SOP.Code t) ~ Shape (Code t)) 
                       => Proxy t -> DatatypeInfo (Shape (Code t))
  datatypeInfo p = diInfoShape $ SOP.datatypeInfo p

class (Base repr) => Embed (repr :: * -> *) where
  sop' :: (Embeddable t) => Proxy t -> NS (NP repr) (Code t) -> repr (HRep t) 
  case' :: (Embeddable t) => Proxy t -> repr (HRep t) -> NP (NFn repr o) (Code t) -> repr o
  
sop :: (Embed repr, Embeddable t) => NS (NP repr) (Code t) -> repr (HRep t)
sop = sop' Proxy 

case_ :: (Embed repr, Embeddable t) => repr (HRep t) -> NP (NFn repr o) (Code t) -> repr o
case_ = case' Proxy


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


-- Template Haskell

data DataDecl = DataDecl Cxt Name [TyVarBndr] [Con] [Name]

tyReal :: DataDecl -> Type 
tyReal (DataDecl _ n tv _ _ ) = foldl AppT (ConT n) $ map (VarT . bndrName) tv

reifyDataDecl :: Name -> Q (Maybe DataDecl) 
reifyDataDecl ty = do  
  info <- reify ty 
  return $ case info of 
    TyConI t -> maybeDataDecl t 
    _ -> Nothing 

maybeDataDecl :: Dec -> Maybe DataDecl 
maybeDataDecl (DataD    cx n tv cs der) = Just $ DataDecl cx n tv cs  der
maybeDataDecl (NewtypeD cx n tv c  der) = Just $ DataDecl cx n tv [c] der
maybeDataDecl _ = Nothing

toDec :: DataDecl -> Dec
toDec (DataDecl cx n tv cs der) = DataD cx n tv cs der

deriveEmbeddableG :: DataDecl -> [Dec] 
deriveEmbeddableG ty =   
  [ emptyInstance ty (mkName "Generics.SOP.Generic")
  , emptyInstance ty (mkName "Generics.SOP.HasDatatypeInfo")
  , deriveCode ty 
  ]

deriveEmbeddable :: Name -> Q [Dec] 
deriveEmbeddable ty = do 
  d <- reifyDataDecl ty 
  return $ maybe (error "tyReal: supplied name not a plain datatype") deriveEmbeddableG d 
  
-- Same as above, but takes a splice containing the datatype.
-- ` deriveEmbeddable' [d| data X ... |] `. 
deriveEmbeddable' :: Q [Dec] -> Q [Dec] 
deriveEmbeddable' decsQ = do 
  let replaceDeriving (DataDecl cx n tv cs _) = DataDecl cx n tv cs [mkName "GHC.Generics.Generic"] in 
    decsQ >>= \decs -> return $ 
      case decs of 
        [dec] | Just d <- maybeDataDecl dec -> toDec (replaceDeriving d) : deriveEmbeddableG d 
        _ -> error "deriveEmbeddable': supplied declarations not a single datatype declaration."

bndrName :: TyVarBndr -> Name
bndrName (PlainTV n) = n
bndrName (KindedTV n _) = n

-- Generates an `instance C (T a0 a1 .. an)`, where a0 .. an are fresh.
emptyInstance :: DataDecl -- ^ Type 
              -> Name     -- ^ Type class name
              -> Dec  
emptyInstance ty cl = InstanceD [] (AppT (ConT cl) (tyReal ty)) []

-- Produces the Code type instance for the given type. 
deriveCode :: DataDecl -> Dec 
deriveCode d@(DataDecl _cx _n _tv cs _der) = 
  let tyR = tyReal d
      mkCode  = typeListLit . map typeListLit . codeCons tyR 
      inst ts = InstanceD [] (AppT embeddableCl tyR) [tySynInstanceD (mkName "Code") [tyR] ts]
   in inst $ mkCode cs 
 
-- The "Code" for type 't' for one of its constructors. 
codeCon :: Type -> Con -> [Type] 
codeCon ty (NormalC _ tys)     = map (recType ty . snd) tys 
codeCon ty (RecC    _ tys)     = map (\(_,_,x) -> recType ty x) tys 
codeCon ty (InfixC  ty0 _ ty1) = map (recType ty . snd) [ty0, ty1] 
codeCon _ (ForallC {}) = error "Deriving Embeddable not supported for types with existential constructors."
  
-- Same as above, but for all constructors.
codeCons :: Type -> [Con] -> [[Type]] 
codeCons ty = map (codeCon ty) 

-- If the first and the second types are the same, return HRep applied to that
-- type. Else, return the 2nd type.
recType :: Type -> Type -> Type 
recType ty t | t == ty   = hrepCon `AppT` ty 
             | otherwise = t

-- Produces a type list literal from the given types.
typeListLit :: [Type] -> Type 
typeListLit = foldr (\x xs -> (PromotedConsT `AppT` x) `AppT` xs) PromotedNilT

-- Various names  
hrepCon :: Type 
hrepCon = ConT (mkName "Language.Hakaru.Embed.HRep")

embeddableCl :: Type
embeddableCl = ConT (mkName "Language.Hakaru.Embed.Embeddable")

tySynInstanceD :: Name -> [Type] -> Type -> Dec 
tySynInstanceD fam ts r = 
#if __GLASGOW_HASKELL__ >= 708
      -- GHC >= 7.8
      TySynInstD fam $ TySynEqn ts r
#elif __GLASGOW_HASKELL__ >= 706
      -- GHC >= 7.6 && < 7.8
      TySynInstD fam ts r
#else
#error "don't know how to compile for template-haskell < 2.7 (aka GHC < 7.6)"
#endif
