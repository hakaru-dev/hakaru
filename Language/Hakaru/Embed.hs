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
  , DeriveDataTypeable
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
import Generics.SOP hiding (Code, Rep, datatypeInfo, Shape, SOP)
import qualified Generics.SOP as SOP 
import qualified GHC.Generics as GHC 
import GHC.Exts (Constraint)
-- import qualified Language.Haskell.TH as TH
-- import Language.Haskell.TH (Name, Q, Dec(..), Type(..), Info (..), TyVarBndr(..), reify, TySynEqn(..))
import Language.Haskell.TH 
import Data.Typeable


type family NAryFun (r :: * -> *) o (xs :: [*])  :: * 
type instance NAryFun r o '[]  = r o 
type instance NAryFun r o (x ': xs) = r x -> NAryFun r o xs 

newtype NFn r o x = NFn { unFn :: NAryFun r o x } 

-- HRep = Hakaru Representation 
data HRep (t :: *) 

-- SOP xs = Sum of products of Hakaru tyeps 
data SOP (xs :: [[*]]) -- xs :: [[HakaruType]]

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

type EmbeddableConstraint t = 
  (SingI (Code t), SingI (Shape (Code t)), All SingI (Code t), HakaruType (Code t), Typeable t) 

-- 't' is really just a "label" - 't' and 'Code t' are completely unrelated.
class EmbeddableConstraint t => Embeddable (t :: *) where 
  type Code t :: [[*]]
  datatypeInfo :: Proxy t -> DatatypeInfo (Shape (Code t))
  default datatypeInfo :: (HasDatatypeInfo t, Shape (SOP.Code t) ~ Shape (Code t)) 
                       => Proxy t -> DatatypeInfo (Shape (Code t))
  datatypeInfo p = diInfoShape $ SOP.datatypeInfo p


class (Base repr) => Embed (repr :: * -> *) where
  -- unit 
  _Nil :: repr (SOP '[ '[] ]) 
  
  -- pair 
  _Cons :: repr x -> repr (SOP '[ xs ]) -> repr (SOP '[ x ': xs ])
  
  -- unpair 
  caseProd :: repr (SOP '[ x ': xs ]) -> (repr x -> repr (SOP '[ xs ]) -> repr o) -> repr o 

  -- inl 
  _Z :: repr (SOP '[ xs ]) -> repr (SOP (xs ': xss))

  -- inr 
  _S :: repr (SOP xss) -> repr (SOP (xs ': xss))

  -- uneither
  caseSum :: repr (SOP (xs ': xss)) 
          -> (repr (SOP '[ xs ]) -> repr o) 
          -> (repr (SOP xss) -> repr o) 
          -> repr o 

  {- 
     "tag" and "unTag". The type we really want is 
       hRep :: r (SOP (Code t)) -> r (HRep t)
     The problem is that 'Code' is really a function of the type *and* the repr,
     but if we include that in the type system, we have a constraint (or type family application)
     which mentions the 'repr', so it may not be able to exist inside existential type constructors.
     And the implemenation of 'Code (Expect r) t' is not obvious to me. 

     For representations which are not phantom types, like Disintegrate and Sample, it may
     be the case that this needs decidable equality on the finite(?) subset of *
     which we know as "Hakaru types". See 'eqHType' below. 

   -}

  hRep :: Embeddable t => repr (SOP xss) -> repr (HRep t)
  unHRep :: Embeddable t => repr (HRep t) -> repr (SOP xss)

  -- A "safer" variant, but the Nothing case will become 'error' at use sites
  -- anyways, so it probably isn't useful. 
  hRepS :: Embeddable t => Sing xss -> Maybe (repr (SOP xss) -> repr (HRep t))
  unHRepS :: Embeddable t => Sing xss -> Maybe (repr (HRep t) -> repr (SOP xss))

  -- A truely "safe" variant, but doesn't permit recursive types, ie, the
  -- following produces an "infinite type" error:
  --   type Code [a] = '[ '[] , '[ a, Tag [a] (Code [a]) ]] 
  -- Also, the only valid (valid in the sense that tagging arbitrary values with
  -- abitrary types probably isn't useful) use of 'tag' is in 'sopTag' below,
  -- which constrains xss ~ Code t. But putting this constraint here would leave 
  -- us in the exact same position as 'hRep :: r (SOP (Code t)) -> r (HRep t)'.
  tag :: Embeddable t => repr (SOP xss) -> repr (Tag t xss)
  untag :: Embeddable t => repr (Tag t xss) -> repr (SOP xss) 

data Tag (t :: *) (xss :: [[*]])


sop' :: Embed repr => NS (NP repr) xss -> repr (SOP xss) 
sop' (Z t) = _Z (prodG t) 
sop' (S t) = _S (sop' t) 

case' :: (All SingI xss, Embed repr) => repr (SOP xss) -> NP (NFn repr o) xss -> repr o 
case' _ Nil = error "Datatype with no constructors" 
case' x (f :* fs) = caseSum x (\h -> caseProdG sing h f) (\t -> case' t fs)

sop :: (Embeddable t, Embed repr) => NS (NP repr) (Code t) -> repr (HRep t)
sop x = hRep (sop' x)

case_ :: (Embeddable t, Embed repr) => repr (HRep t) -> NP (NFn repr o) (Code t) -> repr o 
case_ x f = case' (unHRep x) f 

sopTag :: (Embeddable t, Embed repr) => NS (NP repr) (Code t) -> repr (Tag t (Code t))
sopTag x = tag (sop' x)


-- The simplest solution for eqHType is to just use Typeable. But for that
-- to work, we need polykinded Typeable (GHC 7.8), and having 
-- instance Typeable '[]
-- can expose unsafeCoerce (https://ghc.haskell.org/trac/ghc/ticket/9858)
-- The less simple (and terribly inefficient) solution is to use 
-- singletons and produce a real proof that two types are equal


#if __GLASGOW_HASKELL__ < 708
   -- Before 7.8, :~: isn't in Data.Typeable 
data (a :: k) :~: (b :: k) where Refl :: a :~: a 
#endif


eqHType :: forall (a :: *) b . (HakaruType a, HakaruType b) => Maybe (a :~: b) 
eqHType = error "todo"

eqHType1 :: forall (a :: [*]) b . (HakaruType a, HakaruType b) => Maybe (a :~: b)
eqHType1 = error "todo"

eqHType2 :: forall (a :: [[*]]) b . (HakaruType a, HakaruType b) => Maybe (a :~: b)
eqHType2 = error "todo"

data family HSing (a :: k)

data instance HSing (a :: *) where 
  HProb :: HSing Prob 
  HReal :: HSing Real 
  -- etc .. 

data instance HSing (a :: [k]) where 
  HNil  :: HSing '[]
  HCons :: HSing x -> HSing xs -> HSing (x ': xs)
 
class HakaruType (a :: k) where 
  hsing :: HSing a 

instance HakaruType Prob where hsing = HProb 
instance HakaruType Real where hsing = HReal 

instance HakaruType '[] where hsing = HNil 
instance (HakaruType x, HakaruType xs) => HakaruType (x ': xs) where hsing = HCons hsing hsing


-- eqHType :: (HakaruType a, HakaruType b) => Maybe (a :~: b)
-- eqHType = eqT

-- class Typeable a => HakaruType (a :: k) where 

-- instance HakaruType Prob 
-- instance HakaruType Real 
-- -- etc 

-- deriving instance Typeable '[]
-- instance HakaruType ('[] :: [*])
-- instance HakaruType ('[] :: [[*]])
-- -- etc 

-- deriving instance Typeable HRep 
-- instance (Typeable t, Embeddable t) => HakaruType (HRep t)



prodG :: Embed r => NP r xs -> r (SOP '[ xs ]) 
prodG Nil = _Nil 
prodG (x :* xs) = _Cons x (prodG xs) 

caseProdG :: Embed r => Sing xs -> r (SOP '[ xs ]) -> NFn r o xs -> r o 
caseProdG SNil _ (NFn x) = x 
caseProdG s@SCons a (NFn f) = caseProd a (\x xs -> caseProdG (singTail s) xs (NFn $ f x))


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

singHead :: Sing (x ': xs) -> Sing x
singHead SCons = sing 

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
