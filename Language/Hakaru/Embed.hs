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
    module Language.Hakaru.Embed,
    NS(..), NP(..), All, All2 
  ) where

import Language.Hakaru.Syntax hiding (EqType(..))
import Prelude hiding (Real (..))
import Data.Proxy 
import Language.Haskell.TH 
import Data.Typeable
import Generics.SOP (NS(..), NP(..), All, All2) 

type family NAryFun (r :: * -> *) o (xs :: [*])  :: * 
type instance NAryFun r o '[]  = r o 
type instance NAryFun r o (x ': xs) = r x -> NAryFun r o xs 

newtype NFn r o x = NFn { unFn :: NAryFun r o x } 

-- Sum of products tagged with a Haskell type 
data Tag (t :: *) (xs :: [[*]])

-- SOP xs = Sum of products of Hakaru tyeps 
data SOP (xs :: [[*]]) -- xs :: [[HakaruType]]

-- Datatype info, like in Generics.SOP but without all the ugly dictionaries.
data DatatypeInfo xss = DatatypeInfo 
  { datatypeName :: String 
  , ctrInfo :: NP ConstructorInfo xss 
  } deriving (Eq, Ord, Show) 

data ConstructorInfo xs = ConstructorInfo 
  { ctrName :: String 
  , fieldInfo :: Maybe (NP FieldInfo xs)
  } deriving (Eq, Ord, Show) 

data FieldInfo x = FieldInfo { fieldName :: String } deriving (Eq, Ord, Show) 

-- Singletons for lists. Like in Generics.SOP but again without the ugly
-- dictionary passing.
data family Sing (a :: k)

data instance Sing (xs :: [k]) where
  SNil  :: Sing '[]
  SCons :: Sing x -> Sing xs -> Sing (x ': xs)

data instance Sing (x :: *) where
  SStar :: Sing (x :: *)

class SingI (a :: k) where
  sing :: Sing a

instance SingI (x :: *) where
  sing = SStar

instance SingI '[] where
  sing = SNil

instance (SingI x, SingI xs) => SingI (x ': xs) where
  sing = SCons sing sing 

type EmbeddableConstraint t = 
  (SingI (Code t), All SingI (Code t), All2 SingI (Code t)) 

-- 't' is really just a "label" - 't' and 'Code t' are completely unrelated.
class EmbeddableConstraint t => Embeddable (t :: *) where 
  type Code t :: [[*]]
  datatypeInfo :: Proxy t -> DatatypeInfo (Code t)

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

  -- Doesn't permit recursive types, ie, the
  -- following produces an "infinite type" error:
  --   type Code [a] = '[ '[] , '[ a, Tag [a] (Code [a]) ]] 
  -- Also, the only valid (valid in the sense that tagging arbitrary values with
  -- abitrary types probably isn't useful) use of 'tag' is in 'sop' below,
  -- which constrains xss ~ Code t. But putting this constraint here would leave 
  -- us in the exact same position as 'hRep :: r (SOP (Code t)) -> r (HRep t)'.
  tag :: Embeddable t => repr (SOP xss) -> repr (Tag t xss)
  untag :: Embeddable t => repr (Tag t xss) -> repr (SOP xss) 


-- Sum of products and case in terms of basic functions 

prodG :: Embed r => NP r xs -> r (SOP '[ xs ]) 
prodG Nil = _Nil 
prodG (x :* xs) = _Cons x (prodG xs) 

caseProdG :: Embed r => Sing xs -> r (SOP '[ xs ]) -> NFn r o xs -> r o 
caseProdG SNil _ (NFn x) = x 
caseProdG (SCons _ t) a (NFn f) = caseProd a (\x xs -> caseProdG t xs (NFn $ f x))

sop' :: Embed repr => NS (NP repr) xss -> repr (SOP xss) 
sop' (Z t) = _Z (prodG t) 
sop' (S t) = _S (sop' t) 

case' :: (All SingI xss, Embed repr) => repr (SOP xss) -> NP (NFn repr o) xss -> repr o 
case' _ Nil = error "Datatype with no constructors" 
case' x (f :* fs) = caseSum x (\h -> caseProdG sing h f) (\t -> case' t fs)

sop :: (Embeddable t, Embed repr) => NS (NP repr) (Code t) -> repr (Tag t (Code t))
sop x = tag (sop' x)

case_ :: (Embeddable t, Embed repr) => repr (Tag t (Code t)) -> NP (NFn repr o) (Code t) -> repr o
case_ x f = case' (untag  x) f 

-- Possible useful for implementations like Sample
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

-- When datatypes are put in a [d|..|] quasiquote, the resulting names have
-- numbers appended with them. Get rid of those numbers for use with
-- datatypeInfo. TODO 
realName :: Name -> String 
realName = show 

-- Produce Embeddable code given the name of a datatype.
embeddable :: Name -> Q [Dec]
embeddable n = do 
  mbTy <- reifyDataDecl n 
  case mbTy of 
    Nothing -> error "Supplied name not a plain datatype."
    Just q  -> deriveEmbeddableG q 

-- Produce Embeddable code given given a splice corresponding to a datatype.
-- embeddable' [d| data Bool = True | False |]
embeddable' :: Q [Dec] -> Q [Dec]
embeddable' decsQ = do 
  decsQ >>= \decs -> 
    case decs of 
      [dec] | Just d <- maybeDataDecl dec -> fmap (dec :) (deriveEmbeddableG d)
      _ -> error "embeddable': supplied declarations not a single plain datatype declaration."

deriveEmbeddableG :: DataDecl -> Q [Dec] 
deriveEmbeddableG d@(DataDecl {}) = do 
  diInfo <- deriveDatatypeInfo d
  ctrs   <- deriveCtrs d
  accsrs <- deriveAccessors d
  return $ 
    (InstanceD [] (ConT (mkName "Embeddable") `AppT` tyReal d)
                          (deriveCode d : diInfo)
    ) : ctrs ++ accsrs

deriveDatatypeInfo :: DataDecl -> Q [Dec]
deriveDatatypeInfo (DataDecl _cx n _tv cs _der) = do 
  let diExp = foldr (\x xs -> [| $x :* $xs |]) [|Nil|] (map deriveCtrInfo cs)
  [d| datatypeInfo _ = DatatypeInfo  $(stringE $ realName n) $diExp |]

-- A value of type ConstructorInfo for the given constructor 
deriveCtrInfo :: Con -> Q Exp 
deriveCtrInfo (NormalC n _) = 
  [| ConstructorInfo $(stringE $ realName n) Nothing |]
deriveCtrInfo (RecC n nms) = [| ConstructorInfo 
  $(stringE $ realName n) 
  (Just $(foldr (\(x,_,_) xs -> [| $(stringE $ realName x) :* $xs |]) [|Nil|] nms)) 
  |]
deriveCtrInfo (InfixC  _ n _) = 
  [| ConstructorInfo $(stringE $ realName n) Nothing |]
deriveCtrInfo (ForallC {}) = error "Deriving Embeddable not supported for types with foralls."

deriveCtrs, deriveAccessors, deriveHakaruType :: DataDecl -> Q [Dec]

-- Deriving "constructor functions". TODO
deriveCtrs _ = return []

-- Deriving accessor functions for datatypes which are records and have a single
-- constructor. TODO
deriveAccessors _ = return [] 

type HTypeRep t = Tag t (Code t) 

-- Derive the Hakaru type synoym for the coressponding type. 
deriveHakaruType d@(DataDecl _cx n tv _cs _der) = return . (:[]) $ 
  TySynD (mkName $ mkHakaruNameTy $ realName n) tv (ConT (mkName "HTypeRep") `AppT` tyReal d)

-- This should probably be in some sort of configuration 
mkHakaruNameTy :: String -> String 
mkHakaruNameTy = ("H" ++ )

mkHakaruNameFn :: String -> String 
mkHakaruNameFn = id -- ("h" ++ )

-- Produces the Code type instance for the given type. 
deriveCode :: DataDecl -> Dec 
deriveCode d@(DataDecl _cx _n _tv cs _der) = 
  tySynInstanceD (mkName "Code") [tyReal d] . typeListLit . map typeListLit . map codeCon $ cs 
 
-- We never care about a kind 
bndrName :: TyVarBndr -> Name
bndrName (PlainTV n) = n
bndrName (KindedTV n _) = n

-- The "Code" for type 't' for one of its constructors. 
codeCon :: Con -> [Type] 
codeCon (NormalC _ tys)     = map snd tys 
codeCon (RecC    _ tys)     = map (\(_,_,x) -> x) tys 
codeCon (InfixC  ty0 _ ty1) = map snd [ty0, ty1] 
codeCon (ForallC {}) = error "Deriving Embeddable not supported for types with foralls."

-- Produces a type list literal from the given types.
typeListLit :: [Type] -> Type 
typeListLit = foldr (\x xs -> (PromotedConsT `AppT` x) `AppT` xs) PromotedNilT

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




{- Temporary home for this code which may useful in the future 

-- The simplest solution for eqHType is to just use Typeable. But for that
-- to work, we need polykinded Typeable (GHC 7.8), and having 
-- instance Typeable '[]
-- can expose unsafeCoerce (https://ghc.haskell.org/trac/ghc/ticket/9858)
-- The less simple (and terribly inefficient) solution is to use 
-- singletons and produce a real proof that two types are equal

data (a :: k) :~: (b :: k) where Refl :: a :~: a 

eqHType :: forall (a :: *) (b :: *) . HSing a -> HSing b -> Maybe (a :~: b) 
eqHType HProb HProb = Just Refl
eqHType HReal HReal = Just Refl
eqHType (HMeasure a) (HMeasure b) = 
  case eqHType a b of 
    Just Refl -> Just Refl 
    _ -> Nothing 

eqHType _ _ = Nothing 

eqHType1 :: forall (a :: [*]) (b :: [*]) . HSing a -> HSing b -> Maybe (a :~: b)
eqHType1 HNil HNil = Just Refl 
eqHType1 (HCons x xs) (HCons y ys) = 
  case (eqHType x y, eqHType1 xs ys) of 
    (Just Refl, Just Refl) -> Just Refl 
    _ -> Nothing 
eqHType1 _ _ = Nothing 

eqHType2 :: forall (a :: [[*]]) (b :: [[*]]) . HSing a -> HSing b -> Maybe (a :~: b)
eqHType2 HNil HNil = Just Refl 
eqHType2 (HCons x xs) (HCons y ys) = 
  case (eqHType1 x y, eqHType2 xs ys) of 
    (Just Refl, Just Refl) -> Just Refl 
    _ -> Nothing 
eqHType2 _ _ = Nothing 

data family HSing (a :: k)

data instance HSing (a :: *) where 
  HProb :: HSing Prob 
  HReal :: HSing Real 
  HMeasure :: HSing a -> HSing (Measure a)
  HArr :: HSing a -> HSing b -> HSing (a -> b)
  HPair :: HSing a -> HSing b -> HSing (a,b)
  -- etc .. 

data instance HSing (a :: [k]) where 
  HNil  :: HSing '[]
  HCons :: HSing x -> HSing xs -> HSing (x ': xs)
 
class HakaruType (a :: k) where 
  hsing :: HSing a 

instance HakaruType Prob where hsing = HProb 
instance HakaruType Real where hsing = HReal 
instance HakaruType a => HakaruType (Measure a) where hsing = HMeasure hsing 
instance (HakaruType a, HakaruType b) => HakaruType (a -> b) where hsing = HArr hsing hsing
instance (HakaruType a, HakaruType b) => HakaruType (a , b) where hsing = HPair hsing hsing 

instance HakaruType ('[] :: [*]) where hsing = HNil 
instance HakaruType ('[] :: [[*]]) where hsing = HNil 

instance (HakaruType x, HakaruType xs) => HakaruType (x ': xs :: [*]) where hsing = HCons hsing hsing
instance (HakaruType x, HakaruType xs) => HakaruType (x ': xs :: [[*]]) where hsing = HCons hsing hsing
-}
