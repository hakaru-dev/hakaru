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
  , FlexibleInstances
  #-}

module Language.Hakaru.Embed (
    module Language.Hakaru.Embed,
    NS(..), NP(..), All, All2, Proxy(..)
  ) where

import Language.Hakaru.Syntax hiding (EqType(..))
import Prelude hiding (Real (..))
import Data.List (intercalate, isPrefixOf)
import Data.Proxy 
import Language.Haskell.TH.Syntax
import Language.Haskell.TH
import Generics.SOP (NS(..), NP(..), All, All2) 
import Control.Monad (replicateM)
import Control.Applicative
import Data.Char 
import Data.Typeable 

type family NAryFun (r :: * -> *) o (xs :: [*])  :: * 
type instance NAryFun r o '[]  = r o 
type instance NAryFun r o (x ': xs) = r x -> NAryFun r o xs 

newtype NFn r o x = NFn { unFn :: NAryFun r o x } 

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

-- Sum of products tagged with a Haskell type 
data Tag (t :: *) (xs :: [[*]]) 

#if __GLASGOW_HASKELL__ >= 708

deriving instance Typeable '[]
deriving instance Typeable '(:)
deriving instance Typeable Tag 

#else

-- This needs to be done by hand before ghc 7.8 because Typeable is not
-- polykinded

instance (Typeable t, All2 Typeable xss, SingI xss) => Typeable (Tag t xss) where 
  typeOf _ = mkTyConApp tagTyCon [ typeOf (undefined :: t) 
                                 , typeRepSing2 (sing :: Sing xss)
                                 ] 

nilTyCon, consTyCon, tagTyCon :: TyCon 
nilTyCon = mkTyCon3 "ghc-prim" "GHC.Types" "[]"
consTyCon = mkTyCon3 "ghc-prim" "GHC.Types" ":"
tagTyCon = mkTyCon3 "hakaru" "Language.Hakaru.Embed" "Tag" 

typeRep :: forall a proxy . Typeable a => proxy a -> TypeRep 
typeRep _ = typeOf (undefined :: a) 

typeRepSing1 :: All Typeable xs => Sing xs -> TypeRep 
typeRepSing1 SNil = mkTyConApp nilTyCon []
typeRepSing1 (SCons x xs) = mkTyConApp consTyCon [ typeRep x, typeRepSing1 xs ]

typeRepSing2 :: All2 Typeable xss => Sing xss -> TypeRep 
typeRepSing2 SNil = mkTyConApp nilTyCon []
typeRepSing2 (SCons x xs) = mkTyConApp consTyCon [ typeRepSing1 x, typeRepSing2 xs ]

#endif

type Cons x xs = x ': xs 

replace :: forall a. Eq a => [a] -> [a] -> [a] -> [a]
replace str with = go where 
  n = length str 
  go [] = [] 
  go s@(x:xs) | str `isPrefixOf` s = let (_,b) = splitAt n s in with ++ go b
              | otherwise          = x : go xs 
    

hakaruTypeName :: forall t . Typeable t => Proxy t -> String 
hakaruTypeName _ = replace "_Haskell" "" $ show (typeRep (Proxy :: Proxy t))

mapleTypeTag :: forall t xss . (SingI xss, All2 Typeable xss, Typeable t) => Tag t xss -> String 
mapleTypeTag _ = concat 
  [ "Tagged(`" 
  , hakaruTypeName (Proxy :: Proxy t)
  , "`,"
  , typeList . map typeList $ go2 (sing :: Sing xss)
  , ")"
  ]

     where 
    
      typeList xs = "[" ++ intercalate "," xs ++ "]" 
    
      go2 :: All2 Typeable xs => Sing xs -> [[String]]
      go2 SNil = []
      go2 (SCons x xs) = go1 x : go2 xs 
    
      go1 :: All Typeable xs => Sing xs -> [String]
      go1 SNil = []
      go1 (SCons x xs) = show (typeRep x) : go1 xs 


type EmbeddableConstraint t = 
  (SingI (Code t), All SingI (Code t), All2 SingI (Code t)) 

-- 't' is really just a "label" - 't' and 'Code t' are completely unrelated.
class (EmbeddableConstraint t) => Embeddable (t :: *) where 
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

  -- void
  voidSOP :: repr (SOP '[]) -> repr a
  voidSOP _ = error "Datatype with no constructors"

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
case' x (f :* fs) = caseSum x (\h -> caseProdG sing h f) (\t -> case' t fs) 
case' x Nil = voidSOP x 

sop :: (Embeddable t, Embed repr) => NS (NP repr) (Code t) -> repr (Tag t (Code t))
sop x = tag (sop' x)

case_ :: (Embeddable t, Embed repr) => repr (Tag t (Code t)) -> NP (NFn repr o) (Code t) -> repr o
case_ x f = case' (untag  x) f 

-- Variants of the above for when you want to fix the type of an application
-- (like when functions are being generated by TH) without writing a hideous
-- type signature by hand, or worse, having to generate it.
sopProxy :: (Embeddable t, Embed repr) => Proxy t -> NS (NP repr) (Code t) -> repr (Tag t (Code t))
sopProxy _ = sop 

caseProxy :: (Embeddable t, Embed repr) => Proxy t -> repr (Tag t (Code t)) -> NP (NFn repr o) (Code t) -> repr o
caseProxy _ = case_

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

-- The TH syntax tree contains a lot of extra information we don't care
-- about. This contains the name of the datatype, the type variables it binds,
-- and a list of consructors for this type.
data DataDecl = DataDecl Name [TyVarBndr] [Con]

-- Given the function f and a datatype, produce the type representing the
-- datatype fully applied to its type variables, with the name of the datatype
-- modified by the given function.
tyReal' :: (String -> String) -> DataDecl -> Type 
tyReal' f (DataDecl n tv _ ) = foldl AppT (ConT . mkName . f . realName $ n) $ map (VarT . bndrName) tv

tyReal :: DataDecl -> Type 
tyReal = tyReal' id 

reifyDataDecl :: Name -> Q (Maybe DataDecl) 
reifyDataDecl ty = do  
  info <- reify ty 
  return $ case info of 
    TyConI t -> maybeDataDecl t 
    _ -> Nothing 

maybeDataDecl :: Dec -> Maybe DataDecl 
maybeDataDecl (DataD    _ n tv cs _) = Just $ DataDecl n tv cs  
maybeDataDecl (NewtypeD _ n tv c  _) = Just $ DataDecl n tv [c] 
maybeDataDecl _ = Nothing

-- Give a datatype `D x0 x1 .. xn = ...`, produce a datatype
--   data D_Haskell x0 x1 .. xn deriving Typeable 
toEmptyDec :: DataDecl -> Dec
toEmptyDec (DataDecl n tv _) = 
  DataD [] (mkName $ realName n ++ "_Haskell") tv [] [''Typeable]

-- When datatypes are put in a [d|..|] quasiquote, the resulting names have
-- numbers appended with them. Get rid of those numbers for use with
-- datatypeInfo. 
realName :: Name -> String 
realName (Name (OccName n) (NameU {})) = n
realName x = show x

realNameDecl :: DataDecl -> DataDecl 
realNameDecl (DataDecl n tv cs) = DataDecl (mkName $ realName n) tv cs 

-- Produce Embeddable code given given a splice corresponding to a datatype.
-- embeddableWith cfg [d| data Bool = True | False |]
embeddableWith :: Config -> Q [Dec] -> Q [Dec]
embeddableWith cfg decsQ = do 
  decsQ >>= \decs -> 
    case decs of 
      [dec] | Just d <- maybeDataDecl dec -> fmap (toEmptyDec d :) (deriveEmbeddable cfg d) 
      _ -> error "embeddable': supplied declarations not a single plain datatype declaration."

embeddable = embeddableWith defaultConfig

deriveEmbeddable :: Config -> DataDecl -> Q [Dec] 
deriveEmbeddable cfg d'@(DataDecl _ tvs _) = do 
  let d = realNameDecl d' 
  diInfo <- deriveDatatypeInfo d
  ctrs   <- if mkCtrs    cfg then deriveCtrs       cfg d else return [] 
  accsrs <- if mkRecFuns cfg then deriveAccessors  cfg d else return [] 
  htype  <- if mkTySyn   cfg then deriveHakaruType cfg d else return [] 
  return $ 
    (InstanceD [] (ConT (''Embeddable) `AppT` tyReal' (++"_Haskell") d)
                          (deriveCode d : diInfo)
    ) : htype ++ ctrs ++ accsrs

deriveDatatypeInfo :: DataDecl -> Q [Dec]
deriveDatatypeInfo (DataDecl n _tv cs) = do 
  diExp' <- [| DatatypeInfo  $(stringE $ realName n) $(np (map deriveCtrInfo cs)) |]
  return [FunD (mkName "datatypeInfo") [Clause [WildP] (NormalB diExp') []]]

-- A value of type ConstructorInfo for the given constructor 
deriveCtrInfo :: Con -> Q Exp 
deriveCtrInfo (NormalC n _) = 
  [| ConstructorInfo $(stringE $ realName n) Nothing |]
deriveCtrInfo (RecC n nms) = [| ConstructorInfo 
  $(stringE $ realName n) 
  (Just $(foldr (\(x,_,_) xs -> [| FieldInfo $(stringE $ realName x) :* $xs |]) [|Nil|] nms)) 
  |]
deriveCtrInfo (InfixC  _ n _) = 
  [| ConstructorInfo $(stringE $ realName n) Nothing |]
deriveCtrInfo (ForallC {}) = error "Deriving Embeddable not supported for types with foralls."

deriveCtrs, deriveAccessors, deriveHakaruType :: Config -> DataDecl -> Q [Dec]

-- For the given datatype, for each constructor of the form `C a0 a1 .. an :: T b0 b1 .. bn`, 
-- produce a function like 
--   mkC :: Embed r => r a0 -> r a1 -> r a2 -> .. -> r an -> r (HTypeRep (T b0 b1 .. bn))
--   mkC a0 a1 .. an = sop (S $ S .. S $ Z (a0 :* a1 :* .. :* an :* Nil))
deriveCtrs cfg d@(DataDecl _n _tv cs) = 
  fmap concat $ sequence (zipWith3 deriveCtr [0..] cs (codeCons d))
   where 
     ty = tyReal' id d 
     hTy = hakaruType d 

     deriveCtr :: Int -> Con -> [Type] -> Q [Dec] 
     deriveCtr conIndex con tyArgs = do 
       vars <- replicateM (length tyArgs) (newName "a")
       funB <- [| sop $(ns conIndex (np $ map varE vars)) |]

       reprTV <- newName "repr" 
       let funSig = ForallT (PlainTV reprTV : _tv) 
                            [ClassP ''Embed [reprVar]] 
                            (curryType $ map (AppT reprVar) $ tyArgs ++ [hTy])

           reprVar = VarT reprTV

           funName = mkName $ validateFnName $ mkHakaruFn cfg $ realName $ conName con

       return [ FunD funName [ Clause (map VarP vars) (NormalB funB) [] ]
              , SigD funName funSig 
              ]

-- Given a list [x0, x1 .. xn], produce the type x0 -> x1 -> .. -> xn 
curryType :: [Type] -> Type
curryType = foldr1 (\x xs -> ArrowT `AppT` x `AppT` xs) 

-- NAry product of a list of expressions
np :: [ExpQ] -> ExpQ
np = foldr (\x xs -> [| $x :* $xs |]) [| Nil |] 

-- NAry sum 
ns :: Int -> ExpQ -> ExpQ 
ns i e = iterate (\x -> [| S $x |]) [| Z $e |] !! i 

-- Name of a constructor 
conName :: Con -> Name
conName (NormalC n _)   = n
conName (RecC    n _)   = n
conName (InfixC  _ n _) = n
conName (ForallC _ _ c) = conName c

-- Deriving accessor functions for datatypes which are records and have a single
-- constructor. For a datatype `data D t0 t1 .. tn = C { r0 :: x0, r1 :: x1, .. , rn :: xn }`
-- produce the functions 
--   rkH :: Embed r => r (HTypeRep (D t0 t1 .. tn)) -> r xk
--   rkH x = case_ x (NFn (\x0 x1 .. xn -> xk) :* Nil)
-- for k in [0..n]. 
deriveAccessors cfg d@(DataDecl _n _tv [ RecC cn rcs ]) = 
  concat <$> mapM deriveAccessorK [0 .. q - 1] 
    where 
      ctr = cn 
      recs = map (\(n,_,_) -> n) rcs
      q = length recs
      hTy = hakaruType d 
      conTys = codeCon (RecC cn rcs) 

      deriveAccessorK :: Int -> Q [Dec]
      deriveAccessorK k = do 
        valueN <- newName "x"
        vars   <- replicateM q (newName "a")
        reprTV <- newName "repr" 

        let getK = LamE (map VarP vars) (VarE (vars !! k))
            funName = mkName $ validateFnName $ mkHakaruRec cfg $ realName $ recs !! k
            reprVar = VarT reprTV 

            funSig = ForallT (PlainTV reprTV : _tv) 
                             [ClassP ''Embed [reprVar]] 
                             (curryType $ map (AppT reprVar) $ [hTy, conTys !! k])

        funB   <- [| case_ $(varE valueN) 
                     $(return $ ConE '(:*) `AppE` (ConE 'NFn `AppE` getK) `AppE` ConE 'Nil)
                  |]
      
        return [ FunD funName [ Clause [VarP valueN] (NormalB funB) [] ]
               , SigD funName funSig 
               ]

deriveAccessors _ _ = return [] 


type HTypeRep t = Tag t (Code t) 

-- Derive the Hakaru type synoym for the coressponding type.
deriveHakaruType cfg d@(DataDecl n tv _cs) = return 
  [ TySynD (mkName $ mkHakaruTy cfg $ realName n) 
           tv 
           (hakaruType d)
  ] 

hakaruType :: DataDecl -> Type 
hakaruType d = ConT (''HTypeRep) `AppT` tyReal' (++ "_Haskell") d

data Config = Config 
  { mkHakaruTy, mkHakaruFn, mkHakaruRec :: String -> String
  , mkCtrs, mkRecFuns, mkTySyn :: Bool
  } 

defaultConfig :: Config 
defaultConfig = Config 
  { mkHakaruTy = id, mkHakaruFn = id, mkHakaruRec = id 
  , mkCtrs = True, mkRecFuns = True, mkTySyn = True 
  }

-- Produce a valid function name from a constructor name. 
validateFnName :: String -> String 
validateFnName (c:cs) | isAsciiUpper c = toLower c : cs 
                      | isAsciiLower c = c : cs 
validateFnName cs = '_' : cs

-- Produces the Code type instance for the given type. 
deriveCode :: DataDecl -> Dec 
deriveCode d = 
  tySynInstanceD (''Code) [tyReal' (++ "_Haskell") d] . typeListLit . map typeListLit . codeCons $ d

codeCons :: DataDecl -> [[Type]]
codeCons (DataDecl _n _tv cs) = map codeCon cs
 
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

typeListLit' :: [TypeQ] -> TypeQ
typeListLit' = foldr (\x xs -> [t| $x ': $xs |]) [t| '[] |] 

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


{-

data P2_Haskell (a_aZFo :: *) (b_aZFp :: *)
instance Embeddable (P2_Haskell a_aZFo b_aZFp) where
  type Code (P2_Haskell a_aZFo b_aZFp) = '[ '[ a_aZFo, b_aZFp]]
  datatypeInfo _
    = DatatypeInfo
        "P2"
        ((ConstructorInfo
            "P2"
            (Just ((FieldInfo "p2_fst") :* ((FieldInfo "p2_snd") :* Nil))))
         :* Nil)
type P2 a_aZFo b_aZFp = HTypeRep (P2_Haskell a_aZFo b_aZFp)

pair2 a_aZFq a_aZFr = sop (Z (a_aZFq :* (a_aZFr :* Nil)))
pair2 ::
  forall repr_aZFs a_aZFo b_aZFp. Embed repr_aZFs =>
  repr_aZFs a_aZFo
  -> repr_aZFs b_aZFp
     -> repr_aZFs (HTypeRep (P2_Haskell a_aZFo b_aZFp))

p2_fst x_aZFt
  = case_ x_aZFt ((:*) (NFn (\ a_aZFu a_aZFv -> a_aZFu)) Nil)
p2_fst ::
  forall repr_aZFw a_aZFo b_aZFp. Embed repr_aZFw =>
  repr_aZFw (HTypeRep (P2_Haskell a_aZFo b_aZFp)) -> repr_aZFw a_aZFo
p2_snd x_aZFx
  = case_ x_aZFx ((:*) (NFn (\ a_aZFy a_aZFz -> a_aZFz)) Nil)
p2_snd ::
  forall repr_aZFA a_aZFo b_aZFp. Embed repr_aZFA =>
  repr_aZFA (HTypeRep (P2_Haskell a_aZFo b_aZFp)) -> repr_aZFA b_aZFp

-}
