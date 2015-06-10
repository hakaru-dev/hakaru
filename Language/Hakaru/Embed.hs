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

import Language.Hakaru.Syntax
import Prelude hiding (Real (..))
import Data.List (intercalate, isPrefixOf, intersperse)
import Data.Proxy 
import Language.Haskell.TH.Syntax
import Language.Haskell.TH
import Generics.SOP (NS(..), NP(..), All, All2) 
import Control.Monad (replicateM)
import Control.Applicative
import Data.Char 
import Data.Typeable 

-- TODO: should this be polykinded rather than using (Hakaru *) explicitly?
-- type family   NAryFun (r :: Hakaru * -> *) (o :: Hakaru *) (xs :: [Hakaru *])  :: * 
-- type instance NAryFun r o '[]  = r o 
-- type instance NAryFun r o (x ': xs) = r x -> NAryFun r o xs 

type family   NAryFun (r :: Hakaru * -> *) (o :: Hakaru *) (a :: Hakaru *) (xs :: [HakaruFun *]) :: * 
type instance NAryFun r o a '[] = r o 
type instance NAryFun r o a (x ': xs) = r ('[ '[ x ] ] :$ a) -> NAryFun r o a xs 

newtype NFn (r :: Hakaru * -> *) (o :: Hakaru *) a x = NFn { unFn :: NAryFun r o a x } 

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

{-
This could be derived with the singletons package.  For now, a singleton
representation of Hakaru types in not needed, so the simpler version
which contains no information is used as a "dummy". 

data instance Sing (a :: Hakaru *) where 
  S_HInt :: Sing HInt 
  S_HReal :: Sing HReal 
  S_HProb :: Sing HProb 
  S_HMeasure :: Sing a -> Sing (HMeasure a)
  S_HArray :: Sing a -> Sing (HArray a)
  S_HFun :: Sing a -> Sing b -> Sing (HFun a b)
  S_HBool :: Sing HBool 
  S_HUnit :: Sing HUnit 
  S_HPair :: Sing a -> Sing b -> Sing (HPair a b)
  S_HEither :: Sing a -> Sing b -> Sing (HEither a b)
  S_HSOP :: Sing xss -> Sing (HSOP xss) 
  S_HTag :: Sing t -> Sing xss -> Sing t xss 
  S_HList :: Sing t -> Sing (HList t)
  S_HMaybe :: Sing t -> Sing (HMaybe t)
-}

data instance Sing (a :: Hakaru *) where SHakaru :: forall (a :: Hakaru *) . Sing a 
instance SingI (a :: Hakaru *) where sing = SHakaru 

nilTyCon, consTyCon :: TyCon 

#if __GLASGOW_HASKELL__ >= 708

deriving instance Typeable '[]
deriving instance Typeable '(:)

nilTyCon  = typeRepTyCon (typeRep (Proxy :: Proxy '[]))
consTyCon = typeRepTyCon (typeRep (Proxy :: Proxy '(:) ))

#else

-- This needs to be done by hand before ghc 7.8 because Typeable is not
-- polykinded

instance (Typeable t, All2 Typeable xss, SingI xss) => Typeable (Tag t xss) where 
  typeOf _ = mkTyConApp tagTyCon [ typeOf (undefined :: t) 
                                 , typeRepSing2 (sing :: Sing xss)
                                 ] 

nilTyCon  = mkTyCon3 "ghc-prim" "GHC.Types" "[]"
consTyCon = mkTyCon3 "ghc-prim" "GHC.Types" ":"
tagTyCon  = mkTyCon3 "hakaru" "Language.Hakaru.Embed" "Tag" 

typeRep :: forall a proxy . Typeable a => proxy a -> TypeRep 
typeRep _ = typeOf (undefined :: a) 

typeRepSing1 :: All Typeable xs => Sing xs -> TypeRep 
typeRepSing1 SNil = mkTyConApp nilTyCon []
typeRepSing1 (SCons x xs) = mkTyConApp consTyCon [ typeRep x, typeRepSing1 xs ]

typeRepSing2 :: All2 Typeable xss => Sing xss -> TypeRep 
typeRepSing2 SNil = mkTyConApp nilTyCon []
typeRepSing2 (SCons x xs) = mkTyConApp consTyCon [ typeRepSing1 x, typeRepSing2 xs ]

#endif

type Cons (x :: k) (xs :: [k]) = x ': xs 
type Nil = ('[] :: [k])

type EmbeddableConstraint t = 
  (SingI (Code t), All SingI (Code t), All2 SingI (Code t)) 

-- 't' is really just a "label" - 't' and 'Code t' are completely unrelated.
class (EmbeddableConstraint t) => Embeddable (t :: *) where 
  type Code t :: [[HakaruFun *]]
  datatypeInfo :: Proxy t -> DatatypeInfo (Code t)

data instance Sing (x :: HakaruFun k) where 
  S_Id :: Sing Id
  S_K  :: Sing a -> Sing (K a) 

instance SingI Id where sing = S_Id 
instance SingI a => SingI (K a) where sing = S_K sing 

-- Like Simplifiable in Language.Hakaru.Simplify, but `t' itself should not be
-- Simplifiable because it is not a Hakaru type - its type is only needed in the
-- context of `Tag t (Code t)'. This cannot be part of Embeddable itself because
-- it needs Simplifiable constraints on its type arguements, which should not be
-- required until `simplify' is actually called (ie, we don't want this
-- constraint while we are just building an expression in Haskell). 
class Embeddable t => SimplEmbed t where 
  mapleTypeEmbed :: t -> String 
  
class (Base repr) => Embed (repr :: Hakaru * -> *) where
  -- unit 
  _Nil :: repr ('[ '[] ] :$ a) 
  
  -- pair 
  _Cons :: repr ('[ '[ x ] ] :$ a) -> repr ('[ xs ] :$ a) -> repr ('[ x ': xs ] :$ a)
  
  -- unpair 
  caseProd :: repr ('[ x ': xs ] :$ a) -> (repr ('[ '[ x ] ] :$ a) -> repr ('[ xs ] :$ a) -> repr o) -> repr o 

  -- inl 
  _Z :: repr ('[ xs ] :$ a) -> repr ((xs ': xss) :$ a)

  -- inr 
  _S :: repr (xss :$ a) -> repr ((xs ': xss) :$ a)

  -- uneither
  caseSum :: repr ((xs ': xss) :$ a) 
          -> (repr ('[ xs ] :$ a) -> repr o) 
          -> (repr (xss :$ a) -> repr o) 
          -> repr o 

  -- void
  voidSOP :: repr ('[] :$ a) -> repr b
  voidSOP _ = error "Datatype with no constructors"
  
  -- Fixpoint 
  muE :: repr (f :$ HMu f) -> repr (HMu f)   
  unMuE :: repr (HMu f) -> repr (f :$ HMu f) 
  
  -- Constant type
  konst :: repr x -> repr ('[ '[ K x ] ] :$ a) 
  unKonst :: repr ('[ '[ K x ] ] :$ a) -> repr x 

  -- Identity type, representing recursive occurences of a type. 
  ident :: repr x -> repr ('[ '[ Id ] ] :$ x) 
  unIdent :: repr ('[ '[ Id ] ] :$ x) -> repr x 

  tag   :: Embeddable t => repr (HMu f) -> repr (HTag t f)
  untag :: Embeddable t => repr (HTag t f) -> repr (HMu f) 

  -- Naturality 
  natFn :: forall x y f . (repr x -> repr y) -> repr (f :$ x) -> repr (f :$ y) 
  
-- `HFunRep r a x' is isomorphic to `r (x a)`. 
data HFunRep (r :: Hakaru * -> *) (a :: Hakaru *) (x :: HakaruFun *) where 
  HFunRep :: r ('[ '[ x ] ] :$ a) -> HFunRep r a x 
  HFunI   :: r a -> HFunRep r a Id 
  HFunK   :: r x -> HFunRep r a (K x) 

unHFunRep :: Embed r => HFunRep r a x -> r ( '[ '[ x ] ] :$ a )
unHFunRep (HFunRep x) = x 
unHFunRep (HFunI x) = ident x 
unHFunRep (HFunK x) = konst x 

mapHFunRep :: Embed r => (r a -> r b) -> HFunRep r a x -> HFunRep r b x 
mapHFunRep f (HFunRep x) = HFunRep (natFn f x) 
mapHFunRep f (HFunI x) = HFunI (f x) 
mapHFunRep _ (HFunK x) = HFunK x 

-- Helpers / utilities
mapNS :: (forall a . r a -> r' a) -> NS r xs -> NS r' xs 
mapNS f (Z t) = Z (f t) 
mapNS f (S t) = S (mapNS f t) 

mapNP :: (forall a . r a -> r' a) -> NP r xs -> NP r' xs 
mapNP _ Nil = Nil 
mapNP f (x :* xs) = f x :* mapNP f xs 

-- NS f '[] is inhabited only by bottom.
void_ns :: NS f '[] -> a 
void_ns x = x `seq` undefined

singl :: f x -> NS (NP f) '[ '[ x ] ]
singl x = Z (x :* Nil) 

fromSingl :: NS (NP f) '[ '[ x ] ] -> f x 
fromSingl (Z (x :* Nil)) = x 
fromSingl x = x `seq` undefined

--- Generalized sum-of-products 
prodG :: Embed r => NP (HFunRep r a) xs -> r ( '[ xs ] :$ a) 
prodG Nil = _Nil 
prodG (x :* xs) = _Cons (unHFunRep x) (prodG xs)

sop' :: Embed repr => NS (NP (HFunRep repr a)) xss -> repr (xss :$ a) 
sop' (Z t) = _Z (prodG t) 
sop' (S t) = _S (sop' t) 

sop :: (Embeddable t, Embed repr) => NS (NP (HFunRep repr (HTag t (Code t)))) (Code t) -> repr (HTag t (Code t))
sop x = tag (muE (sop' (untagAll x))) where untagAll = mapNS (mapNP (mapHFunRep untag))

-- Generalized case on sum-of-products 
caseProdG :: Embed r => Sing xs -> r ('[ xs ] :$ a) -> NFn r o a xs -> r o 
caseProdG SNil _ (NFn x) = x 
caseProdG (SCons _ t) a (NFn f) = caseProd a (\x xs -> caseProdG t xs (NFn $ f x))

case' :: (All SingI xss, Embed repr) => repr (xss :$ a) -> NP (NFn repr o a) xss -> repr o
case' x (f :* fs) = caseSum x (\h -> caseProdG sing h f) (\t -> case' t fs) 
case' x Nil = voidSOP x 

case_ :: (Embeddable t, Embed repr) => repr (HTag t (Code t)) -> NP (NFn repr o (HTag t (Code t))) (Code t) -> repr o
case_ x f = case' (natFn tag $ unMuE $ untag x) f 

-- Variants of the above for when you want to fix the type of an application
-- (like when functions are being generated by TH) without writing a hideous
-- type signature by hand, or worse, having to generate it.
sopProxy :: (Embeddable t, Embed repr) => Proxy t -> NS (NP (HFunRep repr (HTag t (Code t)))) (Code t) -> repr (HTag t (Code t))
sopProxy _ = sop 

caseProxy :: (Embeddable t, Embed repr) => Proxy t -> repr (HTag t (Code t)) -> NP (NFn repr o (HTag t (Code t))) (Code t) -> repr o
caseProxy _ = case_


-- Possible useful for implementations like Sample
apNAry' :: Embed f => NP (HFunRep f a) xs -> NAryFun f o a xs -> f o 
apNAry' Nil z = z
apNAry' (x :* xs) f = apNAry' xs (f $ unHFunRep x) 

apNAry :: Embed f => NS (NP (HFunRep f a)) xss -> NP (NFn f o a) xss -> f o
apNAry (Z x) (NFn f :* _) = apNAry' x f 
apNAry (S x) (_ :* fs) = apNAry x fs 
apNAry _ Nil = error "type error" 

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

tyRealFresh :: DataDecl -> Q Type
tyRealFresh (DataDecl n tv _ ) = do 
  vars <- map VarT <$> replicateM (length tv) (newName "v")
  return $ foldl AppT (ConT . mkName . realName $ n) vars 

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
      guarded check deriv = if check cfg then deriv cfg d else return [] 
  diInfo <- deriveDatatypeInfo d
  ctrs   <- guarded mkCtrs     deriveCtrs
  accsrs <- guarded mkRecFuns  deriveAccessors
  htype  <- guarded mkTySyn    deriveHakaruType
  spcFns <- guarded mkSpecFuns deriveTypeSpecFuns
  simpl  <- deriveSimpl cfg d 
  return $ 
    (InstanceD [] (ConT (''Embeddable) `AppT` tyReal' (++"_Haskell") d)
                          (deriveCode d : diInfo)
    ) : htype ++ ctrs ++ accsrs ++ spcFns ++ simpl 

-- Create a SimplEmbed instance for the given type.
deriveSimpl :: Config -> DataDecl -> Q [Dec]
deriveSimpl _ d@(DataDecl nm tvs cs) = do 
  let tvsNames = map bndrName tvs 
      tvs' = map VarT tvsNames
      ctx = map (ClassP (mkName "Simplifiable") . (:[])) tvs' 
      mkArg n = do 
        x <- [| undefined :: $(varT n) |]
        return $ VarE (mkName "mapleType") `AppE` x 


  funB <- [|  $(stringE (realName nm))
              ++ "(" ++ concat $(listE $ intersperse [| "," |] (map mkArg tvsNames))
              ++ ")"
          |]

  return [InstanceD ctx (ConT (''SimplEmbed) `AppT` tyReal' (++"_Haskell") d) 
                    [FunD (mkName "mapleTypeEmbed") [Clause [WildP] (NormalB funB) []] ]
         ]

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

deriveCtrs, deriveAccessors, deriveHakaruType, deriveTypeSpecFuns :: Config -> DataDecl -> Q [Dec]

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

-- Produce functions which are identical to sop and case_ but whose type is specific
-- to the given datatype. For a datatype `data D x0 x1 .. xn = ...`, generate
--   mkD x = sopProxy (Proxy :: Proxy (HTypeRep (D x0 x1 .. xn))) x 
--   unD x = caseProxy (Proxy :: Proxy (HTypeRep (D x0 x1 .. xn))) x
-- A binding is generated on the LHS to avoid monomorphism restriction.
-- These functions serve to make programmer errors less likely (as opposed to
-- using sop and case_ directly).
deriveTypeSpecFuns cfg d@(DataDecl nm tv _) = do
  let ty = ForallT tv [] (ConT ''Proxy `AppT` tyReal' (++"_Haskell") d)
        
      mkFn funName calledFun = do 
        a <- newName "a" 
        b <- [| $(varE $ mkName calledFun) (Proxy :: $(return ty)) $(varE a) |]
        return (FunD (mkName funName) [ Clause [VarP a] (NormalB b) []] )

  sequence $ zipWith (\q -> mkFn (validateFnName $ q cfg $ show nm)) 
                     [mkCaseFun, mkSOPFun] 
                     ["caseProxy", "sopProxy"] 

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
        var    <- newName "a"
        reprTV <- newName "repr" 

        let getK = LamE (replicate k WildP ++ [VarP var] ++ replicate (q-k-1) WildP) 
                        (VarE var)
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


type HTypeRep (t :: *) = 'HTag t (Code t) 

-- Derive the Hakaru type synoym for the coressponding type.
deriveHakaruType cfg d@(DataDecl n tv _cs) = return 
  [ TySynD (mkName $ mkHakaruTy cfg $ realName n) 
           tv 
           (hakaruType d)
  ] 

hakaruType :: DataDecl -> Type 
hakaruType d = ConT (''HTypeRep) `AppT` tyReal' (++ "_Haskell") d

data Config = Config 
  { mkHakaruTy, mkHakaruFn, mkHakaruRec, mkSOPFun, mkCaseFun :: String -> String
  , mkCtrs, mkRecFuns, mkTySyn, mkSpecFuns :: Bool
  } 

defaultConfig :: Config 
defaultConfig = Config 
  { mkHakaruTy = id, mkHakaruFn = id, mkHakaruRec = id 
  , mkSOPFun = ("mk" ++), mkCaseFun = ("un" ++)
  , mkCtrs = True, mkRecFuns = True, mkTySyn = True, mkSpecFuns = True
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

