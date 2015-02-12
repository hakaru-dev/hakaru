{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances,
    TypeFamilies, StandaloneDeriving, GeneralizedNewtypeDeriving, GADTs,
    RankNTypes, ScopedTypeVariables, UndecidableInstances, TypeOperators, DataKinds, InstanceSigs #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Expect (Expect(..), Expect', total, normalize) where

-- Expectation interpretation

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Real, Prob, Measure, Vector,
       Order(..), Base(..), Mochastic(..), Integrate(..), Lambda(..),
       fst_, snd_, sumVec, mapV)
-- import qualified Generics.SOP as SOP
-- import Generics.SOP (HasDatatypeInfo, Generic)
-- import GHC.Generics (Generic)
-- import Data.Typeable
import Language.Hakaru.Embed

newtype Expect repr a = Expect { unExpect :: repr (Expect' a) }
type family Expect' (a :: *)
-- This type family must be changed in lockstep with typeExpect below
type instance Expect' Int          = Int
type instance Expect' Real         = Real
type instance Expect' Prob         = Prob
type instance Expect' Bool         = Bool
type instance Expect' ()           = ()
type instance Expect' (a, b)       = (Expect' a, Expect' b)
type instance Expect' (Either a b) = Either (Expect' a) (Expect' b)
type instance Expect' [a]          = [Expect' a]
type instance Expect' (Vector a)   = Vector (Expect' a)
type instance Expect' (Measure a)  = (Measure (Expect' a),
                                      (Expect' a -> Prob) -> Prob)
type instance Expect' (a -> b)     = (Expect' a -> Expect' b)

instance (Order repr Real) => Order (Expect repr) Real where
  less  (Expect x) (Expect y) = Expect (less  x y)
  equal (Expect x) (Expect y) = Expect (equal x y)

deriving instance (Eq         (repr Real)) => Eq         (Expect repr Real)
deriving instance (Ord        (repr Real)) => Ord        (Expect repr Real)
deriving instance (Num        (repr Real)) => Num        (Expect repr Real)
deriving instance (Fractional (repr Real)) => Fractional (Expect repr Real)
deriving instance (Floating   (repr Real)) => Floating   (Expect repr Real)

instance (Order repr Prob) => Order (Expect repr) Prob where
  less  (Expect x) (Expect y) = Expect (less  x y)
  equal (Expect x) (Expect y) = Expect (equal x y)

deriving instance (Eq         (repr Prob)) => Eq         (Expect repr Prob)
deriving instance (Ord        (repr Prob)) => Ord        (Expect repr Prob)
deriving instance (Num        (repr Prob)) => Num        (Expect repr Prob)
deriving instance (Fractional (repr Prob)) => Fractional (Expect repr Prob)

instance (Order repr Int) => Order (Expect repr) Int where
  less  (Expect x) (Expect y) = Expect (less  x y)
  equal (Expect x) (Expect y) = Expect (equal x y)

deriving instance (Eq  (repr Int)) => Eq  (Expect repr Int)
deriving instance (Ord (repr Int)) => Ord (Expect repr Int)
deriving instance (Num (repr Int)) => Num (Expect repr Int)

instance (Base repr) => Base (Expect repr) where
  unit                           = Expect unit
  pair (Expect a) (Expect b)     = Expect (pair a b)
  unpair (Expect ab) k           = Expect (unpair ab (\a b ->
                                   unExpect (k (Expect a) (Expect b))))
  inl (Expect a)                 = Expect $ inl a
  inr (Expect b)                 = Expect $ inr b
  uneither (Expect ab) ka kb     = Expect $ uneither ab (unExpect . ka . Expect)
                                                        (unExpect . kb . Expect)
  true                           = Expect true
  false                          = Expect false
  if_ eb (Expect et) (Expect ef) = Expect $ if_ (unExpect eb) et ef

  nil                            = Expect nil
  cons (Expect a) (Expect as)    = Expect $ cons a as
  unlist (Expect as) kn kc       = Expect $ unlist as (unExpect kn) (\a' as' ->
                                   unExpect (kc (Expect a') (Expect as')))

  unsafeProb                     = Expect . unsafeProb . unExpect
  fromProb                       = Expect . fromProb   . unExpect
  fromInt                        = Expect . fromInt    . unExpect
  pi_                            = Expect pi_
  exp_                           = Expect . exp_  . unExpect
  log_                           = Expect . log_  . unExpect
  sqrt_                          = Expect . sqrt_ . unExpect
  erf                            = Expect . erf   . unExpect
  erf_                           = Expect . erf_  . unExpect
  pow_ (Expect x) (Expect y)     = Expect (pow_ x y)
  infinity                       = Expect infinity
  negativeInfinity               = Expect negativeInfinity
  gammaFunc (Expect n)           = Expect (gammaFunc n)
  betaFunc (Expect a) (Expect b) = Expect (betaFunc a b)

  vector (Expect l) (Expect h) f = Expect (vector l h (unExpect . f . Expect))
  empty                          = Expect empty
  index (Expect v) (Expect i)    = Expect (index v i)
  loBound (Expect v)             = Expect (loBound v)
  hiBound (Expect v)             = Expect (hiBound v)
  reduce r (Expect z) (Expect v) = Expect (reduce r' z v)
    where r' a b = unExpect (r (Expect a) (Expect b))

  fix f                          = Expect (fix (unExpect . f . Expect))

instance (Integrate repr) => Integrate (Expect repr) where
  integrate (Expect lo) (Expect hi) f =
    Expect (integrate lo hi (unExpect . f . Expect))
  summate (Expect lo) (Expect hi) f =
    Expect (summate lo hi (unExpect . f . Expect))

reflectPair :: (Lambda repr) =>
               (a -> (a -> repr w) -> repr w) ->
               (b -> (b -> repr w) -> repr w) ->
               (a,b) -> ((a,b) -> repr w) -> repr w
reflectPair ra rb (a,b) c = ra a (\a' -> rb b (\b' -> c (a',b')))

reflectList :: (Lambda repr) =>
               (a -> (a -> repr w) -> repr w) ->
               [a] -> ([a] -> repr w) -> repr w
reflectList _  []     c = c []
reflectList ra (a:as) c = ra a (\a' -> reflectList ra as (\as' -> c (a':as')))

reflect :: (Lambda repr) =>
           [(Expect repr a, Expect repr b)] ->
           ([(repr (Expect' a), repr (Expect' b))] -> repr w) -> repr w
reflect ab_s = reflectList (reflectPair let_ let_)
                 [ (a,b) | (Expect a, Expect b) <- ab_s ]

instance (Mochastic repr, Integrate repr, Lambda repr)
      => Mochastic (Expect repr) where
  dirac (Expect a) = Expect $ let_ a $ \a' -> pair
    (dirac a')
    (lam (\c -> c `app` a'))
  bind (Expect m) k =
    Expect $ let_ (lam (unExpect . k . Expect)) $ \k' ->
             unpair m $ \m1 m2 ->
             pair (bind m1 (fst_ . app k'))
                  (lam (\c -> m2 `app` lam (\a -> snd_ (app k' a) `app` c)))
  lebesgue = Expect $ pair
    lebesgue
    (lam (integrate negativeInfinity infinity . app))
  counting = Expect $ pair
    counting
    (lam (summate   negativeInfinity infinity . app))
  superpose pms = Expect $ reflect pms $ \pms -> pair
    (superpose [ (p, fst_ m) | (p, m) <- pms ])
    (lam (\c -> sum [ p * app (snd_ m) c | (p, m) <- pms ]))
  uniform (Expect lo) (Expect hi) = Expect $ pair
    (uniform lo hi)
    (lam (\f -> integrate lo hi (\x -> app f x / unsafeProb (hi - lo))))
  normal (Expect mu) (Expect sd) = Expect $ pair
    (normal mu sd)
    (lam (\c -> integrate negativeInfinity infinity (\x ->
     exp_ (- (x - mu)^(2::Int) / fromProb (2 * pow_ sd 2))
     / sd / sqrt_ (2 * pi_) * app c x)))
  mix (Expect pms) = Expect $ pair
    (mix (mapV (\ pm -> unpair pm (\ p m -> pair p (fst_ m))) pms))
    (lam (\c -> sumVec (mapV (\ pm -> unpair pm (\ p m ->  p * app (snd_ m) c)) pms)
                / sumVec (mapV fst_ pms)))
  categorical (Expect pxs) = Expect $ pair
    (categorical pxs)
    (lam (\c -> sumVec (mapV (\pm -> unpair pm (\ p x ->  p * app c x)) pxs)
                / sumVec (mapV fst_ pxs)))
  poisson (Expect l) = Expect $ pair
    (poisson l)
    (lam (\c -> flip (if_ (less 0 l)) 0 (summate 0 infinity (\x ->
     pow_ l (fromInt x) / gammaFunc (fromInt x + 1) / exp_ (fromProb l)
     * app c x))))
  gamma (Expect shape) (Expect scale) = Expect $ pair
    (gamma shape scale)
    (lam (\c -> integrate 0 infinity (\x ->
     let x_ = unsafeProb x
         shape_ = fromProb shape in
     (pow_ x_ (fromProb (shape - 1)) * exp_ (- fromProb (x_ / scale))
      / (pow_ scale shape_ * gammaFunc shape_) * app c (unsafeProb x)))))
  beta (Expect a) (Expect b) = Expect $ pair
    (beta a b)
    (lam (\c -> integrate 0 1 (\x -> pow_ (unsafeProb x    ) (fromProb a - 1)
                                   * pow_ (unsafeProb (1-x)) (fromProb b - 1)
                                   / betaFunc a b * app c (unsafeProb x))))

instance (Lambda repr) => Lambda (Expect repr) where
  lam f = Expect (lam (unExpect . f . Expect))
  app (Expect rator) (Expect rand) = Expect (app rator rand)

total :: (Lambda repr, Base repr) => Expect repr (Measure a) -> repr Prob
total (Expect m) = unpair m (\_ m2 -> m2 `app` lam (\_ -> 1))

normalize :: (Integrate repr, Lambda repr, Mochastic repr) =>
             Expect repr (Measure a) -> repr (Measure (Expect' a))
normalize (Expect m) = unpair m (\m1 m2 ->
  superpose [(recip (m2 `app` lam (\_ -> 1)), m1)])


-- type family ListToTy (a :: [*]) :: *
-- type instance ListToTy '[] = ()
-- type instance ListToTy (x ': xs) = (Expect' x, ListToTy xs)

-- type family ListToTy2 (a :: [[*]]) :: *
-- type instance ListToTy2 '[] = Void
-- type instance ListToTy2 (x ': xs) = Either (ListToTy x) (ListToTy2 xs)

-- type instance Expect' Void = Void
-- type instance Expect' (HRep t) = ListToTy2 (Code t)

-- {- This should probably be in Base -}
-- data Void
-- absurd :: Base r => r Void -> r a
-- absurd = error "absurd"

-- prodExpect :: Base r => NP (Expect r) xs -> r (ListToTy xs)
-- prodExpect Nil = unit
-- prodExpect (Expect x :* xs) = pair x (prodExpect xs)

-- sopExpect :: Base r => NS (NP (Expect r)) xss -> r (ListToTy2 xss)
-- sopExpect (Z t) = inl (prodExpect t)
-- sopExpect (S (t :: NS (NP (Expect r)) xss')  ) = inr (sopExpect t :: r (ListToTy2 xss'))

-- caseExpect1 :: forall r xs o . Base r => NP Proxy xs -> r (ListToTy xs) -> NFn (Expect r) o xs -> r (Expect' o)
-- caseExpect1 Nil x (NFn (Expect y)) = ununit x y
-- caseExpect1 ((_t :: Proxy x) :* (ts :: NP Proxy xs1)) x (NFn y) = unpair x (\a b -> q1 b (NFn (y (Expect a)))) where

--   q1 :: r (ListToTy xs1) -> NFn (Expect r) o xs1 -> r (Expect' o)
--   q1 = caseExpect1 ts

-- singNP :: forall xs . SingI xs => NP Proxy xs
-- singNP = case sing :: Sing xs of
--            SNil -> Nil
--            SCons -> Proxy :* singNP

-- caseExpect :: forall r o xss . (Base r, SOP.All SingI xss)
--            => r (ListToTy2 xss) -> NP (NFn (Expect r) o) xss -> r (Expect' o)
-- caseExpect x Nil = absurd x
-- caseExpect x ((t :: NFn (Expect r) o xs) :* (ts :: NP (NFn (Expect r) o) xss')) =
--   uneither x (\a -> caseExpect1 singNP a t) (\a -> caseExpect a ts)

-- instance Base r => Embed (Expect r) where
--   sop' _ a = Expect (sopExpect a)
--   case' _ (Expect a) f = Expect (caseExpect a f)



type family MapExpect' (a :: [*]) :: [*]
type instance MapExpect' '[] = '[]
type instance MapExpect' (x ': xs) = (Expect' x ': MapExpect' xs)

type family MapExpect'2 (a :: [[*]]) :: [[*]]
type instance MapExpect'2 '[] = '[]
type instance MapExpect'2 (x ': xs) = MapExpect' x ': MapExpect'2 xs

-- type instance Expect' Void = Void
type instance Expect' (HRep t) = HRep t
type instance Expect' (SOP xss) = SOP (MapExpect'2 xss)

expectHType :: HSing x -> Dict (HakaruType (Expect' x))
expectHType HReal = Dict
expectHType HProb = Dict
expectHType (HMeasure a) = case expectHType a of Dict -> Dict
expectHType (HArr a b) = dictPair (expectHType a) (expectHType b) Dict
expectHType (HPair a b) = dictPair (expectHType a) (expectHType b) Dict

expectHType1 :: HSing xs -> Dict (HakaruType (MapExpect' xs))
expectHType1 HNil = Dict
expectHType1 (HCons x xs) =
  case (expectHType x, expectHType1 xs) of
    (Dict, Dict) -> Dict

expectHType2 :: HSing xss -> Dict (HakaruType (MapExpect'2 xss))
expectHType2 HNil = Dict
expectHType2 (HCons x xs) =
  case (expectHType1 x, expectHType2 xs) of
    (Dict, Dict) -> Dict

type instance Expect' (Tag t xss) = Tag t (MapExpect'2 xss)

instance Embed r => Embed (Expect r) where
  _Nil = Expect _Nil
  _Cons (Expect x) (Expect xs) = Expect (_Cons x xs)

  caseProd (Expect x) f = Expect (caseProd x (\y ys -> unExpect $ f (Expect y) (Expect ys)))

  _Z (Expect x) = Expect (_Z x)
  _S (Expect x) = Expect (_S x)

  caseSum (Expect x) caseZ caseS = Expect (caseSum x (unExpect . caseZ . Expect) (unExpect . caseS . Expect))

  untag (Expect x) = Expect (untag x)
  tag (Expect x) = Expect (tag x)



