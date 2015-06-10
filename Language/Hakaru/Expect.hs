{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances,
    TypeFamilies, StandaloneDeriving, GeneralizedNewtypeDeriving, GADTs,
    RankNTypes, ScopedTypeVariables, UndecidableInstances, TypeOperators, DataKinds, InstanceSigs #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Expect (Expect(..), Expect', total, normalize) where

-- Expectation interpretation

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Hakaru(..), HakaruFun(..), 
       Order(..), Base(..), Mochastic(..), Integrate(..), Lambda(..),
       fst_, snd_, summateV, mapWithIndex)
-- import qualified Generics.SOP as SOP
-- import Generics.SOP (HasDatatypeInfo, Generic)
-- import GHC.Generics (Generic)
-- import Data.Typeable
import Language.Hakaru.Embed

newtype Expect (repr :: Hakaru * -> *) (a :: Hakaru *) =
    Expect { unExpect :: repr (Expect' a) }

type family   Expect' (a :: Hakaru *) :: Hakaru *
-- This type family must be changed in lockstep with typeExpect below
type instance Expect' HInt          = HInt 
type instance Expect' HReal         = HReal 
type instance Expect' HProb         = HProb 
type instance Expect' HBool         = HBool 
type instance Expect' HUnit         = HUnit 
type instance Expect' (HPair a b)   = HPair   (Expect' a) (Expect' b)
type instance Expect' (HEither a b) = HEither (Expect' a) (Expect' b)
type instance Expect' (HList a)     = HList   (Expect' a)
type instance Expect' (HArray a)    = HArray  (Expect' a)
type instance Expect' (HMeasure a)  = HPair (HMeasure (Expect' a))
                                           (HFun (HFun (Expect' a) HProb) HProb)
type instance Expect' (HFun a b)    = HFun (Expect' a) (Expect' b)

instance (Order repr HReal) => Order (Expect repr) HReal where
  less  (Expect x) (Expect y) = Expect (less  x y)
  equal (Expect x) (Expect y) = Expect (equal x y)

deriving instance (Eq         (repr HReal)) => Eq         (Expect repr HReal)
deriving instance (Ord        (repr HReal)) => Ord        (Expect repr HReal)
deriving instance (Num        (repr HReal)) => Num        (Expect repr HReal)
deriving instance (Fractional (repr HReal)) => Fractional (Expect repr HReal)
deriving instance (Floating   (repr HReal)) => Floating   (Expect repr HReal)

instance (Order repr HProb) => Order (Expect repr) HProb where
  less  (Expect x) (Expect y) = Expect (less  x y)
  equal (Expect x) (Expect y) = Expect (equal x y)

deriving instance (Eq         (repr HProb)) => Eq         (Expect repr HProb)
deriving instance (Ord        (repr HProb)) => Ord        (Expect repr HProb)
deriving instance (Num        (repr HProb)) => Num        (Expect repr HProb)
deriving instance (Fractional (repr HProb)) => Fractional (Expect repr HProb)

instance (Order repr HInt) => Order (Expect repr) HInt where
  less  (Expect x) (Expect y) = Expect (less  x y)
  equal (Expect x) (Expect y) = Expect (equal x y)

deriving instance (Eq  (repr HInt)) => Eq  (Expect repr HInt)
deriving instance (Ord (repr HInt)) => Ord (Expect repr HInt)
deriving instance (Num (repr HInt)) => Num (Expect repr HInt)

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

  vector (Expect l) f            = Expect (vector l (unExpect . f . Expect))
  empty                          = Expect empty
  index (Expect v) (Expect i)    = Expect (index v i)
  size  (Expect v)               = Expect (size v)
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
  superpose pms = Expect $ reflect pms $ \pms' -> pair
    (superpose [ (p, fst_ m) | (p, m) <- pms' ])
    (lam (\c -> sum [ p * app (snd_ m) c | (p, m) <- pms' ]))
  uniform (Expect lo) (Expect hi) = Expect $ pair
    (uniform lo hi)
    (lam (\f -> integrate lo hi (\x -> app f x / unsafeProb (hi - lo))))
  normal (Expect mu) (Expect sd) = Expect $ pair
    (normal mu sd)
    (lam (\c -> integrate negativeInfinity infinity (\x ->
     exp_ (- (x - mu)^(2::Int) / fromProb (2 * pow_ sd 2))
     / sd / sqrt_ (2 * pi_) * app c x)))
  categorical (Expect ps) = Expect $ pair
    (categorical ps)
    (lam (\c -> let_ (summateV ps) $ \tot ->
                if_ (less 0 tot)
                    (summateV (mapWithIndex (\i p -> p * app c i) ps) / tot)
                    0))
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
  let_ (Expect rhs) f = Expect (let_ rhs (unExpect . f . Expect))

total :: (Lambda repr, Base repr) => Expect repr (HMeasure a) -> repr HProb
total (Expect m) = unpair m (\_ m2 -> m2 `app` lam (\_ -> 1))

normalize :: (Integrate repr, Lambda repr, Mochastic repr) =>
             Expect repr (HMeasure a) -> repr (HMeasure (Expect' a))
normalize (Expect m) = unpair m (\m1 m2 ->
  superpose [(recip (m2 `app` lam (\_ -> 1)), m1)])


type family ExpectFun' (x :: HakaruFun *) :: HakaruFun * 
type instance ExpectFun' (K x) = K (Expect' x)
type instance ExpectFun' Id = Id 

type family   MapExpect' (a :: [HakaruFun *]) :: [HakaruFun *]
type instance MapExpect' '[] = '[]
type instance MapExpect' (x ': xs) = (ExpectFun' x ': MapExpect' xs)

type family   MapExpect'2 (a :: [[HakaruFun *]]) :: [[HakaruFun *]]
type instance MapExpect'2 '[] = '[]
type instance MapExpect'2 (x ': xs) = MapExpect' x ': MapExpect'2 xs

type instance Expect' (HTag t xss) = HTag t (MapExpect'2 xss)
type instance Expect' (f :$ x) = MapExpect'2 f :$ Expect' x 
type instance Expect' (HMu f) = HMu (MapExpect'2 f) 

instance Embed r => Embed (Expect r) where
  _Nil = Expect _Nil
  _Cons (Expect x) (Expect xs) = Expect (_Cons x xs)

  caseProd (Expect x) f = Expect (caseProd x (\y ys -> unExpect $ f (Expect y) (Expect ys)))

  _Z (Expect x) = Expect (_Z x)
  _S (Expect x) = Expect (_S x)

  caseSum (Expect x) caseZ caseS = Expect (caseSum x (unExpect . caseZ . Expect) (unExpect . caseS . Expect))

  voidSOP (Expect x) = Expect (voidSOP x) 

  untag (Expect x) = Expect (untag x)
  tag (Expect x) = Expect (tag x)

  muE (Expect x) = Expect $ muE x
  unMuE (Expect x) = Expect $ unMuE x 

  konst (Expect x) = Expect $ konst x
  unKonst (Expect x) = Expect $ unKonst x 

  ident (Expect x) = Expect $ ident x
  unIdent (Expect x) = Expect $ unIdent x 

  natFn f (Expect x) = Expect (natFn (unExpect . f . Expect) x)
