{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances,
    TypeFamilies, StandaloneDeriving, GeneralizedNewtypeDeriving,
    Rank2Types, GADTs #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Expect (Expect(..), Expect') where

-- Expectation interpretation

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Real, Prob, Measure,
       TypeOf(..), Type, typeOf1, typeOf2,
       Order(..), Base(..), Mochastic(..), Integrate(..), Lambda(..))

newtype Expect repr a = Expect { unExpect :: repr (Expect' a) }
type family Expect' (a :: *)
type instance Expect' Real         = Real
type instance Expect' Prob         = Prob
type instance Expect' ()           = ()
type instance Expect' (a, b)       = (Expect' a, Expect' b)
type instance Expect' (Either a b) = Either (Expect' a) (Expect' b)
type instance Expect' (Measure a)  = (Expect' a -> Prob) -> Prob
type instance Expect' (a -> b)     = (Expect' a -> Expect' b)

typeExpect :: TypeOf t -> (Type (Expect' t) => w) -> w
typeExpect Real   k = k
typeExpect Prob   k = k
typeExpect One    k = k
typeExpect x@Meas k = typeExpect (typeOf2 x) k
typeExpect x@Prod k = typeExpect (typeOf1 x) (typeExpect (typeOf2 x) k)
typeExpect x@Sum  k = typeExpect (typeOf1 x) (typeExpect (typeOf2 x) k)
typeExpect x@Fun  k = typeExpect (typeOf1 x) (typeExpect (typeOf2 x) k)

typeExpectBoth :: (Type t1, Type t2) => a (f t1 t2)
               -> ((Type (Expect' t1), Type (Expect' t2)) => repr (Expect' w))
               -> Expect repr w
typeExpectBoth a k = Expect (typeExpect (typeOf1 a) (typeExpect (typeOf2 a) k))

instance (Order repr Real) => Order (Expect repr) Real where
  less (Expect x) (Expect y) = Expect (less x y)

deriving instance (Eq         (repr Real)) => Eq         (Expect repr Real)
deriving instance (Ord        (repr Real)) => Ord        (Expect repr Real)
deriving instance (Num        (repr Real)) => Num        (Expect repr Real)
deriving instance (Fractional (repr Real)) => Fractional (Expect repr Real)
deriving instance (Floating   (repr Real)) => Floating   (Expect repr Real)

instance (Order repr Prob) => Order (Expect repr) Prob where
  less (Expect x) (Expect y) = Expect (less x y)

deriving instance (Eq         (repr Prob)) => Eq         (Expect repr Prob)
deriving instance (Ord        (repr Prob)) => Ord        (Expect repr Prob)
deriving instance (Num        (repr Prob)) => Num        (Expect repr Prob)
deriving instance (Fractional (repr Prob)) => Fractional (Expect repr Prob)

instance (Base repr) => Base (Expect repr) where
  unit                           = Expect unit
  pair (Expect a) (Expect b)     = x where x = typeExpectBoth x (pair a b)
  unpair x@(Expect ab) k         = typeExpectBoth x (unpair ab (\a b ->
                                   unExpect (k (Expect a) (Expect b))))
  inl (Expect a)                 = x where x = typeExpectBoth x (inl a)
  inr (Expect b)                 = x where x = typeExpectBoth x (inr b)
  uneither x@(Expect ab) ka kb   = typeExpectBoth x (uneither ab
                                     (unExpect . ka . Expect)
                                     (unExpect . kb . Expect))
  unsafeProb                     = Expect . unsafeProb . unExpect
  fromProb                       = Expect . fromProb   . unExpect
  pi_                            = Expect pi_
  exp_                           = Expect . exp_  . unExpect
  log_                           = Expect . log_  . unExpect
  sqrt_                          = Expect . sqrt_ . unExpect
  pow_ (Expect x) (Expect y)     = Expect (pow_ x y)
  betaFunc (Expect a) (Expect b) = Expect (betaFunc a b)
  gammaFunc (Expect n)           = Expect (gammaFunc n)
  fix f                          = Expect (fix (unExpect . f . Expect))

instance (Integrate repr) => Integrate (Expect repr) where
  integrate (Expect lo) (Expect hi) f =
    Expect (integrate lo hi (unExpect . f . Expect))
  infinity         = Expect infinity
  negativeInfinity = Expect negativeInfinity

instance (Integrate repr, Lambda repr) => Mochastic (Expect repr) where
  dirac (Expect a)  = Expect (lam (\c -> c `app` a))
  bind (Expect m) k = Expect (lam (\c -> m `app` lam (\a ->
                      unExpect (k (Expect a)) `app` c)))
  lebesgue          = Expect (lam (integrate negativeInfinity infinity . app))
  superpose pms     = Expect (lam (\c -> sum [ p * app m c
                                             | (Expect p, Expect m) <- pms ]))
  uniform (Expect lo) (Expect hi) = Expect (lam (\f ->
    integrate lo hi (\x -> app f x / unsafeProb (hi - lo))))

instance (Lambda repr) => Lambda (Expect repr) where
  lam f = Expect (lam (unExpect . f . Expect))
  app (Expect rator) (Expect rand) = Expect (app rator rand)
