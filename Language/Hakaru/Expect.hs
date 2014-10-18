{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances,
    TypeFamilies, StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# OPTIONS -W #-}

module Language.Hakaru.Expect (Expect(..), Expect') where

-- Expectation interpretation

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Real, Prob, Measure,
       Order(..), Base(..), Mochastic(..), Integrate(..), Lambda(..))

newtype Expect repr a = Expect { unExpect :: repr (Expect' a) }
type family Expect' (a :: *)
type instance Expect' Real         = Real
type instance Expect' Prob         = Prob
type instance Expect' Bool         = Bool
type instance Expect' ()           = ()
type instance Expect' (a, b)       = (Expect' a, Expect' b)
type instance Expect' (Either a b) = Either (Expect' a) (Expect' b)
type instance Expect' (Measure a)  = (Expect' a -> Prob) -> Prob
type instance Expect' (a -> b)     = (Expect' a -> Expect' b)

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
  pair (Expect a) (Expect b)     = Expect (pair a b)
  unpair (Expect ab) k           = Expect (unpair ab (\a b ->
                                   unExpect (k (Expect a) (Expect b))))
  inl (Expect a)                 = Expect (inl a)
  inr (Expect b)                 = Expect (inr b)
  uneither (Expect ab) ka kb     = Expect (uneither ab (unExpect . ka . Expect)
                                                       (unExpect . kb . Expect))
  unsafeProb                     = Expect . unsafeProb . unExpect
  fromProb                       = Expect . fromProb   . unExpect
  true                           = Expect true
  false                          = Expect false
  if_ (Expect c) a b             = Expect (if_ c (unExpect a) (unExpect b))
  pi_                            = Expect pi_
  exp_                           = Expect . exp_  . unExpect
  log_                           = Expect . log_  . unExpect
  sqrt_                          = Expect . sqrt_ . unExpect
  pow_ (Expect x) (Expect y)     = Expect (pow_ x y)
  betaFunc (Expect a) (Expect b) = Expect (betaFunc a b)

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
