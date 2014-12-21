{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances,
    TypeFamilies, StandaloneDeriving, GeneralizedNewtypeDeriving,
    RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Expect (Expect(..), Expect') where

-- Expectation interpretation

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Real, Prob, Bool_, Measure,
       Order(..), Base(..), Mochastic(..), Integrate(..), Lambda(..))
import Data.Number.Erf

newtype Expect repr a = Expect { unExpect :: repr (Expect' a) }
type family Expect' (a :: *)
-- This type family must be changed in lockstep with typeExpect below
type instance Expect' Int          = Int
type instance Expect' Real         = Real
type instance Expect' Prob         = Prob
type instance Expect' Bool_        = Bool_
type instance Expect' ()           = ()
type instance Expect' (a, b)       = (Expect' a, Expect' b)
type instance Expect' (Either a b) = Either (Expect' a) (Expect' b)
type instance Expect' (Measure a)  = (Expect' a -> Prob) -> Prob
type instance Expect' (a -> b)     = (Expect' a -> Expect' b)

-- unsafeTypeable :: forall w t. TypeRep -> (Typeable t => w) -> w
-- unsafeTypeable rep = unsafeCoerce (\k -> k (const rep))
-- -- TODO: on ghc 7.8, because the Typeable dictionary uses Proxy#,
-- -- the "const" above needs to be removed to avoid a segfault!

-- typeExpect :: forall w t. (Typeable t) => t -> (Typeable (Expect' t) => w) -> w
-- typeExpect dummy = unsafeTypeable (expect' (typeOf dummy)) where
--   expect' :: TypeRep -> TypeRep
--   expect' t
--     | t  `elem` [tInt, tReal, tProb, tUnit] = t
--     | tc `elem` [tcProd, tcSum, tcFun] = mkTyConApp tc (map expect' ts)
--     | tc == tcMeas = let [ta] = ts in mkFunTy (mkFunTy (expect' ta) tProb) tProb
--     | otherwise = error ("typeExpect " ++ show t)
--     where (tc,ts) = splitTyConApp t
--           tInt    = typeOf (undefined :: Int)
--           tReal   = typeOf (undefined :: Real)
--           tProb   = typeOf (undefined :: Prob)
--           tUnit   = typeOf (undefined :: ())
--           tcProd  = typeRepTyCon (typeOf (undefined :: (,)    () ()))
--           tcSum   = typeRepTyCon (typeOf (undefined :: Either () ()))
--           tcFun   = typeRepTyCon (typeOf (undefined :: (->)   () ()))
--           tcMeas  = typeRepTyCon (typeOf (undefined :: Measure   ()))

-- typeExpectBoth :: forall t1 t2 a f repr w.
--                   (Typeable t1, Typeable t2) => a (f t1 t2) ->
--                   ((Typeable (Expect' t1), Typeable (Expect' t2)) =>
--                    repr (Expect' w)) ->
--                   Expect repr w
-- typeExpectBoth _ k = Expect (typeExpect (undefined :: t1)
--                             (typeExpect (undefined :: t2) k))

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

instance Erf (repr Real) => Erf (Expect repr Real) where
  erf (Expect n) = Expect (erf n)

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
  pow_ (Expect x) (Expect y)     = Expect (pow_ x y)
  infinity                       = Expect infinity
  negativeInfinity               = Expect negativeInfinity
  gammaFunc (Expect n)           = Expect (gammaFunc n)
  betaFunc (Expect a) (Expect b) = Expect (betaFunc a b)
  erfFunc (Expect n)             = Expect (erfFunc n)
  erfFunc_ (Expect n)            = Expect (erfFunc_ n)
  fix f                          = Expect (fix (unExpect . f . Expect))

instance (Integrate repr) => Integrate (Expect repr) where
  integrate (Expect lo) (Expect hi) f =
    Expect (integrate lo hi (unExpect . f . Expect))
  summate (Expect lo) (Expect hi) f =
    Expect (summate lo hi (unExpect . f . Expect))

instance (Integrate repr, Lambda repr)
      => Mochastic (Expect repr) where
  dirac (Expect a)  = Expect (lam (\c -> c `app` a))
  bind (Expect m) k = Expect (lam (\c -> m `app` lam (\a ->
                      unExpect (k (Expect a)) `app` c)))
  lebesgue          = Expect (lam (integrate negativeInfinity infinity . app))
  counting          = Expect (lam (summate   negativeInfinity infinity . app))
  superpose pms     = Expect (lam (\c -> sum [ p * app m c
                                             | (Expect p, Expect m) <- pms ]))
  uniform (Expect lo) (Expect hi) = Expect (lam (\f ->
    integrate lo hi (\x -> app f x / unsafeProb (hi - lo))))
  -- TODO: override poisson, gamma, invgamma to express that they do not
  --       generate negative numbers

instance (Lambda repr) => Lambda (Expect repr) where
  lam f = Expect (lam (unExpect . f . Expect))
  app (Expect rator) (Expect rand) = Expect (app rator rand)
