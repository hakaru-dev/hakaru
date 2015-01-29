{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances,
    TypeFamilies, StandaloneDeriving, GeneralizedNewtypeDeriving, GADTs,
    RankNTypes, ScopedTypeVariables, UndecidableInstances, TypeOperators, DataKinds #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Expect (Expect(..), Expect', total, normalize) where

-- Expectation interpretation

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Real, Prob, Measure,
       Order(..), Base(..), Mochastic(..), Integrate(..), Lambda(..),
       fst_, snd_)
import Generics.SOP hiding (fn) 
import Language.Hakaru.Embed
import Language.Hakaru.Maple 
import GHC.Prim (Any)

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
  fix f                          = Expect (fix (unExpect . f . Expect))

instance (Integrate repr) => Integrate (Expect repr) where
  integrate (Expect lo) (Expect hi) f =
    Expect (integrate lo hi (unExpect . f . Expect))
  summate (Expect lo) (Expect hi) f =
    Expect (summate lo hi (unExpect . f . Expect))

instance (Mochastic repr, Integrate repr, Lambda repr)
      => Mochastic (Expect repr) where
  dirac (Expect a) = Expect $ pair
    (dirac a)
    (lam (\c -> c `app` a))
  bind (Expect m) k = Expect $ unpair m $ \m1 m2 -> pair
    (bind m1 (fst_ . unExpect . k . Expect))
    (lam (\c -> m2 `app` lam (\a -> snd_ (unExpect (k (Expect a))) `app` c)))
  lebesgue = Expect $ pair
    lebesgue
    (lam (integrate negativeInfinity infinity . app))
  counting = Expect $ pair
    counting
    (lam (summate   negativeInfinity infinity . app))
  superpose pms = Expect $ pair
    (superpose [ (p, fst_ m) | (Expect p, Expect m) <- pms ])
    (lam (\c -> sum [ p * app (snd_ m) c | (Expect p, Expect m) <- pms ]))
  uniform (Expect lo) (Expect hi) = Expect $ pair
    (uniform lo hi)
    (lam (\f -> integrate lo hi (\x -> app f x / unsafeProb (hi - lo))))
  -- TODO: override poisson, gamma, invgamma to express that they do not
  --       generate negative numbers

instance (Lambda repr) => Lambda (Expect repr) where
  lam f = Expect (lam (unExpect . f . Expect))
  app (Expect rator) (Expect rand) = Expect (app rator rand)

total :: (Lambda repr, Base repr) => Expect repr (Measure a) -> repr Prob
total (Expect m) = unpair m (\_ m2 -> m2 `app` lam (\_ -> 1))

normalize :: (Integrate repr, Lambda repr, Mochastic repr) =>
             Expect repr (Measure a) -> repr (Measure (Expect' a))
normalize (Expect m) = unpair m (\m1 m2 ->
  superpose [(recip (m2 `app` lam (\_ -> 1)), m1)])

-- 'r' will only ever be 'Expect repr' 
type instance Expect' (NS (NP r) a) = NS (NP r) a 
type instance Expect' Any = HRep (Expect Maple) Any 

instance Embed (Expect Maple) where 
  type Ctx (Expect Maple) t = (Expect' t ~ HRep (Expect Maple) t)

  hRep (Expect x) = Expect x 
  unHRep (Expect x) = Expect x 

  sop' p x = 
    case diSing (datatypeInfo p) of 
      Dict -> Expect $ Maple $ unMaple $ sop' p (unSOP (hliftA toM (SOP x)))
        where toM :: Expect Maple a -> Maple a 
              toM (Expect (Maple a)) = Maple a 

  case' p (Expect (Maple x)) fn = 
    case diSing (datatypeInfo p) of
      Dict -> Expect (Maple $ unMaple $ case' p (Maple x) (funMs sing fn))
        where funM :: Sing xs -> NFn (Expect Maple) o xs -> NFn Maple o xs 
              funM SNil (NFn (Expect (Maple f))) = NFn (Maple f)
              funM s@SCons ((NFn f) :: NFn (Expect Maple) o (x ': xs)) = NFn $ \(Maple a) -> 
                let 
                 r :: NFn (Expect Maple) o xs -> NAryFun Maple o xs 
                 r = unFn . funM (singTail s) 
                in r $ NFn $ f $ Expect $ Maple a  

              funMs :: Sing xss -> NP (NFn (Expect Maple) o) xss -> NP (NFn Maple o) xss 
              funMs SNil Nil = Nil
              funMs SCons (a :* as) = funM sing a :* funMs sing as
              funMs _ _ = error "typeError: funMS" 

                     
