{-# LANGUAGE Rank2Types, ExistentialQuantification, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Compose (Compose, liftCompose, runCompose) where

import Language.Hakaru.Syntax
import Control.Applicative hiding (empty)
import Data.Traversable (traverse)
import Unsafe.Coerce (unsafeCoerce)

newtype Compose f s repr a = Compose { unCompose :: C f repr (repr a) }

newtype C f repr a = C { unC :: Int -> f ([Binding repr] -> a) }
                         -- this^^^       ^^^^^^^^^^^^^^
                         -- is the length of this list

data Binding repr = forall a. Binding (repr a)

unsafeLookup :: Int -> [Binding repr] -> repr a
unsafeLookup n xs = case xs !! n of
  Binding x -> (unsafeCoerce :: repr b -> repr a) x

instance (Functor f) => Functor (C f repr) where
  fmap f (C x) = C (\n -> fmap (f .) (x n))
  a   <$ (C x) = C (\n -> const a <$ (x n))

instance (Applicative f) => Applicative (C f repr) where
  pure a      = C (\_ -> pure (const a))
  C x <*> C y = C (\n -> (\x' y' env -> (x' env) (y' env)) <$> x n <*> y n)
  C x  *> C y = C (\n ->                                       x n  *> y n)
  C x <*  C y = C (\n ->                                       x n <*  y n)

liftCompose :: (Applicative f) => repr a -> Compose f s repr a
liftCompose = Compose . pure

runCompose :: (Functor f) => (forall s. Compose f s repr a) -> f (repr a)
runCompose (Compose (C x)) = fmap ($ []) (x 0)

fun :: (Applicative f) =>
       (C f repr (repr a) -> C f repr b) -> C f repr (repr a -> b)
fun f = C (\n ->
  let param n' | n' > n    = pure (unsafeLookup n)
               | otherwise = error ("Scope extrusion: " ++ show n'
                                              ++ " <= " ++ show n)
  in fmap (\body' env arg -> body' (env ++ [Binding arg]))
          (unC (f (C param)) (n+1)))

fun0 :: Compose f s repr a ->
        C f repr (repr a)
fun1 :: (Applicative f) =>
        (Compose f s repr a -> Compose f s repr b) ->
        C f repr (repr a -> repr b)
fun2 :: (Applicative f) =>
        (Compose f s repr a -> Compose f s repr b -> Compose f s repr c) ->
        C f repr (repr a -> repr b -> repr c)

fun0   = unCompose
fun1 f = fun (\x -> unCompose (f (Compose x)))
fun2 f = fun (\x -> fun (\y -> unCompose (f (Compose x) (Compose y))))

compose0 :: (Applicative f) => repr a ->
            Compose f s repr a
compose1 :: (Functor f) => (repr a -> repr b) ->
            Compose f s repr a -> Compose f s repr b
compose2 :: (Applicative f) => (repr a -> repr b -> repr c) ->
            Compose f s repr a -> Compose f s repr b -> Compose f s repr c

compose0 r     = Compose (pure   r)
compose1 r x   = Compose (fmap   r (fun0 x))
compose2 r x y = Compose (liftA2 r (fun0 x) (fun0 y))

instance (Order repr a, Applicative f) => Order (Compose f s repr) a where
  less  = compose2 less
  equal = compose2 equal

instance (Num (repr a), Applicative f) => Num (Compose f s repr a) where
  (+)         = compose2 (+)
  (*)         = compose2 (*)
  (-)         = compose2 (-)
  negate      = compose1 negate
  abs         = compose1 abs
  signum      = compose1 signum
  fromInteger = compose0 . fromInteger

instance (Fractional (repr a), Applicative f) =>
         Fractional (Compose f s repr a) where
  (/)          = compose2 (/)
  recip        = compose1 recip
  fromRational = compose0 . fromRational

instance (Floating (repr a), Applicative f) =>
         Floating (Compose f s repr a) where
  pi      = compose0 pi
  exp     = compose1 exp
  sqrt    = compose1 sqrt
  log     = compose1 log
  (**)    = compose2 (**)
  logBase = compose2 logBase
  sin     = compose1 sin
  tan     = compose1 tan
  cos     = compose1 cos
  asin    = compose1 asin
  atan    = compose1 atan
  acos    = compose1 acos
  sinh    = compose1 sinh
  tanh    = compose1 tanh
  cosh    = compose1 cosh
  asinh   = compose1 asinh
  atanh   = compose1 atanh
  acosh   = compose1 acosh

instance (Base repr, Applicative f) => Base (Compose f s repr) where
  unit             = compose0 unit
  pair             = compose2 pair
  unpair x f       = Compose (liftA2 unpair (fun0 x) (fun2 f))
  inl              = compose1 inl
  inr              = compose1 inr
  uneither x f g   = Compose (liftA3 uneither (fun0 x) (fun1 f) (fun1 g))
  true             = compose0 true
  false            = compose0 false
  if_ b t f        = Compose (liftA3 if_ (fun0 b) (fun0 t) (fun0 f))
  nil              = compose0 nil
  cons             = compose2 cons
  unlist l f g     = Compose (liftA3 unlist (fun0 l) (fun0 f) (fun2 g))
  unsafeProb       = compose1 unsafeProb
  fromProb         = compose1 fromProb
  fromInt          = compose1 fromInt
  pi_              = compose0 pi_
  exp_             = compose1 exp_
  erf              = compose1 erf
  erf_             = compose1 erf_
  log_             = compose1 log_
  sqrt_            = compose1 sqrt_
  pow_             = compose2 pow_
  infinity         = compose0 infinity
  negativeInfinity = compose0 negativeInfinity
  gammaFunc        = compose1 gammaFunc
  betaFunc         = compose2 betaFunc
  vector l f       = Compose (liftA2 vector (fun0 l) (fun1 f))
  empty            = compose0 empty
  index            = compose2 index
  size             = compose1 size
  reduce r z v     = Compose (liftA3 reduce (fun2 r) (fun0 z) (fun0 v))
  fix f            = Compose (fmap fix (fun1 f))

instance (Mochastic repr, Applicative f) => Mochastic (Compose f s repr) where
  dirac     = compose1 dirac
  bind m k  = Compose (liftA2 bind (fun0 m) (fun1 k))
  lebesgue  = compose0 lebesgue
  counting  = compose0 counting
  superpose = Compose . fmap superpose
                      . traverse (\(Compose p, Compose m) -> liftA2 (,) p m)
  uniform   = compose2 uniform
  normal    = compose2 normal
  -- TODO define mix and categorical
  poisson   = compose1 poisson
  gamma     = compose2 gamma
  beta      = compose2 beta
  dp        = compose2 dp
  plate     = compose1 plate
  -- TODO define chain

instance (Integrate repr, Applicative f) => Integrate (Compose f s repr) where
  integrate l h f = Compose (liftA3 integrate (fun0 l) (fun0 h) (fun1 f))
  summate   l h f = Compose (liftA3 summate   (fun0 l) (fun0 h) (fun1 f))

instance (Lambda repr, Applicative f) => Lambda (Compose f s repr) where
  app   = compose2 app
  lam f = Compose (fmap lam (fun1 f))

instance (Lub f) => Lub (Compose f s repr) where
  bot                                 = Compose (C (\_ -> bot))
  lub (Compose (C x)) (Compose (C y)) = Compose (C (\n -> lub (x n) (y n)))

instance Lub [] where
  bot = []
  lub = (++)
