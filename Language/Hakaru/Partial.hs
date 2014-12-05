{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances,
             TypeFamilies, RankNTypes #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Partial (Partial, toDynamic, fromDynamic) where

-- Rudimentary partial evaluation

import Prelude hiding (Real)
import Language.Hakaru.Syntax
import Data.Ratio (denominator, numerator)

data Partial repr a = Partial (repr a) (Maybe (Static a repr))

data family Static a :: (* -> *) -> *
newtype instance Static Int          repr = SInt   Integer
newtype instance Static Real         repr = SReal  Rational
newtype instance Static Prob         repr = SProb  Rational
newtype instance Static (a -> b)     repr = SArrow (Partial repr a ->
                                                    Partial repr b)
data    instance Static ()           repr = SUnit
data    instance Static (a, b)       repr = SPair  (Partial repr a)
                                                   (Partial repr b)
data    instance Static (Either a b) repr = SLeft  (Partial repr a)
                                          | SRight (Partial repr b)
newtype instance Static (Measure a)  repr = SMeasure (M repr a)

type M repr a =
  forall w. (Partial repr a -> [(Partial repr Prob, repr (Measure w))])
                            -> [(Partial repr Prob, repr (Measure w))]

class Known a where
  type Knowledge a
  toKnown   :: Partial repr a -> Maybe (Knowledge a)
  fromKnown :: (Base repr) => Knowledge a -> Partial repr a

instance Known Bool_ where
  type Knowledge Bool_ = Bool
  toKnown (Partial _ (Just (SLeft  _))) = Just True
  toKnown (Partial _ (Just (SRight _))) = Just False
  toKnown _                             = Nothing
  fromKnown True  = true
  fromKnown False = false

instance Known Int where
  type Knowledge Int = Integer
  toKnown (Partial _ (Just (SInt x))) = Just x
  toKnown _ = Nothing
  fromKnown x = Partial (fromInteger x) (Just (SInt x))

instance Known Real where
  type Knowledge Real = Rational
  toKnown (Partial _ (Just (SReal x))) = Just x
  toKnown _ = Nothing
  fromKnown x = Partial (fromRational x) (Just (SReal x))

instance Known Prob where
  type Knowledge Prob = Rational
  toKnown (Partial _ (Just (SProb x))) = Just x
  toKnown _ = Nothing
  fromKnown x = Partial (fromRational x) (Just (SProb x))

toDynamic :: Partial repr a -> repr a
toDynamic (Partial d _) = d

fromDynamic :: repr a -> Partial repr a
fromDynamic d = Partial d Nothing

unary :: (Base repr, Known a, Known b) => (Knowledge a -> Knowledge b) ->
                                          (repr a -> repr b) ->
                                          Partial repr a -> Partial repr b
unary f1 f2 x = case toKnown x of
                  Just xK -> fromKnown (f1 xK)
                  _       -> fromDynamic (f2 (toDynamic x))

integer :: Rational -> Maybe Integer
integer x | denominator x == 1 = Just (numerator x)
          | otherwise          = Nothing

gammaN :: Integer -> Rational
gammaN n = fromInteger (product [1 .. n-1])

instance (Base repr, Order repr a, Known a, Ord (Knowledge a))
         => Order (Partial repr) a where
  less  x y = case (toKnown x, toKnown y) of
                (Just xK, Just yK) -> fromKnown (xK < yK)
                _ -> fromDynamic (less (toDynamic x) (toDynamic y))
  equal x y = case (toKnown x, toKnown y) of
                (Just xK, Just yK) -> fromKnown (xK == yK)
                _ -> fromDynamic (equal (toDynamic x) (toDynamic y))

instance (Base repr, Num (repr a),
          Known a, Eq (Knowledge a), Num (Knowledge a))
         => Num (Partial repr a) where
  x + y = case (toKnown x, toKnown y) of
            (Just xK, Just yK) -> fromKnown (xK + yK)
            (_      , Just 0 ) -> x
            (Just 0 , _      ) -> y
            _                  -> fromDynamic (toDynamic x + toDynamic y)
  x * y = case (toKnown x, toKnown y) of
            (Just xK, Just yK) -> fromKnown (xK * yK)
            (_      , Just 1 ) -> x
            (Just 1 , _      ) -> y
            (_      , Just 0 ) -> 0
            (Just 0 , _      ) -> 0
            _                  -> fromDynamic (toDynamic x * toDynamic y)
  x - y = case (toKnown x, toKnown y) of
            (Just xK, Just yK) -> fromKnown (xK - yK)
            (_      , Just 0 ) -> x
            (Just 0 , _      ) -> negate y
            _                  -> fromDynamic (toDynamic x - toDynamic y)
  negate = unary negate negate
  abs    = unary abs    abs
  signum = unary signum signum
  fromInteger = fromKnown . fromInteger

instance (Base repr, Fractional (repr a),
          Known a, Eq (Knowledge a), Fractional (Knowledge a))
         => Fractional (Partial repr a) where
  x / y = case (toKnown x, toKnown y) of
            (Just xK, Just yK) -> fromKnown (xK / yK)
            (_      , Just 1 ) -> x
            (Just 1 , _      ) -> recip y
            (Just 0 , _      ) -> 0
            _                  -> fromDynamic (toDynamic x / toDynamic y)
  recip = unary recip recip
  fromRational = fromKnown . fromRational

instance (Base repr, Floating (repr a), Known a, Knowledge a ~ Rational)
         => Floating (Partial repr a) where
  x ** y = case toKnown y >>= integer of
             Just yK -> x ^^ yK
             _ -> fromDynamic (toDynamic x ** toDynamic y)
  logBase x y = fromDynamic (logBase (toDynamic x) (toDynamic y))
  exp  x = case toKnown x of
             Just 0 -> 1
             _      -> fromDynamic (exp  (toDynamic x))
  log  x = case toKnown x of
             Just 1 -> 0
             _      -> fromDynamic (log  (toDynamic x))
  sqrt x = case toKnown x of
             Just 0 -> 0
             Just 1 -> 1
             _      -> fromDynamic (sqrt (toDynamic x))
  pi    = fromDynamic pi
  sin   = fromDynamic . sin   . toDynamic
  cos   = fromDynamic . cos   . toDynamic
  tan   = fromDynamic . tan   . toDynamic
  asin  = fromDynamic . asin  . toDynamic
  acos  = fromDynamic . acos  . toDynamic
  atan  = fromDynamic . atan  . toDynamic
  sinh  = fromDynamic . sinh  . toDynamic
  cosh  = fromDynamic . cosh  . toDynamic
  tanh  = fromDynamic . tanh  . toDynamic
  asinh = fromDynamic . asinh . toDynamic
  acosh = fromDynamic . acosh . toDynamic
  atanh = fromDynamic . atanh . toDynamic

instance (Base repr) => Base (Partial repr) where
  unit = Partial unit (Just SUnit)
  pair a b = Partial (pair (toDynamic a) (toDynamic b)) (Just (SPair a b))
  unpair (Partial _ (Just (SPair a b))) k = k a b
  unpair ab k = fromDynamic (unpair (toDynamic ab)
                (\a b -> toDynamic (k (fromDynamic a) (fromDynamic b))))
  inl a = Partial (inl (toDynamic a)) (Just (SLeft  a))
  inr a = Partial (inr (toDynamic a)) (Just (SRight a))
  uneither (Partial _ (Just (SLeft  a))) k _ = k a
  uneither (Partial _ (Just (SRight b))) _ k = k b
  uneither ab ka kb = fromDynamic (uneither (toDynamic ab)
                      (\a -> toDynamic (ka (fromDynamic a)))
                      (\b -> toDynamic (kb (fromDynamic b))))
  unsafeProb (Partial d s) = Partial (unsafeProb d)
                                     (fmap (\(SReal x) -> SProb x) s)
  fromProb (Partial d s) = Partial (fromProb d)
                                   (fmap (\(SProb x) -> SReal x) s)
  fromInt (Partial d s) = Partial (fromInt d)
                                  (fmap (\(SInt x) -> SReal (fromInteger x)) s)
  pi_              = fromDynamic pi_
  infinity         = fromDynamic infinity
  negativeInfinity = fromDynamic negativeInfinity
  exp_  x = case toKnown x of
              Just 0 -> 1
              _      -> fromDynamic (exp_  (toDynamic x))
  log_  x = case toKnown x of
              Just 1 -> 0
              _      -> fromDynamic (log_  (toDynamic x))
  sqrt_ x = case toKnown x of
              Just 0 -> 0
              Just 1 -> 1
              _      -> fromDynamic (sqrt_ (toDynamic x))
  pow_ x y = case toKnown y >>= integer of
               Just yK -> x ^^ yK
               _ -> fromDynamic (toDynamic x `pow_` toDynamic y)
  gammaFunc x = case toKnown x >>= integer of
                  Just xK | 1 <= xK && xK <= 10
                    -> fromKnown (gammaN xK)
                  _ -> fromDynamic (gammaFunc (toDynamic x))
  betaFunc x y = case (toKnown x >>= integer, toKnown y >>= integer) of
                   (Just xK, Just yK) | 1 <= xK && xK <= 10 &&
                                        1 <= yK && yK <= 10
                     -> fromKnown (gammaN xK * gammaN yK / gammaN (xK + yK))
                   _ -> fromDynamic (betaFunc (toDynamic x) (toDynamic y))
  fix f = Partial (fix (toDynamic . f . fromDynamic)) s
    where Partial _ s = f (fix f)

superpose' :: (Mochastic repr) =>
              [(Partial repr Prob, repr (Measure a))] -> repr (Measure a)
superpose' pms = case filter (\(p,_) -> toKnown p /= Just 0) pms of
                   [(p,m)] | toKnown p == Just 1 -> m
                   pms' -> superpose [ (toDynamic p, m) | (p,m) <- pms' ]

toMeasure :: (Mochastic repr) => Partial repr (Measure a) -> M repr a
toMeasure (Partial _ (Just (SMeasure f))) = f
toMeasure (Partial m Nothing) =
  \c -> [(1, m `bind` \x -> superpose' (c (fromDynamic x)))]

fromMeasure :: (Mochastic repr) => M repr a -> Partial repr (Measure a)
fromMeasure f = Partial (superpose' (f (\x -> [(1, dirac (toDynamic x))])))
                        (Just (SMeasure f))

instance (Mochastic repr) => Mochastic (Partial repr) where
  dirac x       = fromMeasure (\c -> c x)
  bind m k      = fromMeasure (\c -> toMeasure m (\a -> toMeasure (k a) c))
  lebesgue      = fromDynamic lebesgue
  counting      = fromDynamic counting
  superpose pms = fromMeasure (\c -> [ (p*q,n) | (p,m) <- pms
                                               , (q,n) <- toMeasure m c ])
  uniform lo hi = fromDynamic (uniform (toDynamic lo) (toDynamic hi))
  normal  mu sd = fromDynamic (normal  (toDynamic mu) (toDynamic sd))
  poisson l     = fromDynamic (poisson (toDynamic l))
  gamma   sh sc = fromDynamic (gamma   (toDynamic sh) (toDynamic sc))

instance (Integrate repr) => Integrate (Partial repr) where
  integrate lo hi f = fromDynamic (integrate (toDynamic lo) (toDynamic hi)
                                             (toDynamic . f . fromDynamic))
  summate   lo hi f = fromDynamic (summate   (toDynamic lo) (toDynamic hi)
                                             (toDynamic . f . fromDynamic))

instance (Lambda repr) => Lambda (Partial repr) where
  lam f = Partial (lam (toDynamic . f . fromDynamic)) (Just (SArrow f))
  app (Partial _ (Just (SArrow f))) x = f x
  app (Partial f _) (Partial x _) = fromDynamic (app f x)
