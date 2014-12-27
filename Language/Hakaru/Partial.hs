{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances,
             TypeFamilies, RankNTypes #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Partial (Partial, runPartial, dynamic) where

-- Rudimentary partial evaluation

import Prelude hiding (Real)
import Language.Hakaru.Syntax hiding (liftM2)
import Data.Ratio (denominator, numerator)
import Data.Maybe (fromMaybe, isJust)
import Control.Monad (liftM2, liftM3)
import Data.Number.Erf (Erf(..))

data Partial repr a = Partial
  (Maybe (repr a))        -- "Nothing" means unbound
                          -- (we use this value to check if a variable is used)
  (Maybe (Static a repr)) -- "Nothing" means no static information available

runPartial :: Partial repr a -> repr a
runPartial (Partial (Just d) _) = d
runPartial (Partial Nothing  _) =
  error "Unbound variable at top level of partial evaluation"

dynamic :: Partial repr a -> Partial repr a
dynamic = fromDynamic . toDynamic

data family Static a :: (* -> *) -> *
newtype instance Static Int          repr = SInt   Integer
newtype instance Static Real         repr = SReal  Rational
newtype instance Static Prob         repr = SProb  Rational
newtype instance Static (a -> b)     repr = SArrow (Partial repr a ->
                                                    Partial repr b)
data    instance Static ()           repr = SUnit
data    instance Static Bool         repr = STrue | SFalse
data    instance Static (a, b)       repr = SPair  (Partial repr a)
                                                   (Partial repr b)
data    instance Static (Either a b) repr = SLeft  (Partial repr a)
                                          | SRight (Partial repr b)
data    instance Static [a]          repr = SNil
                                          | SCons (Partial repr a)
                                                  (Partial repr [a])
newtype instance Static (Measure a)  repr = SMeasure (M repr a)

type M repr a =
  forall w. (Partial repr a -> [(Partial repr Prob, repr (Measure w))])
                            -> [(Partial repr Prob, repr (Measure w))]

class Known a where
  type Knowledge a
  toKnown   :: Partial repr a -> Maybe (Knowledge a)
  fromKnown :: (Base repr) => Knowledge a -> Partial repr a

instance Known Bool where
  type Knowledge Bool = Bool
  toKnown (Partial _ (Just STrue))  = Just True
  toKnown (Partial _ (Just SFalse)) = Just False
  toKnown _                         = Nothing
  fromKnown True  = true
  fromKnown False = false

instance Known Int where
  type Knowledge Int = Integer
  toKnown (Partial _ (Just (SInt x))) = Just x
  toKnown _ = Nothing
  fromKnown x = Partial (Just (fromInteger x)) (Just (SInt x))

instance Known Real where
  type Knowledge Real = Rational
  toKnown (Partial _ (Just (SReal x))) = Just x
  toKnown _ = Nothing
  fromKnown x = Partial (Just (fromRational x)) (Just (SReal x))

instance Known Prob where
  type Knowledge Prob = Rational
  toKnown (Partial _ (Just (SProb x))) = Just x
  toKnown _ = Nothing
  fromKnown x = Partial (Just (fromRational x)) (Just (SProb x))

toDynamic :: Partial repr a -> Maybe (repr a)
toDynamic (Partial d _) = d

fromDynamic :: Maybe (repr a) -> Partial repr a
fromDynamic d = Partial d Nothing

unary :: (Base repr, Known a, Known b) => (Knowledge a -> Knowledge b) ->
                                          (repr a -> repr b) ->
                                          Partial repr a -> Partial repr b
unary f1 f2 x = case toKnown x of
                  Just xK -> fromKnown (f1 xK)
                  _       -> fromDynamic (fmap f2 (toDynamic x))

integer :: Rational -> Maybe Integer
integer x | denominator x == 1 = Just (numerator x)
          | otherwise          = Nothing

gammaN :: Integer -> Rational
gammaN n = fromInteger (product [1 .. n-1])

instance (Base repr, Order repr a, Known a, Ord (Knowledge a))
         => Order (Partial repr) a where
  less  x y = case (toKnown x, toKnown y) of
                (Just xK, Just yK) -> fromKnown (xK < yK)
                _ -> fromDynamic (liftM2 less (toDynamic x) (toDynamic y))
  equal x y = case (toKnown x, toKnown y) of
                (Just xK, Just yK) -> fromKnown (xK == yK)
                _ -> fromDynamic (liftM2 equal (toDynamic x) (toDynamic y))

instance (Base repr, Num (repr a),
          Known a, Eq (Knowledge a), Num (Knowledge a))
         => Num (Partial repr a) where
  x + y = case (toKnown x, toKnown y) of
            (Just xK, Just yK) -> fromKnown (xK + yK)
            (_      , Just 0 ) -> x
            (Just 0 , _      ) -> y
            _ -> fromDynamic (liftM2 (+) (toDynamic x) (toDynamic y))
  x * y = case (toKnown x, toKnown y) of
            (Just xK, Just yK) -> fromKnown (xK * yK)
            (_      , Just 1 ) -> x
            (Just 1 , _      ) -> y
            (_      , Just 0 ) -> 0
            (Just 0 , _      ) -> 0
            _ -> fromDynamic (liftM2 (*) (toDynamic x) (toDynamic y))
  x - y = case (toKnown x, toKnown y) of
            (Just xK, Just yK) -> fromKnown (xK - yK)
            (_      , Just 0 ) -> x
            (Just 0 , _      ) -> negate y
            _ -> fromDynamic (liftM2 (-) (toDynamic x) (toDynamic y))
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
            _ -> fromDynamic (liftM2 (/) (toDynamic x) (toDynamic y))
  recip = unary recip recip
  fromRational = fromKnown . fromRational

instance (Base repr, Floating (repr a), Known a, Knowledge a ~ Rational)
         => Floating (Partial repr a) where
  x ** y = case toKnown y >>= integer of
             Just yK -> x ^^ yK
             _ -> fromDynamic (liftM2 (**) (toDynamic x) (toDynamic y))
  logBase x y = fromDynamic (liftM2 logBase (toDynamic x) (toDynamic y))
  exp  x = case toKnown x of
             Just 0 -> 1
             _ -> fromDynamic (fmap exp  (toDynamic x))
  log  x = case toKnown x of
             Just 1 -> 0
             _ -> fromDynamic (fmap log  (toDynamic x))
  sqrt x = case toKnown x of
             Just 0 -> 0
             Just 1 -> 1
             _ -> fromDynamic (fmap sqrt (toDynamic x))
  pi    = fromDynamic (Just pi)
  sin   = fromDynamic . fmap sin   . toDynamic
  cos   = fromDynamic . fmap cos   . toDynamic
  tan   = fromDynamic . fmap tan   . toDynamic
  asin  = fromDynamic . fmap asin  . toDynamic
  acos  = fromDynamic . fmap acos  . toDynamic
  atan  = fromDynamic . fmap atan  . toDynamic
  sinh  = fromDynamic . fmap sinh  . toDynamic
  cosh  = fromDynamic . fmap cosh  . toDynamic
  tanh  = fromDynamic . fmap tanh  . toDynamic
  asinh = fromDynamic . fmap asinh . toDynamic
  acosh = fromDynamic . fmap acosh . toDynamic
  atanh = fromDynamic . fmap atanh . toDynamic

instance Base repr => Erf (Partial repr Real) where
  erf x = case toKnown x of
            Just 0 -> 1
            _ -> fromDynamic (fmap erf (toDynamic x))

instance (Base repr) => Base (Partial repr) where
  unit = Partial (Just unit) (Just SUnit)
  pair a b = Partial (liftM2 pair (toDynamic a) (toDynamic b))
                     (Just (SPair a b))
  unpair (Partial _ (Just (SPair a b))) k = k a b
  unpair ab k = if isJust (toDynamic skip) then skip else fromDynamic (do
    _ <- toDynamic (k (fromDynamic (Just undefined))
                      (fromDynamic (Just undefined)))
    ab' <- toDynamic ab
    let k' a b = fromMaybe (error "Partial unpair: k nonmonotonic!?")
                           (toDynamic (k (fromDynamic (Just a))
                                         (fromDynamic (Just b))))
    Just (unpair ab' k'))
    where skip = k (fromDynamic Nothing) (fromDynamic Nothing)
  inl a = Partial (fmap inl (toDynamic a)) (Just (SLeft  a))
  inr a = Partial (fmap inr (toDynamic a)) (Just (SRight a))
  uneither (Partial _ (Just (SLeft  a))) k _ = k a
  uneither (Partial _ (Just (SRight b))) _ k = k b
  uneither ab ka kb = fromDynamic (do
    _ <- toDynamic (ka (fromDynamic (Just undefined)))
    _ <- toDynamic (kb (fromDynamic (Just undefined)))
    ab' <- toDynamic ab
    let ka' a = fromMaybe (error "Partial uneither: ka nonmonotonic!?")
                          (toDynamic (ka (fromDynamic (Just a))))
        kb' b = fromMaybe (error "Partial uneither: kb nonmonotonic!?")
                          (toDynamic (kb (fromDynamic (Just b))))
    Just (uneither ab' ka' kb'))

  true  = Partial (Just true)  (Just STrue)
  false = Partial (Just false) (Just SFalse)
  if_ (Partial _ (Just STrue)) et _ = et
  if_ (Partial _ (Just SFalse)) _ ef = ef
  if_ eb et ef = fromDynamic (liftM3 if_ (toDynamic eb)
                                         (toDynamic et)
                                         (toDynamic ef))

  nil         = Partial (Just nil) (Just SNil)
  cons a as   = Partial (liftM2 cons (toDynamic a) (toDynamic as))
                        (Just (SCons a as))
  unlist (Partial _ (Just SNil)) kn _ = kn
  unlist (Partial _ (Just (SCons a as))) _ kc = kc a as
  unlist as kn kc = fromDynamic (do
    _ <- toDynamic (kc (fromDynamic (Just undefined))
                       (fromDynamic (Just undefined)))
    as' <- toDynamic as
    kn' <- toDynamic kn
    let kc' a l = fromMaybe (error "Partial unlist: kc nonmonotonic!?")
                           (toDynamic (kc (fromDynamic (Just a))
                                         (fromDynamic (Just l))))
    Just (unlist as' kn' kc'))

  unsafeProb (Partial d s) = Partial (fmap unsafeProb d)
                                     (fmap (\(SReal x) -> SProb x) s)
  fromProb (Partial d s) = Partial (fmap fromProb d)
                                   (fmap (\(SProb x) -> SReal x) s)
  fromInt (Partial d s) = Partial (fmap fromInt d)
                                  (fmap (\(SInt x) -> SReal (fromInteger x)) s)
  pi_              = fromDynamic (Just pi_)
  infinity         = fromDynamic (Just infinity)
  negativeInfinity = fromDynamic (Just negativeInfinity)
  exp_  x = case toKnown x of
              Just 0 -> 1
              _ -> fromDynamic (fmap exp_  (toDynamic x))
  log_  x = case toKnown x of
              Just 1 -> 0
              _ -> fromDynamic (fmap log_  (toDynamic x))
  sqrt_ x = case toKnown x of
              Just 0 -> 0
              Just 1 -> 1
              _ -> fromDynamic (fmap sqrt_ (toDynamic x))
  pow_ x y = case toKnown y >>= integer of
               Just yK -> x ^^ yK
               _ -> fromDynamic (liftM2 pow_ (toDynamic x) (toDynamic y))
  gammaFunc x = case toKnown x >>= integer of
                  Just xK | 1 <= xK && xK <= 10
                    -> fromKnown (gammaN xK)
                  _ -> fromDynamic (fmap gammaFunc (toDynamic x))
  betaFunc x y = case (toKnown x >>= integer, toKnown y >>= integer) of
                   (Just xK, Just yK) | 1 <= xK && xK <= 10 &&
                                        1 <= yK && yK <= 10
                     -> fromKnown (gammaN xK * gammaN yK / gammaN (xK + yK))
                   _ -> fromDynamic (liftM2 betaFunc (toDynamic x) (toDynamic y))
  erfFunc x = case toKnown x >>= integer of
                  Just 0 -> 1
                  _ -> fromDynamic (fmap erfFunc (toDynamic x))

  erfFunc_ x = case toKnown x >>= integer of
                   Just 0 -> 1
                   _ -> fromDynamic (fmap erfFunc_ (toDynamic x))

  fix f = Partial d s
    where Partial _ s = f (fix f)
          d = do _ <- toDynamic (f (fromDynamic (Just undefined)))
                 let f' = fromMaybe (error "Partial fix: f nonmonotonic!?")
                        . toDynamic . f . fromDynamic . Just
                 Just (fix f')

superpose' :: (Mochastic repr) =>
              [(Partial repr Prob, repr (Measure a))] ->
              Maybe (repr (Measure a))
superpose' pms = case filter (\(p,_) -> toKnown p /= Just 0) pms of
                   [(p,m)] | toKnown p == Just 1 -> Just m
                   pms' -> fmap superpose
                         $ sequence
                         $ [ fmap (\p'->(p',m)) (toDynamic p) | (p,m) <- pms' ]

toMeasure :: (Mochastic repr) => Partial repr (Measure a) -> M repr a
toMeasure (Partial _ (Just (SMeasure f))) = f
toMeasure (Partial m Nothing) = \c ->
  if all ((Just 0 ==) . toKnown . fst) (c (fromDynamic Nothing)) then [] else
  case (m, superpose' (c (fromDynamic (Just undefined)))) of
    (Just m', Just _) ->
      let c' x = fromMaybe (error "Partial Measure: c nonmonotonic!?")
                           (superpose' (c (fromDynamic (Just x))))
      in [(1, m' `bind` c')]
    _ -> [(fromDynamic Nothing, undefined)]

fromMeasure :: (Mochastic repr) => M repr a -> Partial repr (Measure a)
fromMeasure f = Partial (superpose' (f c)) (Just (SMeasure f))
  where c (Partial (Just x) _) = [(1, dirac x)]
        c (Partial Nothing  _) = [(fromDynamic Nothing, undefined)]

instance (Mochastic repr) => Mochastic (Partial repr) where
  dirac x       = fromMeasure (\c -> c x)
  bind m k      = fromMeasure (\c -> toMeasure m (\a -> toMeasure (k a) c))
  lebesgue      = fromDynamic (Just lebesgue)
  counting      = fromDynamic (Just counting)
  superpose pms = fromMeasure (\c -> [ (p*q,n) | (p,m) <- pms
                                               , (q,n) <- toMeasure m c ])
  uniform lo hi = fromDynamic (liftM2 uniform (toDynamic lo) (toDynamic hi))
  normal  mu sd = fromDynamic (liftM2 normal  (toDynamic mu) (toDynamic sd))
  poisson l     = fromDynamic (fmap   poisson (toDynamic l))
  gamma   sh sc = fromDynamic (liftM2 gamma   (toDynamic sh) (toDynamic sc))

instance (Integrate repr) => Integrate (Partial repr) where
  integrate lo hi f = fromDynamic (do
    _ <- toDynamic (f (fromDynamic (Just undefined)))
    lo' <- toDynamic lo
    hi' <- toDynamic hi
    let f' x = fromMaybe (error "Partial integrate: f nonmonotonic!?")
                         (toDynamic (f (fromDynamic (Just x))))
    Just (integrate lo' hi' f'))
  summate lo hi f = fromDynamic (do
    _ <- toDynamic (f (fromDynamic (Just undefined)))
    lo' <- toDynamic lo
    hi' <- toDynamic hi
    let f' x = fromMaybe (error "Partial summate: f nonmonotonic!?")
                         (toDynamic (f (fromDynamic (Just x))))
    Just (summate lo' hi' f'))

instance (Lambda repr) => Lambda (Partial repr) where
  lam f = Partial d (Just (SArrow f))
    where d = do _ <- toDynamic (f (fromDynamic (Just undefined)))
                 let f' = fromMaybe (error "Partial lam: f nonmonotonic!?")
                        . toDynamic . f . fromDynamic . Just
                 Just (lam f')
  app (Partial _ (Just (SArrow f))) x = f x
  app (Partial f _) (Partial x _) = fromDynamic (liftM2 app f x)
