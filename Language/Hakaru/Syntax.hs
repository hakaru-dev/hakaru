{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, DefaultSignatures,
             DeriveDataTypeable, GADTs, Rank2Types #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Syntax (Real, Prob, Measure, Bool_,
       EqType(Refl), Number(..), Fraction(..), ggcast, Uneither(Uneither),
       errorEmpty,
       Order(..), Base(..), ununit, true, false, if_, fst_, snd_,
       and_, or_, not_, min_, max_,
       Mochastic(..), bind_, liftM, liftM2, invgamma, beta, bern,
       Summate(..), Integrate(..), Lambda(..)) where

import Prelude hiding (Real)
import Data.Typeable (Typeable, gcast)

infix  4 `less`
infixl 1 `bind`, `bind_`
infixl 9 `app`

------- Types

data Real      deriving Typeable
data Prob      deriving Typeable -- meaning: non-negative real number
data Measure a deriving Typeable
type Bool_ = Either () ()

data EqType t t' where
  Refl :: EqType t t

class (Typeable a) => Number a where
  numberCase :: f Int -> f Real -> f Prob -> f a
  numberRepr :: (Base repr) =>
                ((Order repr a, Num (repr a)) => f repr a) -> f repr a

class (Number a) => Fraction a where
  fractionCase :: f Real -> f Prob -> f a
  fractionRepr :: (Base repr) =>
                  ((Order repr a, Fractional (repr a)) => f repr a) -> f repr a

instance Number Int where
  numberCase k _ _ = k
  numberRepr k     = k

instance Number Real where
  numberCase _ k _ = k
  numberRepr k     = k

instance Number Prob where
  numberCase _ _ k = k
  numberRepr k     = k

instance Fraction Real where
  fractionCase k _ = k
  fractionRepr k   = k

instance Fraction Prob where
  fractionCase _ k = k
  fractionRepr k   = k

newtype Flip f b a = Flip (f a b)
ggcast :: (Typeable a, Typeable a', Typeable b, Typeable b') =>
          f a b -> Maybe (f a' b')
ggcast fab = do Flip fa'b <- gcast (Flip fab)
                gcast fa'b

newtype Uneither repr a b = Uneither (forall c.
  repr (Either a b) -> (repr a -> repr c) -> (repr b -> repr c) -> repr c)

------- Terms

class Order repr a where
  less :: repr a -> repr a -> repr Bool_

class (Order repr Int , Num        (repr Int ),
       Order repr Real, Floating   (repr Real),
       Order repr Prob, Fractional (repr Prob)) => Base repr where
  unit       :: repr ()
  pair       :: repr a -> repr b -> repr (a,b)
  unpair     :: repr (a,b) -> (repr a -> repr b -> repr c) -> repr c
  inl        :: (Typeable a, Typeable b) => repr a -> repr (Either a b)
  inr        :: (Typeable a, Typeable b) => repr b -> repr (Either a b)
  uneither   :: (Typeable a, Typeable b) => repr (Either a b) ->
                (repr a -> repr c) -> (repr b -> repr c) -> repr c

  unsafeProb :: repr Real -> repr Prob
  fromProb   :: repr Prob -> repr Real
  fromInt    :: repr Int  -> repr Real

  pi_      :: repr Prob
  pi_      =  unsafeProb pi
  exp_     :: repr Real -> repr Prob
  exp_     =  unsafeProb . exp
  log_     :: repr Prob -> repr Real
  log_     =  log . fromProb
  sqrt_    :: repr Prob -> repr Prob
  sqrt_ x  =  pow_ x (1/2)
  pow_     :: repr Prob -> repr Real -> repr Prob
  pow_ x y =  exp_ (log_ x * y)

  infinity, negativeInfinity :: repr Real

  gammaFunc         ::                     repr Real -> repr Prob
  default gammaFunc :: (Integrate repr) => repr Real -> repr Prob
  gammaFunc t = integrate 0 infinity $ \x ->
    pow_ (unsafeProb x) (t-1) * exp_ (-x)

  fix :: (repr a -> repr a) -> repr a
  fix f = x where x = f x

ununit :: repr () -> repr a -> repr a
ununit _ e = e

true, false :: (Base repr) => repr Bool_
true  = inl unit
false = inr unit

if_ :: (Base repr) => repr Bool_ -> repr c -> repr c -> repr c
if_ e et ef = uneither e (const et) (const ef)

fst_ :: (Base repr) => repr (a,b) -> repr a
fst_ ab = unpair ab (\a _ -> a)

snd_ :: (Base repr) => repr (a,b) -> repr b
snd_ ab = unpair ab (\_ b -> b)

and_ :: (Base repr) => [repr Bool_] -> repr Bool_
and_ []     = true
and_ [b]    = b
and_ (b:bs) = if_ b (and_ bs) false

or_ :: (Base repr) => [repr Bool_] -> repr Bool_
or_ []      = false
or_ [b]     = b
or_ (b:bs)  = if_ b true (or_ bs)

not_ :: Base repr => repr Bool_ -> repr Bool_
not_ a = if_ a false true

min_, max_ :: (Order repr a, Base repr) => repr a -> repr a -> repr a
min_ x y = if_ (less x y) x y
max_ x y = if_ (less x y) y x

class (Base repr) => Mochastic repr where
  dirac         :: repr a -> repr (Measure a)
  bind          :: repr (Measure a) ->
                   (repr a -> repr (Measure b)) -> repr (Measure b)
  lebesgue      :: repr (Measure Real)
  countInt      :: repr (Measure Int)
  superpose     :: [(repr Prob, repr (Measure a))] -> repr (Measure a)

  uniform       :: repr Real -> repr Real -> repr (Measure Real)
  uniform lo hi =  lebesgue `bind` \x ->
                   if_ (and_ [less lo x, less x hi])
                       (superpose [(recip (unsafeProb (hi - lo)), dirac x)])
                       (superpose [])
  normal        :: repr Real -> repr Prob -> repr (Measure Real)
  normal mu sd  =  lebesgue `bind` \x ->
                   superpose [( exp_ (- (x - mu)^(2::Int)
                                      / fromProb (2 * pow_ sd 2))
                                 / sd / sqrt_ (2 * pi_)
                              , dirac x )]
  factor        :: repr Prob -> repr (Measure ())
  factor p      =  superpose [(p, dirac unit)]
  mix           :: [(repr Prob, repr (Measure a))] -> repr (Measure a)
  mix []        =  errorEmpty
  mix pms       =  let total = sum (map fst pms)
                   in superpose [ (p/total, m) | (p,m) <- pms ]
  categorical   :: [(repr Prob, repr a)] -> repr (Measure a)
  categorical l =  mix [ (p, dirac x) | (p,x) <- l ]

  poisson       :: repr Prob -> repr (Measure Int)
  poisson l     =  countInt `bind` \x ->
                   if_ (and_ [not_ (less x 0), less 0 l])
                       (superpose [(pow_ l (fromInt x) /
                                    gammaFunc (fromInt x + 1) *
                                    exp_ (- fromInt x), dirac x)])
                       (superpose [])

  gamma :: repr Prob -> repr Prob -> repr (Measure Prob)
  gamma shape scale =
    lebesgue `bind` \x ->
    if_ (less 0 x)
        (let x_ = unsafeProb x
             shape_ = fromProb shape in
         superpose [(pow_ x_ (fromProb (shape - 1))
                    * exp_ (- fromProb (x_ / scale))
                    / (pow_ scale shape_ * gammaFunc shape_),
                    dirac (unsafeProb x))])
        (superpose [])

errorEmpty :: a
errorEmpty = error "empty mixture makes no sense"

bind_ :: (Mochastic repr) => repr (Measure a) -> repr (Measure b) ->
                                                 repr (Measure b)
m `bind_` n = m `bind` \_ -> n

liftM :: (Mochastic repr) => (repr a -> repr b) ->
         repr (Measure a) -> repr (Measure b)
liftM f m = m `bind` dirac . f

liftM2 :: (Mochastic repr) => (repr a -> repr b -> repr c) ->
          repr (Measure a) -> repr (Measure b) -> repr (Measure c)
liftM2 f m n = m `bind` \x -> n `bind` \y -> dirac (f x y)

invgamma :: (Mochastic repr) => repr Prob -> repr Prob -> repr (Measure Prob)
invgamma k t = liftM recip (gamma k (recip t))

beta :: (Mochastic repr) => repr Prob -> repr Prob -> repr (Measure Prob)
beta a b = gamma a 1 `bind` \x ->
           gamma b 1 `bind` \y ->
           dirac (x / (x + y))

bern :: (Mochastic repr) => repr Prob -> repr (Measure Bool_)
bern p = categorical [(p, true), (1-p, false)]

class (Base repr) => Summate repr where
  summate :: repr Real -> repr Real -> (repr Int -> repr Prob) -> repr Prob

class (Base repr) => Integrate repr where
  integrate :: repr Real -> repr Real -> (repr Real -> repr Prob) -> repr Prob

class Lambda repr where
  lam :: (repr a -> repr b) -> repr (a -> b)
  app :: repr (a -> b) -> repr a -> repr b
  let_ :: (Lambda repr) => repr a -> (repr a -> repr b) -> repr b
  let_ x f = lam f `app` x
