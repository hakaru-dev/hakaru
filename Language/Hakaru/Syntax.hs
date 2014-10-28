{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, DefaultSignatures #-}
{-# OPTIONS -W #-}

module Language.Hakaru.Syntax (Real, Prob, Measure, errorEmpty,
       Order(..), Base(..), fst_, snd_, and_, min_, max_,
       Mochastic(..), bind_, liftM, liftM2, beta, bern,
       Disintegrate(..), condition, density,
       Integrate(..), Lambda(..)) where

import Prelude hiding (Real)

-- A small probabilistic language with conditioning

infixl 1 `bind`, `bind_`
infixl 9 `app`

data Real
data Prob -- meaning: non-negative real number
data Measure a

class Order repr a where
  less :: repr a -> repr a -> repr Bool

class (Order repr Real, Floating (repr Real),
       Order repr Prob, Fractional (repr Prob)) => Base repr where
  unit       :: repr ()
  pair       :: repr a -> repr b -> repr (a,b)
  unpair     :: repr (a,b) -> (repr a -> repr b -> repr c) -> repr c
  inl        :: repr a -> repr (Either a b)
  inr        :: repr b -> repr (Either a b)
  uneither   :: repr (Either a b) -> (repr a -> repr c) ->
                                     (repr b -> repr c) -> repr c

  true, false :: repr Bool
  if_ :: repr Bool -> repr c -> repr c -> repr c

  unsafeProb :: repr Real -> repr Prob
  fromProb   :: repr Prob -> repr Real

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

  betaFunc         ::                     repr Real -> repr Real -> repr Prob
  default betaFunc :: (Integrate repr) => repr Real -> repr Real -> repr Prob
  betaFunc a b = integrate 0 1 $ \x ->
    pow_ (unsafeProb x) (a-1) * pow_ (unsafeProb (1-x)) (b-1)

  fix :: (repr a -> repr a) -> repr a
  fix f = x where x = f x

fst_ :: (Base repr) => repr (a,b) -> repr a
fst_ ab = unpair ab (\a _ -> a)

snd_ :: (Base repr) => repr (a,b) -> repr b
snd_ ab = unpair ab (\_ b -> b)

and_ :: (Base repr) => [repr Bool] -> repr Bool
and_ []     = true
and_ [b]    = b
and_ (b:bs) = if_ b (and_ bs) false

min_, max_ :: (Order repr a, Base repr) => repr a -> repr a -> repr a
min_ x y = if_ (less x y) x y
max_ x y = if_ (less x y) y x

class (Base repr) => Mochastic repr where
  dirac         :: repr a -> repr (Measure a)
  bind          :: repr (Measure a) -> (repr a -> repr (Measure b)) ->
                   repr (Measure b)
  lebesgue      :: repr (Measure Real)
  superpose     :: [(repr Prob, repr (Measure a))] -> repr (Measure a)

  uniform       :: repr Real -> repr Real -> repr (Measure Real)
  uniform lo hi =  lebesgue `bind` \x ->
                   if_ (and_ [less lo x, less x hi])
                       (superpose [(recip (unsafeProb (hi - lo)), dirac x)])
                       (superpose [])
  normal        :: repr Real -> repr Prob -> repr (Measure Real)
  normal mu sd  =  lebesgue `bind` \x ->
                   superpose [( exp_ (- (x - mu)^2 / fromProb (2 * pow_ sd 2))
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

beta :: (Mochastic repr) => repr Real -> repr Real -> repr (Measure Prob)
beta a b = uniform 0 1 `bind` \x ->
           superpose [( pow_ (unsafeProb x    ) (a-1) *
                        pow_ (unsafeProb (1-x)) (b-1) / betaFunc a b
                      , dirac (unsafeProb x) )]

bern :: (Mochastic repr) => repr Prob -> repr (Measure Bool)
bern p = categorical [(p, true), (1-p, false)]

class (Mochastic repr) => Disintegrate repr where
  disintegrate :: repr (Measure a) -> repr (Measure (a,b)) ->
                  repr a -> repr (Measure b)

condition :: (Disintegrate repr) => repr (Measure (a,b)) ->
                                    repr a -> repr (Measure b)
condition m = disintegrate (liftM fst_ m) m

density :: (Disintegrate repr) => repr (Measure a) -> repr (Measure a) ->
                                  repr a -> repr (Measure Real)
density ambient m = disintegrate ambient (liftM (`pair` 1) m)

class (Base repr) => Integrate repr where
  integrate :: repr Real -> repr Real -> (repr Real -> repr Prob) -> repr Prob
  infinity, negativeInfinity :: repr Real

class Lambda repr where
  lam :: (repr a -> repr b) -> repr (a -> b)
  app :: repr (a -> b) -> repr a -> repr b
