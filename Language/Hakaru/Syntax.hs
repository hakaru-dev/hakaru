{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, DefaultSignatures,
             DeriveDataTypeable, GADTs, Rank2Types #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Syntax (Real, Prob, Measure, Bool_,
       TypeOf(..), Type(..), typeOf, typeOf1, typeOf2,
       typeMeas, typeProd, typeSum, typeFun,
       EqType(..), eqType, OrdType(..), ordType, Fraction(..),
       errorEmpty,
       Order(..), Base(..), ununit, true, false, if_, fst_, snd_,
       and_, or_, not_, min_, max_,
       Mochastic(..), bind_, liftM, liftM2, beta, bern,
       Integrate(..), Lambda(..)) where

import Prelude hiding (Real)
import Data.Dynamic (Typeable)

infix  4 `less`
infixl 1 `bind`, `bind_`
infixl 9 `app`

------- Types

data Real
data Prob deriving Typeable -- meaning: non-negative real number
data Measure a
type Bool_ = Either () ()

data TypeOf t where
  Meas :: (Type t)           => TypeOf (Measure t)
  Prod :: (Type t1, Type t2) => TypeOf (t1, t2)
  Sum  :: (Type t1, Type t2) => TypeOf (Either t1 t2)
  Fun  :: (Type t1, Type t2) => TypeOf (t1 -> t2)
  One  ::                       TypeOf ()
  Real ::                       TypeOf Real
  Prob ::                       TypeOf Prob

class Type t where theType :: TypeOf t
instance (Type t)           => Type (Measure t)    where theType = Meas
instance (Type t1, Type t2) => Type (t1, t2)       where theType = Prod
instance (Type t1, Type t2) => Type (Either t1 t2) where theType = Sum
instance (Type t1, Type t2) => Type (t1 -> t2)     where theType = Fun
instance                       Type ()             where theType = One
instance                       Type Real           where theType = Real
instance                       Type Prob           where theType = Prob

typeOf :: (Type t) => a t -> TypeOf t
typeOf _ = theType

typeOf1 :: (Type t1) => a (f t1 t2) -> TypeOf t1
typeOf1 _ = theType

typeOf2 :: (Type t2) => a (f t2) -> TypeOf t2
typeOf2 _ = theType

typeMeas :: (Type (Measure t)) => a (Measure t) -> ((Type t) => w) -> w
typeMeas x k = case typeOf x of Meas -> k

typeProd :: (Type (t1, t2)) => a (t1, t2) -> ((Type t1, Type t2) => w) -> w
typeProd x k = case typeOf x of Prod -> k

typeSum :: (Type (Either t1 t2)) => a (Either t1 t2) -> ((Type t1, Type t2) => w) -> w
typeSum x k = case typeOf x of Sum -> k

typeFun :: (Type (t1 -> t2)) => a (t1 -> t2) -> ((Type t1, Type t2) => w) -> w
typeFun x k = case typeOf x of Fun -> k

data EqType t t' where
  Refl :: EqType t t

eqType :: (Type t1, Type t2) => TypeOf t1 -> TypeOf t2 -> Maybe (EqType t1 t2)
eqType a@Meas b@Meas = do Refl <- eqType (typeOf2 a) (typeOf2 b)
                          Just Refl
eqType a@Prod b@Prod = do Refl <- eqType (typeOf1 a) (typeOf1 b)
                          Refl <- eqType (typeOf2 a) (typeOf2 b)
                          Just Refl
eqType a@Sum  b@Sum  = do Refl <- eqType (typeOf1 a) (typeOf1 b)
                          Refl <- eqType (typeOf2 a) (typeOf2 b)
                          Just Refl
eqType a@Fun  b@Fun  = do Refl <- eqType (typeOf1 a) (typeOf1 b)
                          Refl <- eqType (typeOf2 a) (typeOf2 b)
                          Just Refl
eqType   One    One  =    Just Refl
eqType   Real   Real =    Just Refl
eqType   Prob   Prob =    Just Refl
eqType   _      _    =    Nothing

data OrdType t t' where
  LT' :: OrdType t t'
  EQ' :: OrdType t t
  GT' :: OrdType t t'

ordType :: (Type t1, Type t2) => TypeOf t1 -> TypeOf t2 -> OrdType t1 t2
ordType a@Meas b@Meas = case ordType (typeOf2 a) (typeOf2 b) of
                          LT' -> LT'
                          GT' -> GT'
                          EQ' -> EQ'
ordType   Meas   Prod = LT'
ordType   Meas   Sum  = LT'
ordType   Meas   Fun  = LT'
ordType   Meas   One  = LT'
ordType   Meas   Real = LT'
ordType   Meas   Prob = LT'
ordType   Prod   Meas = GT'
ordType a@Prod b@Prod = case ordType (typeOf1 a) (typeOf1 b) of
                          LT' -> LT'
                          GT' -> GT'
                          EQ' -> case ordType (typeOf2 a) (typeOf2 b) of
                                   LT' -> LT'
                                   GT' -> GT'
                                   EQ' -> EQ'
ordType   Prod   Sum  = LT'
ordType   Prod   Fun  = LT'
ordType   Prod   One  = LT'
ordType   Prod   Real = LT'
ordType   Prod   Prob = LT'
ordType   Sum    Meas = GT'
ordType   Sum    Prod = GT'
ordType a@Sum  b@Sum  = case ordType (typeOf1 a) (typeOf1 b) of
                          LT' -> LT'
                          GT' -> GT'
                          EQ' -> case ordType (typeOf2 a) (typeOf2 b) of
                                   LT' -> LT'
                                   GT' -> GT'
                                   EQ' -> EQ'
ordType   Sum    Fun  = LT'
ordType   Sum    One  = LT'
ordType   Sum    Real = LT'
ordType   Sum    Prob = LT'
ordType   Fun    Meas = GT'
ordType   Fun    Prod = GT'
ordType   Fun    Sum  = GT'
ordType a@Fun  b@Fun  = case ordType (typeOf1 a) (typeOf1 b) of
                          LT' -> LT'
                          GT' -> GT'
                          EQ' -> case ordType (typeOf2 a) (typeOf2 b) of
                                   LT' -> LT'
                                   GT' -> GT'
                                   EQ' -> EQ'
ordType   Fun    One  = LT'
ordType   Fun    Real = LT'
ordType   Fun    Prob = LT'
ordType   One    Meas = GT'
ordType   One    Prod = GT'
ordType   One    Sum  = GT'
ordType   One    Fun  = GT'
ordType   One    One  = EQ'
ordType   One    Real = LT'
ordType   One    Prob = LT'
ordType   Real   Meas = GT'
ordType   Real   Prod = GT'
ordType   Real   Sum  = GT'
ordType   Real   Fun  = GT'
ordType   Real   One  = GT'
ordType   Real   Real = EQ'
ordType   Real   Prob = LT'
ordType   Prob   Meas = GT'
ordType   Prob   Prod = GT'
ordType   Prob   Sum  = GT'
ordType   Prob   Fun  = GT'
ordType   Prob   One  = GT'
ordType   Prob   Real = GT'
ordType   Prob   Prob = EQ'

class (Type a) => Fraction a where
  fractionCase :: f Real -> f Prob -> f a
  fractionRepr :: (Base repr) =>
                  ((Order repr a, Fractional (repr a)) => f repr a) -> f repr a

instance Fraction Real where
  fractionCase k _ = k
  fractionRepr k   = k

instance Fraction Prob where
  fractionCase _ k = k
  fractionRepr k   = k

------- Terms

class Order repr a where
  less :: repr a -> repr a -> repr Bool_

class (Order repr Real, Floating (repr Real),
       Order repr Prob, Fractional (repr Prob)) => Base repr where
  unit       :: repr ()
  pair       :: (Type a, Type b) => repr a -> repr b -> repr (a,b)
  unpair     :: (Type a, Type b) => repr (a,b) ->
                (repr a -> repr b -> repr c) -> repr c
  inl        :: (Type a, Type b) => repr a -> repr (Either a b)
  inr        :: (Type a, Type b) => repr b -> repr (Either a b)
  uneither   :: (Type a, Type b) => repr (Either a b) ->
                (repr a -> repr c) -> (repr b -> repr c) -> repr c

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

ununit :: repr () -> repr a -> repr a
ununit _ e = e

true, false :: (Base repr) => repr Bool_
true  = inl unit
false = inr unit

if_ :: (Base repr) => repr Bool_ -> repr c -> repr c -> repr c
if_ e et ef = uneither e (const et) (const ef)

fst_ :: (Base repr, Type a, Type b) => repr (a,b) -> repr a
fst_ ab = unpair ab (\a _ -> a)

snd_ :: (Base repr, Type a, Type b) => repr (a,b) -> repr b
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
  bind          :: (Type a) => repr (Measure a) ->
                   (repr a -> repr (Measure b)) -> repr (Measure b)
  lebesgue      :: repr (Measure Real)
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

errorEmpty :: a
errorEmpty = error "empty mixture makes no sense"

bind_ :: (Type a, Mochastic repr) => repr (Measure a) -> repr (Measure b) ->
                                     repr (Measure b)
m `bind_` n = m `bind` \_ -> n

liftM :: (Type a, Mochastic repr) => (repr a -> repr b) ->
         repr (Measure a) -> repr (Measure b)
liftM f m = m `bind` dirac . f

liftM2 :: (Type a, Type b, Mochastic repr) => (repr a -> repr b -> repr c) ->
          repr (Measure a) -> repr (Measure b) -> repr (Measure c)
liftM2 f m n = m `bind` \x -> n `bind` \y -> dirac (f x y)

beta :: (Mochastic repr) => repr Real -> repr Real -> repr (Measure Prob)
beta a b = uniform 0 1 `bind` \x ->
           superpose [( pow_ (unsafeProb x    ) (a-1) *
                        pow_ (unsafeProb (1-x)) (b-1) / betaFunc a b
                      , dirac (unsafeProb x) )]

bern :: (Mochastic repr) => repr Prob -> repr (Measure Bool_)
bern p = categorical [(p, true), (1-p, false)]

class (Base repr) => Integrate repr where
  integrate :: repr Real -> repr Real -> (repr Real -> repr Prob) -> repr Prob
  infinity, negativeInfinity :: repr Real

class Lambda repr where
  lam :: (repr a -> repr b) -> repr (a -> b)
  app :: repr (a -> b) -> repr a -> repr b
  let_ :: (Lambda repr) => repr a -> (repr a -> repr b) -> repr b
  let_ x f = lam f `app` x
