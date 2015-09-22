{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, DefaultSignatures,
             GADTs, Rank2Types, DataKinds, KindSignatures, TypeFamilies, 
             StandaloneDeriving, DeriveDataTypeable, PolyKinds #-}
{-# OPTIONS -Wall -Werror #-}

module Language.Hakaru.Syntax (Hakaru(..), HakaruFun(..), 
       Order_(..), lesseq, Number(..), Fraction(..), 
       Order(..), Base(..), ununit, fst_, snd_, swap_,
       and_, or_, not_, min_, max_,
       summateV, sumV, normalizeV, dirichlet,
       mapWithIndex, mapV, zipWithV, zipV, rangeV, constV, unitV,
       fromListV, concatV, unzipV,
       Mochastic(..), bind_, factor, weight, bindx, bindo, liftM, liftM2,
       positiveUniform, invgamma, exponential, chi2, bern,
       cauchy, laplace, student, weibull, mix, geometric, negativeBinomial,
       binomial, multinomial,
       Integrate(..), Lambda(..), lam2, lam3, app2, app3, Lub(..)) where

import Prelude hiding (Real)
import Data.Typeable (Typeable)

infix  4 `less`, `equal`, `less_`, `equal_`
infixl 1 `bind`, `bind_`, `bindx`
infixl 9 `app`
infixr 9 `pair`

------- The universe/kind of Hakaru types
data Hakaru star
    = HNat -- TODO: finish incorporating this everywhere...
    | HInt
    | HProb -- meaning: non-negative real number (not [0,1] !)
    | HReal
    | HMeasure (Hakaru star)
    | HArray (Hakaru star)
    | HFun (Hakaru star) (Hakaru star)
    | HBool
    | HUnit
    | HPair (Hakaru star) (Hakaru star)
    | HEither (Hakaru star) (Hakaru star)
    -- Used in "Language.Hakaru.Embed"
    -- The lists-of-lists are sum-of-products functors. The application
    -- form allows us to unroll fixpoints: @HMu sop ~= sop :$ HMu sop@.
    | HMu [[HakaruFun star]]
    | [[HakaruFun star]] :$ Hakaru star
    | HTag star [[HakaruFun star]]
    -- Used in "Language.Hakaru.Expect"
    | HList (Hakaru star)
    -- Used in "Language.Hakaru.Sample"
    | HMaybe (Hakaru star)
    -- TODO: arbitrary embedding of Haskell types

-- | The identity and constant functors on @Hakaru*@. This gives
-- us limited access to type-variables in @Hakaru*@, for use in
-- recursive sums-of-products. Notably, however, it only allows a
-- single variable (namely the one bound by the closest binder) so
-- it can't encode mutual recursion or other non-local uses of
-- multiple binders.
--
-- Products and sums are represented as lists, so they aren't
-- in this datatype.
data HakaruFun star = Id | K (Hakaru star)

-- N.B., The @Proxy@ type from "Data.Proxy" is polykinded, so it works for @Hakaru*@ too. However, it is _not_ Typeable!

-- TODO: these instances are only used in 'Language.Hakaru.Simplify.closeLoop'; it would be cleaner to remove these instances and reimplement that function to work without them.
deriving instance Typeable 'HNat
deriving instance Typeable 'HInt
deriving instance Typeable 'HReal
deriving instance Typeable 'HProb
deriving instance Typeable 'HMeasure
deriving instance Typeable 'HArray
deriving instance Typeable 'HFun
deriving instance Typeable 'HBool
deriving instance Typeable 'HUnit
deriving instance Typeable 'HPair
deriving instance Typeable 'HEither
deriving instance Typeable 'HMu
deriving instance Typeable 'HTag
deriving instance Typeable (:$)
deriving instance Typeable 'HList
deriving instance Typeable 'HMaybe
deriving instance Typeable 'Id
deriving instance Typeable 'K



-- TODO: We used to require @Typeable a@... but now what?
class Order_ (a :: Hakaru *) where
  less_, equal_  :: (Base repr              ) => repr a -> repr a -> repr 'HBool
  default less_  :: (Base repr, Order repr a) => repr a -> repr a -> repr 'HBool
  default equal_ :: (Base repr, Order repr a) => repr a -> repr a -> repr 'HBool
  less_  = less
  equal_ = equal

lesseq :: (Order_ a, Base repr) => repr a -> repr a -> repr 'HBool
lesseq x y = or_ [less_ x y, equal_ x y]

--instance Order_ 'HNat
instance Order_ 'HInt
instance Order_ 'HReal
instance Order_ 'HProb

instance Order_ 'HUnit where
  less_  _ _ = false
  equal_ _ _ = true

instance Order_ 'HBool where
  less_  x y = if_ x false y
  equal_ x y = if_ x y (not_ y)

instance (Order_ a, Order_ b) => Order_ ('HPair a b) where
  less_  ab1 ab2 = unpair ab1 (\a1 b1 ->
                   unpair ab2 (\a2 b2 ->
                   or_ [less_ a1 a2, and_ [equal_ a1 a2, less_ b1 b2]]))
  equal_ ab1 ab2 = unpair ab1 (\a1 b1 ->
                   unpair ab2 (\a2 b2 ->
                   and_ [equal_ a1 a2, equal_ b1 b2]))

instance (Order_ a, Order_ b) => Order_ ('HEither a b) where
  less_  ab1 ab2 = uneither ab1
                     (\a1 -> uneither ab2 (\a2 -> less_ a1 a2) (\_ -> true))
                     (\b1 -> uneither ab2 (\_ -> false) (\b2 -> less_ b1 b2))
  equal_ ab1 ab2 = uneither ab1
                     (\a1 -> uneither ab2 (\a2 -> equal_ a1 a2) (\_ -> false))
                     (\b1 -> uneither ab2 (\_ -> false) (\b2 -> equal_ b1 b2))

instance (Order_ a) => Order_ ('HArray a) where
  less_ _ _ = undefined
  equal_ _ _ = undefined

-- TODO: add HNat to the numberCase
-- TODO: we can mostly get rid of this class: numberRepr isn't used anywhere, and numberCase is only used once in Lazy.hs to define fromInteger for Hnf.
class (Order_ a) => Number (a :: Hakaru *) where
  numberCase :: f 'HInt -> f 'HReal -> f 'HProb -> f a
  numberRepr :: (Base repr) =>
                ((Order repr a, Num (repr a)) => f repr a) -> f repr a

-- TODO: we can mostly get rid of this class: fractionRepr isn't used anywhere, and fractionCase is only used once in Lazy.hs to define fromRational for Hnf. However, unsafeProbFraction is used extensively in Lazy.hs
class (Number a) => Fraction (a :: Hakaru *) where
  fractionCase :: f 'HReal -> f 'HProb -> f a
  fractionRepr :: (Base repr) =>
                  ((Order repr a, Fractional (repr a)) => f repr a) -> f repr a
  unsafeProbFraction :: (Base repr) => repr a -> repr 'HProb
  piFraction         :: (Base repr) => repr a
  expFraction        :: (Base repr) => repr 'HReal -> repr a
  logFraction        :: (Base repr) => repr a -> repr 'HReal
  erfFraction        :: (Base repr) => repr a -> repr a

instance Number 'HInt where
  numberCase k _ _ = k
  numberRepr k     = k

instance Number 'HReal where
  numberCase _ k _ = k
  numberRepr k     = k

instance Number 'HProb where
  numberCase _ _ k = k
  numberRepr k     = k

instance Fraction 'HReal where
  fractionCase k _   = k
  fractionRepr k     = k
  unsafeProbFraction = unsafeProb
  piFraction         = pi
  expFraction        = exp
  logFraction        = log
  erfFraction        = erf

instance Fraction 'HProb where
  fractionCase _ k   = k
  fractionRepr k     = k
  unsafeProbFraction = id
  piFraction         = pi_
  expFraction        = exp_
  logFraction        = log_
  erfFraction        = erf_

------- Terms

class (Number a) => Order (repr :: Hakaru * -> *) (a :: Hakaru *) where
  less          ::                repr a -> repr a -> repr 'HBool
  equal         ::                repr a -> repr a -> repr 'HBool
  default equal :: (Base repr) => repr a -> repr a -> repr 'HBool
  equal a b = not_ (or_ [less a b, less b a])

-- TODO: incorporate HNat
class (Order repr 'HInt , Num        (repr 'HInt ),
       Order repr 'HReal, Floating   (repr 'HReal),
       Order repr 'HProb, Fractional (repr 'HProb))
    => Base (repr :: Hakaru * -> *) where
  unit       :: repr 'HUnit
  pair       :: repr a -> repr b -> repr ('HPair a b)
  unpair     :: repr ('HPair a b) -> (repr a -> repr b -> repr c) -> repr c
  inl        :: repr a -> repr ('HEither a b)
  inr        :: repr b -> repr ('HEither a b)
  uneither   :: repr ('HEither a b) ->
                (repr a -> repr c) -> (repr b -> repr c) -> repr c
  true       :: repr 'HBool
  false      :: repr 'HBool
  if_        :: repr 'HBool -> repr c -> repr c -> repr c

  unsafeProb :: repr 'HReal -> repr 'HProb
  fromProb   :: repr 'HProb -> repr 'HReal
  fromInt    :: repr 'HInt  -> repr 'HReal

  pi_      :: repr 'HProb
  pi_      =  unsafeProb pi
  exp_     :: repr 'HReal -> repr 'HProb
  exp_     =  unsafeProb . exp
  erf      :: repr 'HReal -> repr 'HReal
  erf_     :: repr 'HProb -> repr 'HProb
  erf_     =  unsafeProb . erf . fromProb
  log_     :: repr 'HProb -> repr 'HReal
  log_     =  log . fromProb
  sqrt_    :: repr 'HProb -> repr 'HProb
  sqrt_ x  =  pow_ x (1/2)
  pow_     :: repr 'HProb -> repr 'HReal -> repr 'HProb
  pow_ x y =  exp_ (log_ x * y)

  infinity, negativeInfinity :: repr 'HReal

  gammaFunc         ::                     repr 'HReal -> repr 'HProb
  default gammaFunc :: (Integrate repr) => repr 'HReal -> repr 'HProb
  gammaFunc t = integrate 0 infinity $ \x ->
    pow_ (unsafeProb x) (t-1) * exp_ (-x)

  betaFunc         ::                     repr 'HProb -> repr 'HProb -> repr 'HProb
  default betaFunc :: (Integrate repr) => repr 'HProb -> repr 'HProb -> repr 'HProb
  betaFunc a b = integrate 0 1 $ \x -> pow_ (unsafeProb x    ) (fromProb a - 1)
                                     * pow_ (unsafeProb (1-x)) (fromProb b - 1)

  vector           :: repr 'HInt -> (repr 'HInt -> repr a) -> repr ('HArray a)
  empty            :: repr ('HArray a)
  index            :: repr ('HArray a) -> repr 'HInt -> repr a
  size             :: repr ('HArray a) -> repr 'HInt
  reduce           :: (repr a -> repr a -> repr a) ->
                      repr a -> repr ('HArray a) -> repr a
  vector           =  error "vector unimplemented"
  empty            =  error "empty unimplemented"
  index            =  error "index unimplemented"
  size             =  error "size unimplemented"
  reduce           =  error "reduce unimplemented"

  fix :: (repr a -> repr a) -> repr a
  fix f = x where x = f x

ununit :: repr 'HUnit -> repr a -> repr a
ununit _ e = e

fst_ :: (Base repr) => repr ('HPair a b) -> repr a
fst_ ab = unpair ab (\a _ -> a)

snd_ :: (Base repr) => repr ('HPair a b) -> repr b
snd_ ab = unpair ab (\_ b -> b)

swap_ :: (Base repr) => repr ('HPair a b) -> repr ('HPair b a)
swap_ ab = unpair ab (flip pair)

and_ :: (Base repr) => [repr 'HBool] -> repr 'HBool
and_ []     = true
and_ [b]    = b
and_ (b:bs) = if_ b (and_ bs) false

or_ :: (Base repr) => [repr 'HBool] -> repr 'HBool
or_ []      = false
or_ [b]     = b
or_ (b:bs)  = if_ b true (or_ bs)

not_ :: (Base repr) => repr 'HBool -> repr 'HBool
not_ a = if_ a false true

min_, max_ :: (Order_ a, Base repr) => repr a -> repr a -> repr a
min_ x y = if_ (less_ x y) x y
max_ x y = if_ (less_ x y) y x

class (Base repr) => Mochastic (repr :: Hakaru * -> *) where
  dirac         :: repr a -> repr ('HMeasure a)
  bind          :: repr ('HMeasure a) ->
                   (repr a -> repr ('HMeasure b)) -> repr ('HMeasure b)
  lebesgue      :: repr ('HMeasure 'HReal)
  counting      :: repr ('HMeasure 'HInt)
  superpose     :: [(repr 'HProb, repr ('HMeasure a))] -> repr ('HMeasure a)
  categorical   :: repr ('HArray 'HProb) -> repr ('HMeasure 'HInt)
  categorical v =  counting `bind` \i ->
                   if_ (and_ [not_ (less i 0), less i (size v)])
                       (weight (index v i / sumV v) (dirac i))
                       (superpose [])

  uniform       :: repr 'HReal -> repr 'HReal -> repr ('HMeasure 'HReal)
  uniform lo hi =  lebesgue `bind` \x ->
                   if_ (and_ [less lo x, less x hi])
                       (superpose [(recip (unsafeProb (hi - lo)), dirac x)])
                       (superpose [])
  normal        :: repr 'HReal -> repr 'HProb -> repr ('HMeasure 'HReal)
  normal mu sd  =  lebesgue `bind` \x ->
                   superpose [( exp_ (- (x - mu)^(2::Int)
                                      / fromProb (2 * pow_ sd 2))
                                 / sd / sqrt_ (2 * pi_)
                              , dirac x )]
  poisson       :: repr 'HProb -> repr ('HMeasure 'HInt)
  poisson l     =  counting `bind` \x ->
                   if_ (and_ [not_ (less x 0), less 0 l])
                       (superpose [( pow_ l (fromInt x)
                                   / gammaFunc (fromInt x + 1)
                                   / exp_ (fromProb l)
                                   , dirac x )])
                       (superpose [])

  gamma :: repr 'HProb -> repr 'HProb -> repr ('HMeasure 'HProb)
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

  beta :: repr 'HProb -> repr 'HProb -> repr ('HMeasure 'HProb)
  beta a b = uniform 0 1 `bind` \x ->
             superpose [( pow_ (unsafeProb x    ) (fromProb a - 1)
                        * pow_ (unsafeProb (1-x)) (fromProb b - 1)
                        / betaFunc a b
                        , dirac (unsafeProb x) )]

  dp :: repr 'HProb -> repr ('HMeasure a) -> repr ('HMeasure ('HMeasure a))
  dp =  error "dp unimplemented"

  plate :: repr ('HArray ('HMeasure          a)) ->
           repr (         'HMeasure ('HArray a))
  chain :: (Lambda repr) =>
           repr ('HArray ('HFun s ('HMeasure         ('HPair a s)))) ->
           repr (         'HFun s ('HMeasure ('HPair ('HArray a) s)))
  plate v = reduce r z (mapV m v)
    where r   = liftM2 concatV
          z   = dirac empty
          m a = liftM (vector 1 . const) a
  chain v = reduce r z (mapV m v)
    where r x y = lam (\s -> app x s `bind` \v1s1 ->
                             unpair v1s1 $ \v1 s1 ->
                             app y s1 `bind` \v2s2 ->
                             unpair v2s2 $ \v2 s2 ->
                             dirac (pair (concatV v1 v2) s2))
          z     = lam (\s -> dirac (pair empty s))
          m a   = lam (\s -> liftM (`unpair` pair . vector 1 . const)
                                   (app a s))

bind_
    :: (Mochastic repr)
    => repr ('HMeasure a)
    -> repr ('HMeasure b)
    -> repr ('HMeasure b)
m `bind_` n = m `bind` \_ -> n

factor
    :: (Mochastic repr)
    => repr 'HProb
    -> repr ('HMeasure 'HUnit)
factor p = weight p (dirac unit)

weight
    :: (Mochastic repr)
    => repr 'HProb
    -> repr ('HMeasure w)
    -> repr ('HMeasure w)
weight p m = superpose [(p, m)]

bindx
    :: (Mochastic repr)
    => repr ('HMeasure a)
    -> (repr a -> repr ('HMeasure b))
    -> repr ('HMeasure ('HPair a b))
m `bindx` k = m `bind` \a -> k a `bind` \b -> dirac (pair a b)

-- Kleisli composition
-- bindo f g = \x -> do y <- f x
--                      z <- g y
--                      return z

bindo
    :: (Mochastic repr, Lambda repr)
    => repr ('HFun a ('HMeasure b))
    -> repr ('HFun b ('HMeasure c))
    -> repr ('HFun a ('HMeasure c))
bindo f g = lam (\x -> app f x `bind` app g)

liftM
    :: (Mochastic repr)
    => (repr a -> repr b)
    -> repr ('HMeasure a) -> repr ('HMeasure b)
liftM f m = m `bind` dirac . f

liftM2
    :: (Mochastic repr)
    => (repr a -> repr b -> repr c)
    -> repr ('HMeasure a) -> repr ('HMeasure b) -> repr ('HMeasure c)
liftM2 f m n = m `bind` \x -> n `bind` \y -> dirac (f x y)

positiveUniform
    :: (Mochastic repr)
    => repr 'HProb -> repr 'HProb -> repr ('HMeasure 'HProb)
positiveUniform lo hi = liftM unsafeProb (uniform (fromProb lo) (fromProb hi))

invgamma
    :: (Mochastic repr)
    => repr 'HProb -> repr 'HProb -> repr ('HMeasure 'HProb)
invgamma k t = liftM recip (gamma k (recip t))

exponential :: (Mochastic repr) => repr 'HProb -> repr ('HMeasure 'HProb)
exponential l = gamma 1 l

chi2 :: (Mochastic repr) => repr 'HProb -> repr ('HMeasure 'HProb)
chi2 v = gamma (v/2) 2

cauchy
    :: (Mochastic repr)
    => repr 'HReal -> repr 'HProb -> repr ('HMeasure 'HReal)
cauchy loc scale = normal 0 1 `bind` \x ->
                   normal 0 1 `bind` \y ->
                   dirac $ loc + fromProb scale * (x/y)

laplace
    :: (Mochastic repr)
    => repr 'HReal -> repr 'HProb -> repr ('HMeasure 'HReal)
laplace loc scale = exponential 1 `bind` \v ->
                    normal 0 1 `bind` \z ->
                    dirac $ loc + z * fromProb (scale * sqrt_ (2*v))

student
    :: (Mochastic repr)
    => repr 'HReal -> repr 'HProb -> repr ('HMeasure 'HReal)
student loc v = normal loc 1 `bind` \z ->
                chi2 v `bind` \df ->
                dirac $ z * fromProb (sqrt_ (v/df))

weibull
    :: (Mochastic repr)
    => repr 'HProb -> repr 'HProb -> repr ('HMeasure 'HProb)
weibull b k = exponential 1 `bind` \x ->
              dirac $ b * pow_ x (fromProb (recip k))

bern :: (Mochastic repr) => repr 'HProb -> repr ('HMeasure 'HBool)
bern p = superpose [(p, dirac true), (1-p, dirac false)]

mix :: (Mochastic repr) => repr ('HArray 'HProb) -> repr ('HMeasure 'HInt)
mix v = weight (sumV v) (categorical v)

class (Base repr) => Integrate (repr :: Hakaru * -> *) where
  integrate :: repr 'HReal -> repr 'HReal -> (repr 'HReal -> repr 'HProb) -> repr 'HProb
  summate   :: repr 'HReal -> repr 'HReal -> (repr 'HInt  -> repr 'HProb) -> repr 'HProb

summateV :: (Integrate repr) => repr ('HArray 'HProb) -> repr 'HProb
summateV x = summate 0 (fromInt (size x - 1)) (index x)

sumV :: (Base repr, Num (repr a)) => repr ('HArray a) -> repr a
sumV = reduce (+) 0 -- equivalent to summateV for the type Prob

binomial
    :: (Mochastic repr)
    => repr 'HInt -> repr 'HProb -> repr ('HMeasure 'HInt)
binomial n p = liftM sumV
             $ plate (constV n (liftM (\x -> if_ x 1 0) (bern p)))

negativeBinomial
    :: (Mochastic repr)
    => repr 'HInt -> repr 'HProb -> repr ('HMeasure 'HInt)
negativeBinomial r p =
    gamma (unsafeProb $ fromInt r) (recip p - 1) `bind` \l ->
    poisson l

geometric :: (Mochastic repr) => repr 'HProb -> repr ('HMeasure 'HInt)
geometric = negativeBinomial 1

multinomial
    :: (Mochastic repr)
    => repr 'HInt
    -> repr ('HArray 'HProb)
    -> repr ('HMeasure ('HArray 'HProb))
multinomial n v =
    reduce (liftM2 (zipWithV (+)))
        (dirac (constV (size v) 0))
        (constV n (liftM (unitV (size v))
            (categorical v)))

normalizeV
    :: (Integrate repr, Lambda repr)
    => repr ('HArray 'HProb) -> repr ('HArray 'HProb)
normalizeV x = mapV (/ summateV x) x

dirichlet
    :: (Lambda repr, Mochastic repr, Integrate repr)
    => repr ('HArray 'HProb) -> repr ('HMeasure ('HArray 'HProb))
dirichlet a = liftM normalizeV (plate (mapV (`gamma` 1) a))

fromListV :: (Base repr) => [repr a] -> repr ('HArray a)
fromListV []     = empty
fromListV (x:xs) = vector
  (fromIntegral (length xs))
  (let loop y []     _ _ = y
       loop y (z:zs) j i = if_ (equal i (fromIntegral (j::Int)))
                               y
                               (loop z zs (j+1) i)
   in loop x xs 0)

rangeV :: (Base repr) => repr 'HInt -> repr ('HArray 'HInt)
rangeV n = vector n id

constV :: (Base repr) => repr 'HInt -> repr b -> repr ('HArray b)
constV s c = vector s (const c)

unitV :: (Base repr) => repr 'HInt -> repr 'HInt -> repr ('HArray 'HProb)
unitV s i = vector s (\j -> if_ (equal i j) 1 0)

concatV
    :: (Base repr)
    => repr ('HArray a) -> repr ('HArray a) -> repr ('HArray a)
concatV v1 v2 =
    vector (size v1 + size v2) $ \i ->
        if_ (less i (size v1))
            (index v1 i)
            (index v2 (i - size v1))

unzipV
    :: (Base repr)
    => repr ('HArray ('HPair a b)) -> repr ('HPair ('HArray a) ('HArray b))
unzipV v = pair (mapV fst_ v) (mapV snd_ v)

mapWithIndex
    :: (Base repr)
    => (repr 'HInt -> repr a -> repr b)
    -> repr ('HArray a)
    -> repr ('HArray b)
mapWithIndex f v = vector (size v) (\i -> f i (index v i))

mapV
    :: (Base repr)
    => (repr a -> repr b) -> repr ('HArray a) -> repr ('HArray b)
mapV f = mapWithIndex (const f)

-- | Assume (without checking) that the bounds of the two
-- vectors are the same
zipWithV
    :: (Base repr)
    => (repr a -> repr b -> repr c)
    -> repr ('HArray a) -> repr ('HArray b) -> repr ('HArray c)
zipWithV f v1 v2 =
    vector (size v1) (\i -> f (index v1 i) (index v2 i))

zipV
    :: (Base repr)
    => repr ('HArray a) -> repr ('HArray b) -> repr ('HArray ('HPair a b))
zipV = zipWithV pair

class Lambda (repr :: Hakaru * -> *) where
  lam  :: (repr a -> repr b) -> repr ('HFun a b)
  app  :: repr ('HFun a b) -> repr a -> repr b
  let_ :: (Lambda repr) => repr a -> (repr a -> repr b) -> repr b
  let_ x f = lam f `app` x

lam2 :: (Lambda r) => (r a -> r b -> r c) -> r ('HFun a ('HFun b c))
lam2 f = lam (lam . f)

lam3
    :: (Lambda r)
    => (r a -> r b -> r c -> r d)
    -> r ('HFun a ('HFun b ('HFun c d)))
lam3 f = lam (lam2 . f)

app2 :: (Lambda r) => r ('HFun a ('HFun b c)) -> (r a -> r b -> r c)
app2 f = app . app f

app3
    :: (Lambda r)
    => r ('HFun a ('HFun b ('HFun c d)))
    -> (r a -> r b -> r c -> r d)
app3 f = app2 . app f

class Lub (repr :: Hakaru * -> *) where
  lub :: repr a -> repr a -> repr a -- two ways to compute the same thing
  bot :: repr a -- no way to compute anything (left and right identity for lub)
