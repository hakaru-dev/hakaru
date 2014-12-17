{-# LANGUAGE MultiParamTypeClasses, TypeFamilies,
             FlexibleInstances, FlexibleContexts,
             ConstraintKinds, DataKinds #-}

module Language.Hakaru.Vector (Nat(..), fromNat, toNat, Repeat,
       Vector(..), toNestedPair, fromNestedPair, fromList,
       sequenceA, mapM, sequence, mapAccum, iota, mapC) where

import Prelude hiding (Real, mapM, sequence, abs)
import qualified Control.Applicative as A
import Language.Hakaru.Syntax
-- import Language.Hakaru.Sample (Sample(unSample))
import Control.Applicative (WrappedMonad(..))
import Control.Monad.State (runState, state)
import Control.Monad.Cont (runCont, cont)

infixl 4 <*>, <$>

-- Type-level natural numbers (starting at 1, not 0)

data Nat = I | D Nat | SD Nat deriving (Eq, Ord, Show, Read)

fromNat :: (Num a) => Nat -> a
fromNat I      = 1
fromNat (D n)  = 2 * fromNat n
fromNat (SD n) = 2 * fromNat n + 1

toNat :: (Integral a) => a -> Nat
toNat n | (d,m) == (0,1) = I
        | d <= 0         = error "toNat: must be positive"
        | m == 0         = D (toNat d)
        | m == 1         = SD (toNat d)
  where (d,m) = divMod n 2

-- Homogeneous vectors of a given type-level length

type Length a as = Length' as
type family   Length' as :: Nat
type instance Length' ()                  = I
type instance Length' ((as, (a, as)), ()) = D  (Length' as)
  --                  ^             ^^^^^
  -- This is necessary to avoid "Conflicting family instance declarations"
  -- between the type instance above and the type instance below in GHC 7.8.
  -- As for why they should conflict, see
  -- http://stackoverflow.com/questions/18369827/why-are-type-instances-a-a-and-a-a-a-conflicting-in-ghc-7-8
  -- http://ghc.haskell.org/trac/ghc/ticket/8154
type instance Length' ((a, as), (a, as))  = SD (Length' as)

type Repeat n a = (a, Repeat' n a)
type family   Repeat' (n :: Nat) a
type instance Repeat' I      a = ()
type instance Repeat' (D n)  a = ((Repeat' n a, Repeat n a), ())
type instance Repeat' (SD n) a = (Repeat n a, Repeat n a)

-- A theorem that GHC can only infer concrete instances of

type SameLength as b = Length' as ~ Length' (Repeat' (Length' as) b)

class (as ~ Repeat' (Length' as) a) => Vector a as where
  pure            :: a -> (a, as)
  (<*>)           :: (SameLength as (a -> b), SameLength as b) =>
                     Repeat (Length a as) (a -> b) ->
                     (a, as) ->
                     Repeat (Length a as) b
  (<$>)           :: (SameLength as b) =>
                     (a -> b) ->
                     (a, as) ->
                     Repeat (Length a as) b
  traverse        :: (A.Applicative f, SameLength as b) =>
                     (a -> f b) -> (a, as) -> f (Repeat (Length a as) b)
  toNestedPair'   :: (SameLength as (repr a), Base repr) =>
                     Repeat (Length a as) (repr a) -> (repr a, repr as)
  fromNestedPair' :: (SameLength as (repr a), Base repr) =>
                     repr a -> repr as ->
                     (Repeat (Length a as) (repr a) -> repr w) -> repr w
  toList          :: (a, as) -> [a]
  fromList'       :: [a] -> ((a, as), [a])

toNestedPair :: (Vector a as, SameLength as (repr a), Base repr) =>
                Repeat (Length a as) (repr a) -> repr (a, as)
toNestedPair = uncurry pair . toNestedPair'

fromNestedPair :: (Vector a as, SameLength as (repr a), Base repr) =>
                  repr (a, as) ->
                  (Repeat (Length a as) (repr a) -> repr w) -> repr w
fromNestedPair raas k = unpair raas (\ra ras -> fromNestedPair' ra ras k)

fromList :: (Vector a as) => [a] -> (a, as)
fromList = fst . fromList'

instance Vector a () where
  pure a                 = (a, ())
  (ab, ()) <*> (a, ())   = (ab a, ())
  ab <$> (a, ())         = (ab a, ())
  traverse f (a, ())     = (\b -> (b,())) A.<$> f a
  toNestedPair' (a, ())  = (a, unit)
  fromNestedPair' ra _ k = k (ra, ())
  toList (a, ())         = [a]
  fromList' (a : as)     = ((a, ()), as)
  fromList' []           = error "should not happen - fromList' of empty"

instance (Vector a as) => Vector a ((as, (a, as)), ()) where
  pure a                          = case pure a of p@(b,p') -> (b,((p',p),()))
  (ab,((abs,ababs),())) <*>
   (a,(( as,  aas),()))           = case (ab,abs) <*> (a,as) of { (b,bs) ->
                                    (b, ((bs, ababs <*> aas), ())) }
  ab <$> (a,((as,aas),()))        = case ab <$> (a,as) of { (b,bs) ->
                                    (b, ((bs, ab <$> aas), ())) }
  traverse f (a,((as,aas),()))    = (\(b,bs) bbs -> (b,((bs,bbs),())))
                                      A.<$> traverse f (a,as)
                                      A.<*> traverse f aas
  toNestedPair' (a,((as,aas),())) = case toNestedPair' (a,as) of { (ra,ras) ->
                                    (ra, pair (pair ras (toNestedPair aas))
                                              unit) }
  fromNestedPair' ra rasaasu k    = unpair (fst_ rasaasu) (\ras raas ->
                                    fromNestedPair' ra ras (\(a, as) ->
                                    fromNestedPair raas (\aas ->
                                    k (a, ((as, aas), ())))))
  toList (a,((as,aas),()))        = toList (a, as) ++ toList aas
  fromList' l0                    = case fromList' l0 of { ((a, as), l1) ->
                                    case fromList' l1 of { (aas, l) ->
                                    ((a, ((as, aas), ())), l) } }

instance (Vector a as) => Vector a ((a, as), (a, as)) where
  pure a                          = let p = pure a in (a, (p, p))
  (ab, (ababs1, ababs2)) <*>
   (a, (  aas1,   aas2))          = (ab a, (ababs1 <*> aas1, ababs2 <*> aas2))
  ab <$> (a, (aas1, aas2))        = (ab a, (ab <$> aas1, ab <$> aas2))
  traverse f (a, (aas1, aas2))    = (,) A.<$> f a
                                        A.<*> ((,) A.<$> traverse f aas1
                                                   A.<*> traverse f aas2)
  toNestedPair' (a, (aas1, aas2)) = (a, pair (toNestedPair aas1)
                                             (toNestedPair aas2))
  fromNestedPair' ra raasaas k    = unpair raasaas (\raas1 raas2 ->
                                    fromNestedPair raas1 (\aas1 ->
                                    fromNestedPair raas2 (\aas2 ->
                                    k (ra, (aas1, aas2)))))
  toList (a, (aas1, aas2))        = a : toList aas1 ++ toList aas2
  fromList' (a:l0)                = case fromList' l0 of { (aas1, l1) ->
                                    case fromList' l1 of { (aas2, l) ->
                                    ((a, (aas1, aas2)), l) } }
  fromList' []                    = error "should not happen - fromList' of empty"

sequenceA :: (A.Applicative f, Vector (f a) fas, SameLength fas a) =>
             (f a, fas) -> f (Repeat (Length (f a) fas) a)
sequenceA = traverse id

mapM :: (Vector a as, Monad m, SameLength as b) =>
        (a -> m b) -> (a, as) -> m (Repeat (Length a as) b)
mapM f = unwrapMonad . traverse (WrapMonad . f)

sequence :: (Monad m, Vector (m a) mas, SameLength mas a) =>
            (m a, mas) -> m (Repeat (Length (m a) mas) a)
sequence = mapM id

mapAccum :: (Vector x xs, SameLength xs y) =>
            (acc -> x -> (acc, y)) -> acc -> (x, xs) ->
            (acc, Repeat (Length x xs) y)
mapAccum f acc xs = exch (runState (mapM f' xs) acc)
  where exch (a,b) = (b,a)
        f' = state . curry (exch . uncurry f . exch)

iota :: (Enum y, Vector () xs, SameLength xs y) =>
        y -> Repeat (Length () xs) y
iota start = snd (mapAccum (\x () -> (succ x, x)) start (pure ()))

mapC :: (Vector a as, SameLength as b) =>
        (a -> (b -> w) -> w) -> (a, as) -> (Repeat (Length a as) b -> w) -> w
mapC f = runCont . mapM (cont . f)

{-
type Nat123 = SD (SD (D (SD (SD (SD I))))) -- toNat 123

main :: IO ()
main = do
  print (unSample (toNestedPair ((+) <$>
                                 fromList [1,2,3] <*>
                                 fromList [100,200,300])
                   :: Sample IO (Repeat (SD I) Real)))
       -- (101.0,((202.0,()),(303.0,())))
  print (unSample (fromNestedPair (pair 3 (pair (pair 5 unit) (pair 7 unit)))
                                  (\(a,((b,()),(c,()))) -> a + b + c)
                   :: Sample IO Real))
       -- 15.0
  print (iota 10 :: Repeat Nat123 Int)
  -}
