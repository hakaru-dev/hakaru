module Util.Finite (Finite(..), enumEverything, enumCardinality, suchThat) where

import Data.List (tails)
import Data.Maybe (fromJust)
import Data.Bits (shiftL)
import qualified Data.Set as S
import qualified Data.Map as M

class (Ord a) => Finite a where
    everything :: [a]
    cardinality :: a -> Integer

enumEverything :: (Enum a, Bounded a) => [a]
enumEverything = [minBound..maxBound]

enumCardinality :: (Enum a, Bounded a) => a -> Integer
enumCardinality dummy = succ
                      $ fromIntegral (fromEnum (maxBound `asTypeOf` dummy))
                      - fromIntegral (fromEnum (minBound `asTypeOf` dummy))

instance Finite () where
    everything = enumEverything
    cardinality = enumCardinality

instance Finite Bool where
    everything = enumEverything
    cardinality = enumCardinality

instance Finite Ordering where
    everything = enumEverything
    cardinality = enumCardinality

instance (Finite a) => Finite (Maybe a) where
    everything = Nothing : map Just everything
    cardinality = succ . cardinality . fromJust

instance (Finite a, Finite b) => Finite (Either a b) where
    everything = map Left everything ++ map Right everything
    cardinality x = cardinality l + cardinality r where
        (Left l, Right r) = (x, x)

instance (Finite a, Finite b) => Finite (a, b) where
    everything = [ (a, b) | a <- everything, b <- everything ]
    cardinality ~(a, b) = cardinality a * cardinality b

instance (Finite a, Finite b, Finite c) => Finite (a, b, c) where
    everything = [ (a, b, c) | a <- everything, b <- everything, c <- everything ]
    cardinality ~(a, b, c) = cardinality a * cardinality b * cardinality c

instance (Finite a, Finite b, Finite c, Finite d) => Finite (a, b, c, d) where
    everything = [ (a, b, c, d) | a <- everything, b <- everything, c <- everything, d <- everything ]
    cardinality ~(a, b, c, d) = cardinality a * cardinality b * cardinality c * cardinality d

instance (Finite a, Finite b, Finite c, Finite d, Finite e) => Finite (a, b, c, d, e) where
    everything = [ (a, b, c, d, e) | a <- everything, b <- everything, c <- everything, d <- everything, e <- everything ]
    cardinality ~(a, b, c, d, e) = cardinality a * cardinality b * cardinality c * cardinality d * cardinality e

instance (Finite a) => Finite (S.Set a) where
    everything = loop everything S.empty where
        loop candidates set = set
            : concat [ loop xs (S.insert x set) | x:xs <- tails candidates ]
    cardinality set = shiftL 1 (fromIntegral (cardinality (S.findMin set)))

instance (Finite a, Eq b) => Eq (a -> b) where
    f == g = all (\x -> f x == g x) everything
    f /= g = any (\x -> f x /= g x) everything

instance (Finite a, Ord b) => Ord (a -> b) where
    f `compare` g = map f everything `compare` map g everything
    f <         g = map f everything <         map g everything
    f >         g = map f everything >         map g everything
    f <=        g = map f everything <=        map g everything
    f >=        g = map f everything >=        map g everything

instance (Finite a, Finite b) => Finite (a -> b) where
    everything = [ (M.!) (M.fromDistinctAscList m)
                 | m <- loop everything ] where
        loop []     = [[]]
        loop (a:as) = [ (a,b):rest | b <- everything, rest <- loop as ]
    cardinality f = cardinality y ^ cardinality x where
        (x, y) = (x, f x)

suchThat :: (Finite a) => (a -> Bool) -> S.Set a
suchThat p = S.fromDistinctAscList (filter p everything)

