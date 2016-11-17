{-# LANGUAGE CPP
           , GADTs
           , DataKinds
           , TypeFamilies
           , FlexibleContexts
           , UndecidableInstances
           , LambdaCase
           , OverloadedStrings
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs -fsimpl-tick-factor=1000 #-}
module Language.Hakaru.Runtime.Prelude where

#if __GLASGOW_HASKELL__ < 710
import           Data.Functor                    ((<$>))
import           Control.Applicative             (Applicative(..))
#endif
import           Data.Foldable                   as F
import qualified System.Random.MWC               as MWC
import qualified System.Random.MWC.Distributions as MWCD
import           Data.Number.Natural
import qualified Data.Vector                     as V
import qualified Data.Vector.Unboxed             as U
import qualified Data.Vector.Generic             as G
import           Control.Monad
import           Prelude                         hiding (product)

type family MinBoxVec (v1 :: * -> *) (v2 :: * -> *) :: * -> *
type instance MinBoxVec V.Vector v        = V.Vector
type instance MinBoxVec v        V.Vector = V.Vector
type instance MinBoxVec U.Vector U.Vector = U.Vector

type family MayBoxVec a :: * -> *
type instance MayBoxVec Int          = U.Vector
type instance MayBoxVec Double       = U.Vector
type instance MayBoxVec (U.Vector a) = V.Vector
type instance MayBoxVec (V.Vector a) = V.Vector
type instance MayBoxVec (a,b)        = MinBoxVec (MayBoxVec a) (MayBoxVec b)

lam :: (a -> b) -> a -> b
lam = id

app :: (a -> b) -> a -> b
app f x = f x

let_ :: a -> (a -> b) -> b
let_ x f = let x1 = x in f x1

ann_ :: a -> b -> b
ann_ _ a = a

newtype Measure a = Measure { unMeasure :: MWC.GenIO -> IO (Maybe a) }

instance Functor Measure where
    fmap  = liftM

instance Applicative Measure where
    pure x = Measure $ \_ -> return (Just x)
    (<*>)  = ap

instance Monad Measure where
    return  = pure
    m >>= f = Measure $ \g -> do
                          Just x <- unMeasure m g
                          unMeasure (f x) g

makeMeasure :: (MWC.GenIO -> IO a) -> Measure a
makeMeasure f = Measure $ \g -> Just <$> f g

uniform :: Double -> Double -> Measure Double
uniform lo hi = makeMeasure $ MWC.uniformR (lo, hi)

normal :: Double -> Double -> Measure Double
normal mu sd = makeMeasure $ MWCD.normal mu sd

beta :: Double -> Double -> Measure Double
beta a b = makeMeasure $ MWCD.beta a b

gamma :: Double -> Double -> Measure Double
gamma a b = makeMeasure $ MWCD.gamma a b

categorical :: MayBoxVec Double Double -> Measure Int
categorical a = makeMeasure (\g -> fromIntegral <$> MWCD.categorical a g)

plate :: (G.Vector (MayBoxVec a) a) =>
         Int -> (Int -> Measure a) -> Measure (MayBoxVec a a)
plate n f = G.generateM (fromIntegral n) $ \x ->
             f (fromIntegral x)

pair :: a -> b -> (a, b)
pair = (,)

true, false :: Bool
true  = True
false = False

unit :: ()
unit = ()

data Pattern = PVar | PWild
newtype Branch a b =
    Branch { extract :: a -> Maybe b }

ptrue, pfalse :: a -> Branch Bool a
ptrue  b = Branch { extract = extractBool True  b }
pfalse b = Branch { extract = extractBool False b }

extractBool :: Bool -> a -> Bool -> Maybe a
extractBool b a p | p == b     = Just a  
                  | otherwise  = Nothing

ppair :: Pattern -> Pattern -> (x -> y -> b) -> Branch (x,y) b
ppair PVar  PVar c = Branch { extract = (\(x,y) -> Just (c x y)) }
ppair _     _    _ = error "ppair: TODO"

case_ :: a -> [Branch a b] -> b
case_ e_ bs_ = go e_ bs_
  where go _ []     = error "case_: unable to match any branches"
        go e (b:bs) = case extract b e of
                        Just b' -> b'
                        Nothing -> go e bs

branch :: (c -> Branch a b) -> c -> Branch a b
branch pat body = pat body

dirac :: a -> Measure a
dirac = return

pose :: Double -> Measure a -> Measure a
pose _ a = a

superpose :: [(Double, Measure a)]
          -> Measure a
superpose pms = do
  i <- makeMeasure $ MWCD.categorical (U.fromList $ map fst pms)
  snd (pms !! i)

reject :: Measure a
reject = Measure $ \_ -> return Nothing

nat_ :: Int -> Int
nat_ = id

int_ :: Int -> Int
int_ = id

unsafeNat :: Int -> Int
unsafeNat = id

nat2prob :: Int -> Double
nat2prob = fromIntegral

fromInt  :: Int -> Double
fromInt  = fromIntegral

nat2int  :: Int -> Int
nat2int  = id

nat2real :: Int -> Double
nat2real = fromIntegral

fromProb :: Double -> Double
fromProb = id

unsafeProb :: Double -> Double
unsafeProb = id

real_ :: Rational -> Double
real_ = fromRational

prob_ :: NonNegativeRational -> Double
prob_ = fromRational . fromNonNegativeRational

infinity :: Double
infinity = 1/0

abs_ :: Num a => a -> a
abs_ = abs

thRootOf :: Int -> Double -> Double
thRootOf a b = b ** (recip $ fromIntegral a)

array
    :: (G.Vector (MayBoxVec a) a)
    => Int
    -> (Int -> a)
    -> MayBoxVec a a
array n f = G.generate (fromIntegral n) (f . fromIntegral)

(!) :: (G.Vector (MayBoxVec a) a) => MayBoxVec a a -> Int -> a
a ! b = a G.! (fromIntegral b)

size :: (G.Vector (MayBoxVec a) a) => MayBoxVec a a -> Int
size v = fromIntegral (G.length v)

product
    :: Num a
    => Int
    -> Int
    -> (Int -> a)
    -> a
product a b f = F.foldl' (\x y -> x * f y) 1 [a .. b-1]

summate
    :: Num a
    => Int
    -> Int
    -> (Int -> a)
    -> a
summate a b f = F.foldl' (\x y -> x + f y) 0 [a .. b-1]

run :: Show a
    => MWC.GenIO
    -> Measure a
    -> IO ()
run g k = unMeasure k g >>= \case
           Just a  -> print a
           Nothing -> return ()

iterateM_
    :: Monad m
    => (a -> m a)
    -> a
    -> m b
iterateM_ f = g
    where g x = f x >>= g

withPrint :: Show a => (a -> IO b) -> a -> IO b
withPrint f x = print x >> f x
