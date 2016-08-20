{-# LANGUAGE GADTs
           , DataKinds
           , OverloadedStrings
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs -fsimpl-tick-factor=1000 #-}
module Language.Hakaru.Runtime.Prelude where

import qualified System.Random.MWC               as MWC
import qualified System.Random.MWC.Distributions as MWCD
import           Data.Number.Natural
import qualified Data.Vector                     as V
import qualified Control.Monad                   as M
import           Prelude                         hiding (product, (>>=))
import qualified Prelude                         as P

lam :: (a -> b) -> a -> b
lam = id

let_ :: a -> (a -> b) -> b
let_ x f = let x1 = x in f x1

ann_ :: a -> b -> b
ann_ _ a = a

type Measure a = MWC.GenIO -> IO a

uniform :: Double -> Double -> Measure Double
uniform lo hi g = MWC.uniformR (lo, hi) g

normal :: Double -> Double -> Measure Double
normal mu sd g = MWCD.normal mu sd g

pair :: a -> b -> (a, b)
pair = (,)

true, false :: Bool
true  = True
false = False

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

(>>=) :: Measure a
      -> (a -> Measure b)
      -> Measure b
m >>= f = \g -> m g M.>>= flip f g

dirac :: a -> Measure a
dirac x _ = return x

pose :: Double -> Measure a -> Measure a
pose _ a = a

superpose :: [(Double, Measure a)]
          -> Measure a
superpose pms g = do
  i <- MWCD.categorical (V.fromList $ map fst pms) g
  let m = snd (pms !! i)
  m g

nat_ :: Integer -> Integer
nat_ = id

int_ :: Integer -> Integer
int_ = id

nat2prob :: Integer -> Double
nat2prob = fromIntegral

fromInt  :: Integer -> Double
fromInt  = fromIntegral

nat2int  :: Integer -> Integer
nat2int  = id

nat2real :: Integer -> Double
nat2real = fromIntegral

fromProb :: Double -> Double
fromProb = id

unsafeProb :: Double -> Double
unsafeProb = id

real_ :: Rational -> Double
real_ = fromRational

prob_ :: NonNegativeRational -> Double
prob_ = fromRational . fromNonNegativeRational

thRootOf :: Integer -> Double -> Double
thRootOf a b = b ** (recip $ fromIntegral a)

product
    :: Num a
    => Integer
    -> Integer
    -> (Integer -> a)
    -> a
product a b f = P.product $ map f [a .. b-1]

summate
    :: Num a
    => Integer
    -> Integer
    -> (Integer -> a)
    -> a
summate a b f = sum $ map f [a .. b-1]

run :: Show a
    => MWC.GenIO
    -> Measure a
    -> IO ()
run g k = k g M.>>= print

iterateM_
    :: Monad m
    => (a -> m a)
    -> a
    -> m b
iterateM_ f = g
    where g x = f x M.>>= g

withPrint :: Show a => (a -> IO b) -> a -> IO b
withPrint f x = print x >> f x
