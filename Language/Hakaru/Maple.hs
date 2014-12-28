{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# OPTIONS -W #-}

module Language.Hakaru.Maple (Maple(..), runMaple) where

-- Maple printing interpretation

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Real, Prob, Number(..),
    Order(..), Base(..), Integrate(..), Lambda(..))
import Data.Ratio
import Control.Monad (liftM2)
import Control.Monad.Trans.Reader (Reader, reader, runReader)
import Data.Number.Erf

newtype Maple a = Maple { unMaple :: Reader Int String }

-- "piecewise" in Maple only works when the expression has numeric type.
-- So "runMaple" should only be used when the expression has numeric type.
runMaple :: Maple a -> Int -> String
runMaple (Maple x) = runReader x

mapleFun1 :: String -> Maple a -> Maple b
mapleFun1 fn (Maple x) =
  Maple (fmap (\y -> fn ++ "(" ++ y ++ ")") x)

mapleFun2 :: String -> Maple a -> Maple b -> Maple c
mapleFun2 fn (Maple x) (Maple y) =
  Maple (liftM2 (\w z -> fn ++ "(" ++ w ++ ", " ++ z ++ ")") x y)

mapleOp2 :: String -> Maple a -> Maple b -> Maple c
mapleOp2 fn (Maple x) (Maple y) =
  Maple (liftM2 (\w z -> "(" ++ w ++ fn ++ z ++ ")") x y)

mapleBind :: (Maple a -> Maple b) -> Int -> (String, String)
mapleBind f i = (x, runMaple (f (Maple (return x))) (i + 1))
  where x = "x" ++ show i

instance (Number a) => Order Maple a where
  less  = mapleOp2 "<"
  equal = mapleOp2 "="

instance Num (Maple a) where
  (+)              = mapleOp2 "+"
  (*)              = mapleOp2 "*"
  (-)              = mapleOp2 "-"
  negate (Maple x) = Maple (fmap (\u -> "(-" ++ u ++ ")") x)
  abs              = mapleFun1 "abs"
  signum           = mapleFun1 "signum"
  fromInteger x    = Maple (return (show x))

instance Fractional (Maple a) where
  (/)            = mapleOp2 "/"
  fromRational x = Maple (return ("(" ++ show (numerator   x) ++
                                  "/" ++ show (denominator x) ++ ")"))

instance Floating (Maple a) where
  pi    = Maple (return "Pi")
  exp   = mapleFun1 "exp"
  sqrt  = mapleFun1 "(x -> piecewise(x<0, undefined, sqrt(x)))"
  log   = mapleFun1 "(x -> piecewise(x<0, undefined, ln(x)))"
  (**)  = mapleOp2 "^"
  logBase (Maple b) (Maple y) =
    Maple (liftM2 (\b' y' -> "log[" ++ b' ++ "]" ++ "(" ++ y' ++ ")") b y)
  sin   = mapleFun1 "sin"
  tan   = mapleFun1 "tan"
  cos   = mapleFun1 "cos"
  asin  = mapleFun1 "arcsin"
  atan  = mapleFun1 "arctan"
  acos  = mapleFun1 "arccos"
  sinh  = mapleFun1 "sinh"
  tanh  = mapleFun1 "tanh"
  cosh  = mapleFun1 "cosh"
  asinh = mapleFun1 "arcsinh"
  atanh = mapleFun1 "arctanh"
  acosh = mapleFun1 "arccosh"

instance Erf (Maple a) where
  erf = mapleFun1 "erf"

instance Base Maple where
  unit = Maple (return "Unit")
  pair = mapleFun2 "Pair"
  unpair (Maple ab) k = Maple (ab >>= \ab' ->
    let opab :: Int -> String
        opab n = "op(" ++ show n ++ ", " ++ ab' ++ ")"
    in
    unMaple (k (Maple (return (opab 1))) (Maple (return (opab 2)))))
  inl (Maple a) = Maple (fmap (\a' -> "Left("  ++ a' ++ ")") a)
  inr (Maple b) = Maple (fmap (\b' -> "Right(" ++ b' ++ ")") b)
  uneither (Maple ab) ka kb
    = Maple (ab >>= \ab' ->
             reader $ \i ->
             let opab :: Int -> String
                 opab n = "op(" ++ show n ++ ", " ++ ab' ++ ")"
                 arm k = runReader (unMaple (k (return (opab 1)))) i
             in "if_(" ++ opab 0 ++ " = Left, " ++ arm (ka . Maple)
                                        ++ ", " ++ arm (kb . Maple) ++ ")")
  true = Maple (return "true")
  false = Maple (return "false")
  if_ (Maple b) (Maple et) (Maple ef)
    = Maple (b >>= \b' ->
             reader $ \i ->
             "if_(" ++ b' ++ ", " ++ runReader et i
                          ++ ", " ++ runReader ef i ++ ")")

  nil = Maple (return "Nil")
  cons = mapleFun2 "Cons"
  unlist (Maple as) (Maple kn) kc
    = Maple (as >>= \as' ->
             reader $ \i ->
             let opas :: Int -> String
                 opas n = "op(" ++ show n ++ ", " ++ as' ++ ")"
                 car = Maple (return (opas 1))
                 cdr = Maple (return (opas 2))
                 kc' = unMaple (kc car cdr)
             in "if_(" ++ opas 0 ++ " = Nil, " ++ runReader kn i
                                       ++ ", " ++ runReader kc' i
                                       ++ ")")

  unsafeProb (Maple x) = Maple x
  fromProb   (Maple x) = Maple x
  fromInt    (Maple x) = Maple x
  sqrt_ = mapleFun1 "sqrt"
  log_ = mapleFun1 "ln" -- ok since it is fed >= 0 only
  pow_ = mapleOp2 "^"
  infinity         = Maple (return  "infinity")
  negativeInfinity = Maple (return "-infinity")
  gammaFunc = mapleFun1 "GAMMA"
  betaFunc = mapleFun2 "Beta"
  erfFunc = mapleFun1 "erf"
  erfFunc_ = mapleFun1 "erf"
  fix = mapleFun1 "(proc (f) local x; x := f(x) end proc)" . lam

instance Integrate Maple where
  integrate = quant "Int"
  summate   = quant "sum"

quant :: String -> Maple Real -> Maple Real ->
         (Maple a -> Maple Prob) -> Maple Prob
quant q (Maple lo) (Maple hi) f = Maple (lo >>= \lo' -> hi >>= \hi' ->
  reader $ \i ->
  let (x, body) = mapleBind f i
  in q ++ "(" ++ body ++ "," ++ x ++ "=" ++ lo' ++ ".." ++ hi' ++ ")")

instance Lambda Maple where
  lam f = Maple (reader $ \i ->
    let (x, body) = mapleBind f i in "(" ++ x ++ "->" ++ body ++ ")")
  app (Maple rator) (Maple rand) =
    Maple (liftM2 (\rator' rand' -> rator' ++ "(" ++ rand' ++ ")") rator rand)
