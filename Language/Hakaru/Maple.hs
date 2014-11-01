{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, ScopedTypeVariables #-}
{-# OPTIONS -W #-}

module Language.Hakaru.Maple (Maple(..), runMaple, closeLoop) where

-- Maple printing interpretation

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Order(..), Base(..), Integrate(..), Lambda(..),
    Mochastic(..), Prob)
import Data.Ratio
import Data.Dynamic (Typeable)
import Control.Monad (liftM2)
import Control.Monad.Trans.Reader (ReaderT(ReaderT), runReaderT)
import Control.Monad.Trans.Cont (Cont, cont, runCont)

import Language.Haskell.Interpreter

newtype Maple a = Maple { unMaple :: ReaderT Int (Cont String) String }

-- "piecewise" in Maple only works when the expression has numeric type.
-- So "runMaple" should only be used when the expression has numeric type.
runMaple :: Maple a -> Int -> String
runMaple (Maple x) i = runCont (runReaderT x i) id

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

instance Order Maple a where
  less = mapleOp2 "<"

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
  sqrt  = mapleFun1 "sqrt"
  log   = mapleFun1 "log"
  (**)  = mapleOp2 "^"
  logBase (Maple b) (Maple y) =
    Maple (liftM2 (\b' y' -> "log[" ++ b' ++ "]" ++ "(" ++ y' ++ ")") b y)
  sin   = mapleFun1 "sin"
  tan   = mapleFun1 "tan"
  cos   = mapleFun1 "cos"
  asin  = mapleFun1 "asin"
  atan  = mapleFun1 "atan"
  acos  = mapleFun1 "acos"
  sinh  = mapleFun1 "sinh"
  tanh  = mapleFun1 "tanh"
  cosh  = mapleFun1 "cosh"
  asinh = mapleFun1 "asinh"
  atanh = mapleFun1 "atanh"
  acosh = mapleFun1 "acosh"

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
  uneither (Maple ab) ka kb = Maple (ab >>= \ab' ->
    ReaderT $ \i -> cont $ \c ->
    let opab :: Int -> String
        opab n = "op(" ++ show n ++ ", " ++ ab' ++ ")" in
    let arm tag k = opab 0 ++ " = " ++ tag ++ ", " ++
                    runCont (runReaderT (k (return (opab 1))) i) c in
    "piecewise(" ++ arm "Left"  (unMaple . ka . Maple)
         ++ ", " ++ arm "Right" (unMaple . kb . Maple) ++ ")")
  unsafeProb (Maple x) = Maple x
  fromProb   (Maple x) = Maple x
  true  = Maple (return "true" )
  false = Maple (return "false")
  if_ (Maple cond) (Maple a) (Maple b) = Maple (cond >>= \cond' ->
    ReaderT $ \i -> cont $ \c ->
    "piecewise(" ++ cond' ++ ", " ++ runCont (runReaderT a i) c
                          ++ ", " ++ runCont (runReaderT b i) c ++ ")")
  sqrt_ = mapleFun1 "sqrt"
  pow_ = mapleOp2 "^"
  betaFunc = mapleFun2 "Beta"
  fix = mapleFun1 "(proc (f) local x; x := f(x) end proc)" . lam

instance Integrate Maple where
  integrate (Maple lo) (Maple hi) f = Maple (lo >>= \lo' -> hi >>= \hi' ->
    ReaderT $ \i -> return $
    let (x, body) = mapleBind f i
    in "int(" ++ body ++ "," ++ x ++ "=" ++ lo' ++ ".." ++ hi' ++ ")")
  infinity         = Maple (return  "infinity")
  negativeInfinity = Maple (return "-infinity")

instance Lambda Maple where
  lam f = Maple (ReaderT $ \i -> return $
    let (x, body) = mapleBind f i in "(" ++ x ++ "->" ++ body ++ ")")
  app (Maple rator) (Maple rand) =
    Maple (liftM2 (\rator' rand' -> rator' ++ "(" ++ rand' ++ ")") rator rand)

-- and now for the other way around: take things that came from Maple
-- (as strings), and interpret in Haskell.  This is probably not the best
-- place for this code, since Maple is supposed to produce proper Haskell,
-- but this is a start.
ourContext :: MonadInterpreter m => m ()
ourContext = setImports ["Prelude", "Data.Ratio"]

-- Typeable repr is very scary!?
closeLoop :: forall m repr.(Functor m, MonadInterpreter m, Mochastic repr,
  Typeable repr) => 
    String -> m (Either InterpreterError (repr Prob))
closeLoop s = runInterpreter (ourContext >> interpret s (as :: repr Prob))
