{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, ScopedTypeVariables, GADTs, TypeFamilies, InstanceSigs #-}
{-# OPTIONS -W #-}

module Language.Hakaru.Maple (Maple(..), runMaple) where

-- Maple printing interpretation

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Number(..),
    Order(..), Base(..), Integrate(..), Lambda(..), Mochastic(..))
import Data.Ratio
import Control.Monad (liftM2)
import Control.Monad.Trans.Reader (ReaderT(ReaderT), runReaderT)
import Control.Monad.Trans.Cont (Cont, cont, runCont)
-- import Data.List (intercalate)
import Language.Hakaru.Embed

-- Jacques wrote on December 16 that "the condition of a piecewise can be
-- 1. a relation (i.e. <, <=, =, ::, in)
-- 2. an explicit boolean
-- 3. a boolean combination of relations (i.e. And, Or, Not)
-- and that's it.  Anything else will throw a hard error."
-- We try to satisfy this condition in Maple Bool here---------vvvvvv
newtype Maple a = Maple { unMaple :: ReaderT Int (Cont String) String }
-- So "runMaple" should not be used on Maple Bool.

runMaple :: Maple a -> Int -> String
runMaple (Maple x) i = runCont (runReaderT x i) id

mapleFun1 :: String -> Maple a -> Maple b
mapleFun1 fn x = Maple (ReaderT $ \i -> return $
  fn ++ "(" ++ runMaple x i ++ ")")

mapleFun2 :: String -> Maple a -> Maple b -> Maple c
mapleFun2 fn x y = Maple (ReaderT $ \i -> return $
  fn ++ "(" ++ runMaple x i ++ ", " ++ runMaple y i ++ ")")

mapleOp2 :: String -> Maple a -> Maple b -> Maple c
mapleOp2 fn x y = Maple (ReaderT $ \i -> return $
  "(" ++ runMaple x i ++ fn ++ runMaple y i ++ ")")

mapleBind :: (Maple a -> Maple b) -> Int -> (String, String)
mapleBind f i = (x, runMaple (f (Maple (return x))) (i + 1))
  where x = "x" ++ show i

instance (Number a) => Order Maple a where
  less  = mapleOp2 "<"
  equal = mapleOp2 "="

instance Num (Maple a) where
  (+)           = mapleOp2 "+"
  (*)           = mapleOp2 "*"
  (-)           = mapleOp2 "-"
  negate x      = Maple (ReaderT $ \i -> return $ "(-" ++ runMaple x i ++ ")")
  abs           = mapleFun1 "abs"
  signum        = mapleFun1 "signum"
  fromInteger x = Maple (return (show x))

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
  logBase b y = Maple (ReaderT $ \i -> return $
    "log[" ++ runMaple b i ++ "](" ++ runMaple y i ++ ")")
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

instance Base Maple where
  unit = Maple (return "Unit")
  pair = mapleFun2 "Pair"
  -- unpair, uneither, and unlist duplicate their first argument.
  -- Does this duplication blow up our Maple output?
  unpair (Maple ab) k = Maple (ab >>= \ab' ->
    unMaple (k (Maple (return ("fst(" ++ ab' ++ ")"))) 
               (Maple (return ("snd(" ++ ab' ++ ")")))))
  inl (Maple a) = Maple (fmap (\a' -> "Left("  ++ a' ++ ")") a)
  inr (Maple b) = Maple (fmap (\b' -> "Right(" ++ b' ++ ")") b)
  uneither (Maple ab) ka kb
    = Maple (ab >>= \ab' ->
             ReaderT $ \i -> cont $ \c ->
             let opS :: Int -> String
                 opS n = "op(" ++ show n ++ ", " ++ ab' ++ ")"
                 arm k = runCont (runReaderT (unMaple (k (return (opS 1)))) i) c
             in "if_(" ++ opS 0 ++ " = Left, " ++ arm (ka . Maple)
                                       ++ ", " ++ arm (kb . Maple) ++ ")")
  true = Maple (return "true")
  false = Maple (return "false")
  if_ (Maple b) (Maple et) (Maple ef)
    = Maple (b >>= \b' ->
             ReaderT $ \i -> cont $ \c ->
             "if_(" ++ b' ++ ", " ++ runCont (runReaderT et i) c
                          ++ ", " ++ runCont (runReaderT ef i) c ++ ")")

  nil = Maple (return "Nil")
  cons = mapleFun2 "Cons"
  unlist (Maple as) (Maple kn) kc
    = Maple (as >>= \as' ->
             ReaderT $ \i -> cont $ \c ->
             let opS :: Int -> String
                 opS n = "op(" ++ show n ++ ", " ++ as' ++ ")"
                 car = Maple (return (opS 1))
                 cdr = Maple (return (opS 2))
                 kc' = unMaple (kc car cdr)
             in "if_(" ++ opS 0 ++ " = Nil, " ++ runCont (runReaderT kn i) c
                                      ++ ", " ++ runCont (runReaderT kc' i) c
                                      ++ ")")

  unsafeProb (Maple x) = Maple x
  fromProb   (Maple x) = Maple x
  fromInt    (Maple x) = Maple x
  infinity         = Maple (return  "infinity")
  negativeInfinity = Maple (return "-infinity")
  sqrt_     = mapleFun1 "sqrt"
  log_      = mapleFun1 "ln" -- ok since it is fed > = 0 only
  pow_      = mapleOp2 "^"
  gammaFunc = mapleFun1 "GAMMA"
  betaFunc  = mapleFun2 "Beta"
  fix       = mapleFun1 "(proc (f) local x; x := f(x) end proc)" . lam
  erf       = mapleFun1 "erf"
  erf_      = mapleFun1 "erf"

  vector    = quant "MVECTOR" 0
  empty     = Maple (return "MVECTOR(undefined,n=0..0)")
  index     = mapleFun2 "index"
  size      = mapleFun1 "size" -- should probably be "LinearAlgebra[Dimension]"
  reduce r z v = Maple (ReaderT $ \i -> return $
    "Reduce((" ++ (let x = "x" ++ show i
                       y = "x" ++ show (i+1)
                   in x ++ "->" ++ y ++ "->" ++
                      runMaple (r (Maple (return x)) (Maple (return y))) (i+2))
               ++ "), " ++ runMaple z i ++ ", " ++ runMaple v i ++ ")")

instance Integrate Maple where
  integrate = quant "Int"
  summate   = quant "sum"

-- use gensym rather than escaped locals.
-- put lo and hi in directly, instead of passing them in.
-- put the body in directly too, but still use a thunk for gensym
quant :: String -> Maple b -> Maple b ->
         (Maple a -> Maple c) -> Maple d
quant q lo hi f = 
  Maple (ReaderT $ \i -> return $ 
    let lo' = runMaple lo i in
    let hi' = runMaple hi i in
    let (x, body) = mapleBind f i in
    "(proc () local "++x++"; "++x++" := gensym(`h`);" ++
        q ++ "(" ++ body ++","++x++"=" ++ lo' ++ ".." ++ hi' ++") end proc)()")

instance Lambda Maple where
  lam f = Maple (ReaderT $ \i -> return $
    let (x, body) = mapleBind f i in "(" ++ x ++ "->" ++ body ++ ")")
  app (Maple rator) (Maple rand) =
    Maple (liftM2 (\rator' rand' -> 
        "(" ++ rator' ++ "(" ++ rand' ++ "))") rator rand)

instance Mochastic Maple where
  -- Maple doesn't currently understand this input (though one day it might).
  -- This instance is currently here because Expect produces dual output and
  -- we want "instance Mochastic (Expect Maple)".
  dirac _       = Maple (return "measure")
  bind _ _      = Maple (return "measure")
  lebesgue      = Maple (return "measure")
  counting      = Maple (return "measure")
  superpose _   = Maple (return "measure")
  categorical _ = Maple (return "measure")
{-
  dirac = mapleFun1 "Return"
  m `bind` k = Maple (ReaderT $ \i -> return $
    let (x, body) = mapleBind k i
    in "Bind(" ++ runMaple m i ++ "," ++ x ++ "," ++ body ++ ")")
  lebesgue = Maple (return "Lebesgue")
  counting = Maple (return "Counting")
  superpose pms = Maple (ReaderT $ \i -> return $
    let pms' = [ "WeightedM(" ++ runMaple p i ++ "," ++ runMaple m i ++ ")"
               | (p,m) <- pms ]
    in "Superpose(" ++ intercalate "," pms' ++ ")")
-}

op :: Int -> Maple a -> Maple b 
op n (Maple x) = Maple $ x >>= \x' -> return ("op(" ++ show n ++ ", " ++ x' ++ ")")

-- reMaple :: Maple a -> Maple b
-- reMaple (Maple a) = Maple a 

instance Embed Maple where 
  _Nil = Maple (return "Nil")
  _Cons = mapleFun2 "Cons"

  _Z = mapleFun1 "Zero"
  _S = mapleFun1 "Succ"

  voidSOP _ = Maple . return $ "HakaruError (`Datatype with no constructors`)"

  tag :: forall xss t . (Embeddable t) => Maple (SOP xss) -> Maple (Tag t xss)
  -- tag = mapleFun1 "Tag" 

  tag = mapleFun2 "Tag"
         (Maple $ return $ datatypeName $ datatypeInfo (Proxy :: Proxy t))

  caseProd x f = f (op 1 x) (op 2 x)

  caseSum (Maple ab) ka kb
    = Maple (ab >>= \ab' ->
             ReaderT $ \i -> cont $ \c ->
             let opS :: Int -> String
                 opS n = "op(" ++ show n ++ ", " ++ ab' ++ ")"
                 arm k = runCont (runReaderT (unMaple (k (return (opS 1)))) i) c
             in "if_(" ++ opS 0 ++ " = Zero, " ++ arm (ka . Maple)
                                       ++ ", " ++ arm (kb . Maple) ++ ")")

  untag = op 2 
