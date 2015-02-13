{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, ScopedTypeVariables, GADTs, TypeFamilies #-}
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
-- import Language.Hakaru.Embed

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
             let op :: Int -> String
                 op n = "op(" ++ show n ++ ", " ++ ab' ++ ")"
                 arm k = runCont (runReaderT (unMaple (k (return (op 1)))) i) c
             in "if_(" ++ op 0 ++ " = Left, " ++ arm (ka . Maple)
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
             let op :: Int -> String
                 op n = "op(" ++ show n ++ ", " ++ as' ++ ")"
                 car = Maple (return (op 1))
                 cdr = Maple (return (op 2))
                 kc' = unMaple (kc car cdr)
             in "if_(" ++ op 0 ++ " = Nil, " ++ runCont (runReaderT kn i) c
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

  vector    = quant "VECTOR"
  empty     = Maple (return "VECTOR(undefined,n=0..-1)")
  index     = mapleFun2 "index"
  loBound   = mapleFun1 "loBound"
  hiBound   = mapleFun1 "hiBound"
  reduce r z v = Maple (ReaderT $ \i -> return $
    "Reduce((" ++ (let x = "x" ++ show i
                       y = "x" ++ show (i+1)
                   in x ++ "->" ++ y ++ "->" ++
                      runMaple (r (Maple (return x)) (Maple (return y))) (i+2))
               ++ "), " ++ runMaple z i ++ ", " ++ runMaple v i ++ ")")

instance Integrate Maple where
  integrate = quant "Int"
  summate   = quant "sum"

quant :: String -> Maple b -> Maple b ->
         (Maple a -> Maple c) -> Maple d
quant q lo hi f = mapleFun2 ("(proc (r,c) local x; "++q++"(c(x),x=r) end proc)")
                            (mapleOp2 ".." lo hi)
			    (lam f)

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

{-
constructor :: String -> [Maple a] -> Maple b
constructor fn xs = Maple $ ReaderT $ \i -> return $ 
  let ms = intercalate "," (map (flip runMaple i) xs) in 
   ("`" ++ fn ++ "`(" ++ ms ++ ")")
  
prodMaple' :: forall xs a . SingI xs => ConstructorInfo (Shape xs) -> [Maple a] -> Maple (NP Maple xs) 
prodMaple' (Infix nm _ _) (x:y:_) = constructor nm [x,y] 
prodMaple' (Infix {}) _ = error "prodMaple': wrong number of values"
prodMaple' (Constructor ctr) q = constructor ctr (take (lengthSing (Proxy :: Proxy xs)) q)
prodMaple' (Record ctr _ ) q   = constructor ctr (take (lengthSing (Proxy :: Proxy xs)) q)

prodMaple :: SingI xs => ConstructorInfo (Shape xs) -> NP Maple xs -> Maple (NP Maple xs)
prodMaple c xs = prodMaple' c (unprod (Maple . unMaple) xs)

sopMaple :: forall xss . Sing xss -> NP ConstructorInfo (Shape xss) -> NS (NP Maple) xss -> Maple ()
sopMaple SCons (ctr :* _) (Z x) = (Maple . unMaple) (prodMaple ctr x) 
sopMaple s@SCons (_ :* ctrs) (S x) = (Maple . unMaple) (sopMaple (singTail s) ctrs x)
sopMaple _ _ _ = error "sopMaple: Type error"

op' :: Int -> Maple a -> Maple b 
op' n (Maple ab) = Maple (ab >>= \ab' ->
  return $ "op(" ++ show n ++ ", " ++ ab' ++ ")")

unprodMaple :: SingI xs => NFn Maple o xs -> Maple (NP Maple xs) -> Maple o
unprodMaple b a = go sing a b 1 where 
  go :: Sing xs -> Maple (NP Maple xs) -> NFn Maple o xs -> Int -> Maple o 
  go SNil _ (NFn f) _ = f
  go s@SCons (Maple v) (NFn f) i = go (singTail s) (Maple v) (NFn (f (op' i (Maple v)))) (i+1) 

unConstructor :: String
              -> Maple t
              -> (Maple a2 -> Maple a1)
              -> (Maple a3 -> Maple a1)
              -> Maple a

unConstructor ctr (Maple ab) ka kb
    = Maple (ab >>= \ab' ->
             ReaderT $ \i -> cont $ \c ->
             let op :: Int -> String
                 op n = "op(" ++ show n ++ ", " ++ ab' ++ ")"

                 arm :: (Maple a -> Maple b) -> String 
                 arm k = runCont (runReaderT (unMaple $ k (Maple ab)) i) c 

             in "if_(" ++ op 0 ++ " = `" ++ ctr ++ "`, " ++ arm ka 
                                        ++ ", " ++ arm kb ++ ")")

caseMaple :: forall xss o . SingI xss 
          => Int -> NP ConstructorInfo (Shape xss) -> NP (NFn Maple o) xss -> Maple (NS (NP Maple) xss) -> Maple o 
caseMaple _ Nil Nil _ = Maple $ return "Error(\"Datatypes with no constructors or type error\")"
caseMaple i (ctr :* ctrs) (f :* fs) m = 
  case sing :: Sing xss of 
    SCons -> unConstructor (ctrName ctr) m (unprodMaple f) (caseMaple (i+1) ctrs fs)
    _     -> error "caseMaple: type error"
caseMaple _ _ _ _ = error "caseMaple: type error"

instance Embed Maple where 
  sop' p xs = (\(Maple x) -> Maple x) (sopMaple sing (ctrInfo (datatypeInfo p)) xs)
  case' p (Maple x) f = caseMaple 1 (ctrInfo (datatypeInfo p)) f (Maple x) 
-}
