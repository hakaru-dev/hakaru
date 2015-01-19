{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, ScopedTypeVariables, TypeFamilies #-}
{-# OPTIONS -W #-}

module Language.Hakaru.Maple (Maple(..), runMaple) where

-- Maple printing interpretation

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Real, Prob, Number(..),
    Order(..), Base(..), Integrate(..), Lambda(..))
import Data.Ratio
import Control.Monad (liftM2)
import Control.Monad.Trans.Reader (ReaderT(ReaderT), runReaderT)
import Control.Monad.Trans.Cont (Cont, cont, runCont)
import Data.List (intercalate)
import Data.Function (on)
import Generics.SOP hiding (fn) 
import Language.Hakaru.Embed hiding (liftM, liftM2) 

-- Jacques wrote on December 16 that "the condition of a piecewise can be
-- 1. a relation (i.e. <, <=, =, ::, in)
-- 2. an explicit boolean
-- 3. a boolean combination of relations (i.e. And, Or, Not)
-- and that's it.  Anything else will throw a hard error."
-- We try to satisfy this condition in Maple Bool here---------vvvvvv
newtype Maple a = Maple { unMaple :: ReaderT Int (Cont String) String }
-- So "runMaple" and "resetMaple" should not be used on Maple Bool.

runMaple :: Maple a -> Int -> String
runMaple (Maple x) i = runCont (runReaderT x i) id

resetMaple :: Maple a -> Maple a
resetMaple x = Maple (ReaderT (return . runMaple x))

mapleFun1 :: String -> Maple a -> Maple b
mapleFun1 fn x =
  Maple (fmap (\y -> fn ++ "(" ++ y ++ ")") (unMaple (resetMaple x)))

mapleFun2 :: String -> Maple a -> Maple b -> Maple c
mapleFun2 fn x y =
  Maple (liftM2 (\w z -> fn ++ "(" ++ w ++ ", " ++ z ++ ")")
                (unMaple (resetMaple x))
                (unMaple (resetMaple y)))

mapleOp2 :: String -> Maple a -> Maple b -> Maple c
mapleOp2 fn x y =
  Maple (liftM2 (\w z -> "(" ++ w ++ fn ++ z ++ ")")
                (unMaple (resetMaple x))
                (unMaple (resetMaple y)))

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
  negate        = Maple . fmap (\u -> "(-" ++ u ++ ")") . unMaple . resetMaple
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
  logBase = (\b y -> Maple (liftM2 f b y)) `on` (unMaple . resetMaple)
    where f b y = "log[" ++ b ++ "]" ++ "(" ++ y ++ ")"
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
    let op :: Int -> String
        op n = "op(" ++ show n ++ ", " ++ ab' ++ ")"
    in
    unMaple (k (Maple (return (op 1))) (Maple (return (op 2)))))
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

instance Integrate Maple where
  integrate = quant "Int"
  summate   = quant "sum"

quant :: String -> Maple Real -> Maple Real ->
         (Maple a -> Maple Prob) -> Maple Prob
quant q (Maple lo) (Maple hi) f = Maple (lo >>= \lo' -> hi >>= \hi' ->
  ReaderT $ \i -> return $
  let (x, body) = mapleBind f i
  in q ++ "(" ++ body ++ "," ++ x ++ "=" ++ lo' ++ ".." ++ hi' ++ ")")

instance Lambda Maple where
  lam f = Maple (ReaderT $ \i -> return $
    let (x, body) = mapleBind f i in "(" ++ x ++ "->" ++ body ++ ")")
  app (Maple rator) (Maple rand) =
    Maple (liftM2 (\rator' rand' -> rator' ++ "(" ++ rand' ++ ")") rator rand)


constructor :: String -> [Maple a] -> Maple b
constructor fn xs = Maple $ do 
  ms <- fmap (intercalate ",") $ sequence (map (unMaple . resetMaple) xs)
  return ("`" ++ fn ++ "`(" ++ ms ++ ")")
  
prodMaple' :: forall xs a . ConstructorInfo xs -> [Maple a] -> Maple (NP Maple xs)
prodMaple' (Infix nm _ _) (x:y:_) = constructor nm [x,y] 
prodMaple' (Infix {}) _ = error "prodMaple': wrong number of values"
prodMaple' (Constructor ctr) q = constructor ctr (take (lengthSing (Proxy :: Proxy xs)) q)
prodMaple' (Record ctr _ ) q   = constructor ctr (take (lengthSing (Proxy :: Proxy xs)) q)

prodMaple :: forall xs . ConstructorInfo xs -> NP Maple xs -> Maple (NP Maple xs)
prodMaple c xs = case ciSing c of Dict -> prodMaple' c (unprod (Maple . unMaple) xs)

sopMaple :: NP ConstructorInfo xss -> NS (NP Maple) xss -> Maple (NS (NP Maple) xss)
sopMaple (ctr :* _) (Z x) = (Maple . unMaple) (prodMaple ctr x) 
sopMaple (_ :* ctrs) (S x) = (Maple . unMaple) (sopMaple ctrs x)
sopMaple Nil _ = error "sopMaple: Type error"

op' :: Int -> Maple a -> Maple b 
op' n (Maple ab) = Maple (ab >>= \ab' ->
  return $ "op(" ++ show n ++ ", " ++ ab' ++ ")")

unprodMaple :: SingI xs => NFn Maple o xs -> Maple (NP Maple xs) -> Maple o
unprodMaple b a = go sing a b 1 where 
  go :: Sing xs -> Maple (NP Maple xs) -> NFn Maple o xs -> Int -> Maple o 
  go SNil _ (NFn f) _ = f
  go s@SCons (Maple v) (NFn f) i = go (singTail s) (Maple v) (NFn (f (op' i (Maple v)))) (i+1) 

unConstructor ctr (Maple ab) ka kb
    = Maple (ab >>= \ab' ->
             ReaderT $ \i -> cont $ \c ->
             let op :: Int -> String
                 op n = "op(" ++ show n ++ ", " ++ ab' ++ ")"
                 arm k = runCont (runReaderT (unMaple (k (return (op 1)))) i) c
             in "if_(" ++ op 0 ++ " = `" ++ ctr ++ "`, " ++ arm (ka . Maple)
                                        ++ ", " ++ arm (kb . Maple) ++ ")")

caseMaple :: Int -> NP ConstructorInfo xss -> NP (NFn Maple o) xss -> Maple (NS (NP Maple) xss) -> Maple o 
caseMaple _ Nil Nil _ = Maple $ return "error \"Datatypes with no constructors or type error\""
caseMaple i (ctr :* ctrs) (f :* fs) m = 
  case ciSing ctr of 
    Dict -> unConstructor (ctrName ctr) m (unprodMaple f) (caseMaple (i+1) ctrs fs)
caseMaple _ _ _ _ = error "caseMaple: type error"

instance Embed Maple where 
  type Ctx Maple t = ()
  
  hRep (Maple x) = Maple x
  unHRep (Maple x) = Maple x
                   
  sop' p xs = sopMaple (ctrInfo (datatypeInfo p)) xs 
  case' p r f = 
    let di = datatypeInfo p in 
    case diSing di of 
      Dict -> caseMaple 1 (ctrInfo di) f r 

