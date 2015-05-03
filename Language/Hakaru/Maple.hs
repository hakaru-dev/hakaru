{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, ScopedTypeVariables, GADTs, TypeFamilies, InstanceSigs #-}
{-# OPTIONS -W #-}

module Language.Hakaru.Maple (Maple(..), runMaple) where

-- Expect-Maple printing interpretation
-- This fuses two operations:
-- 1. the Expect program transformation
-- 2. the "Expect repr" instantiation at repr = Maple
-- where Maple is a "printing in Maple syntax" interpretation

-- We won't need fancy type gymnastics (which Expect requires) because
-- we're squishing everything into String.

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Number(..),
    Order(..), Base(..), Integrate(..), Lambda(..), Mochastic(..), Prob, Measure)
import Data.Ratio
import Control.Monad (liftM, liftM2)
import Control.Monad.Trans.State.Strict (State, evalState, state)
import Language.Hakaru.Embed
import Data.List (intersperse)

newtype Maple a = Maple {unMaple :: State Int String}

runMaple :: Maple a -> Int -> String
runMaple (Maple a) = evalState a

constant :: String -> Maple a
constant = Maple . return

app1 :: String -> Maple a -> Maple b
app1 fn = Maple . liftM (\z -> fn ++ "(" ++ z ++ ")") . unMaple

app2 :: String -> Maple a -> Maple b -> Maple c
app2 fn (Maple x) (Maple y) = 
  Maple $ liftM2 (\a b -> fn ++ "(" ++ a ++ ", " ++ b ++ ")") x y

lam1 :: String -> (Maple a  -> Maple b) -> Maple (a -> b)
lam1 s k = Maple $ do
    x <- gensym s
    cont <- unMaple (k (constant x))
    return ("(" ++ x ++ " -> " ++ cont ++ ")")

lam2 :: String -> (Maple a  -> Maple b -> Maple c) -> Maple (a -> b -> c)
lam2 s k = Maple $ do
    x <- gensym s
    y <- gensym s
    cont <- unMaple (k (constant x) (constant y))
    return ("( (" ++ x ++ " , " ++ y ++ ") -> " ++ cont ++ ")")

mapleOp2 :: String -> Maple a -> Maple b -> Maple c
mapleOp2 fn (Maple x) (Maple y) = 
  Maple $ liftM2 (\a b -> "(" ++ a ++ fn ++ b ++ ")") x y

maplePre1 :: String -> Maple a -> Maple b
maplePre1 fn (Maple x) = Maple $ liftM (\z -> "("++ fn ++ z ++ ")") x

gensym :: String -> State Int String
gensym s = state $ \i -> (s ++ show i, i + 1)

mapleCut1 :: String -> Maple a -> Maple b
mapleCut1 fn (Maple x) = Maple $
{-
  do undef <- gensym "Undef"
     liftM (\a -> "(x -> piecewise(x<0, " ++ undef ++ ", " ++ fn ++ "(x)))(" ++ a ++ ")") x
-}
  -- rather than a new Undef symbol, or undefined, pick an absurd value
  -- which has a decent chance of being easy to spot.
  do liftM (\a -> "(x -> piecewise(x<0, -337, " ++ fn ++ "(x)))(" ++ a ++ ")") x

instance (Number a) => Order Maple a where
  less  = mapleOp2 "<"
  equal = mapleOp2 "="

instance Num (Maple a) where
  (+)           = mapleOp2 "+"
  (*)           = mapleOp2 "*"
  (-)           = mapleOp2 "-"
  negate        = maplePre1 "-"
  abs           = app1 "abs"
  signum        = app1 "signum"
  fromInteger   = constant . show

instance Fractional (Maple a) where
  (/)            = mapleOp2 "/"
  fromRational x = constant ("(" ++ show (numerator   x) ++
                         "/" ++ show (denominator x) ++ ")")

-- below we don't use Maple's undefined as that leads to more problems
-- than it is worth.  Use a separate symbol instead.
instance Floating (Maple a) where
  pi    = constant "Pi"
  exp   = app1 "exp"
  sqrt  = mapleCut1 "sqrt"
  log   = mapleCut1 "ln"
  (**)  = mapleOp2 "^"
  logBase b y = Maple $ liftM2 (\bb yy -> 
    "log[" ++ bb ++ "](" ++ yy ++ ")") (unMaple b) (unMaple y)
  sin   = app1 "sin"
  tan   = app1 "tan"
  cos   = app1 "cos"
  asin  = app1 "arcsin"
  atan  = app1 "arctan"
  acos  = app1 "arccos"
  sinh  = app1 "sinh"
  tanh  = app1 "tanh"
  cosh  = app1 "cosh"
  asinh = app1 "arcsinh"
  atanh = app1 "arctanh"
  acosh = app1 "arccosh"

instance Base Maple where
  unit = constant "Unit"
  pair = app2 "Pair"
  inl (Maple a) = Maple (fmap (\a' -> "Left("  ++ a' ++ ")") a)
  inr (Maple b) = Maple (fmap (\b' -> "Right(" ++ b' ++ ")") b)
  true = constant "true"
  false = constant "false"
  unsafeProb (Maple x) = (Maple x) -- because the phantom types shift
  fromProb   (Maple x) = (Maple x) -- because the phantom types shift
  fromInt    (Maple x) = (Maple x) -- because the phantom types shift
  infinity   = constant "infinity"
  negativeInfinity = constant "-infinity"
  sqrt_     = app1 "sqrt"
  log_      = app1 "ln" -- ok since it is fed > = 0 only
  pow_      = mapleOp2 "^"
  gammaFunc = app1 "GAMMA"
  betaFunc  = app2 "Beta"
  erf       = app1 "erf"
  erf_      = app1 "erf"

  vector    = quant "MVECTOR" 0
  empty     = constant "MVECTOR(undefined,n=0..0)" -- feels like a hack
  index     = app2 "vindex"
  size      = app1 "vsize"
  unpair (Maple ab) k = Maple $ do
    pr <- ab
    f <- unMaple $ lam2 "p" k
    return ("unpair(" ++ f ++ ", "++pr++")")
  uneither (Maple ab) ka kb = Maple $ do
    e <- ab
    f <- unMaple $ lam1 "left" ka
    g <- unMaple $ lam1 "right" kb
    return ("uneither (" ++ f ++ ", " ++ g ++ ", "++e++")")
  if_ (Maple b) (Maple et) (Maple ef) = Maple $ do
    b' <- b
    et' <- et
    ef' <- ef
    return $ "if_(" ++ b' ++ ", " ++ et'
                          ++ ", " ++ ef' ++ ")"
  -- fix       = app1 "(proc (f) local x; x := f(x) end proc)" . lam
{-
  reduce r z v = Maple (ReaderT $ \i -> return $
    "Reduce((" ++ (let x = "x" ++ show i
                       y = "x" ++ show (i+1)
                   in x ++ "->" ++ y ++ "->" ++
                      runMaple (r (Maple (return x)) (Maple (return y))) (i+2))
               ++ "), " ++ runMaple z i ++ ", " ++ runMaple v i ++ ")")
-}
-- use gensym rather than escaped locals.
-- put lo and hi in directly, instead of passing them in.
-- put the body in directly too, but still use a thunk for gensym
quant :: String -> Maple b -> Maple b ->
         (Maple a -> Maple c) -> Maple d
quant q (Maple lo) (Maple hi) f = Maple $ do
  lo' <- lo
  hi' <- hi
  x <- gensym "x"
  body <- unMaple $ f $ constant x
  return $ "(proc () local "++x++"; "++x++" := gensym(`h`);" ++
           q ++ "(" ++ body ++","++x++"=" ++ lo' ++ ".." ++ hi' ++") end proc)()"

-- variant, which (in Maple) takes a function to apply
fquant :: String -> Maple b -> Maple b -> Maple d
fquant q (Maple lo) (Maple hi) = Maple $ do
  lo' <- lo
  hi' <- hi
  x <- gensym "x"
  f <- gensym "f"
  return $ "(proc ("++f++") local "++x++"; "++x++" := gensym(`h`);" ++
           q ++ "(" ++ f++"("++x++")"++
               ","++x++"=" ++ lo' ++ ".." ++ hi' ++") end proc)"

instance Integrate Maple where
  integrate = quant "Int"
  summate   = quant "Sum"

instance Lambda Maple where
  lam f = lam1 "x" f
  app (Maple rator) (Maple rand) =
    Maple (liftM2 (\rator' rand' -> 
        "(" ++ rator' ++ "(" ++ rand' ++ "))") rator rand)

-- this does not return a Measure b, but rather the body of a measure
wmtom :: String -> (Maple Prob, Maple (Measure b)) -> Maple b
wmtom c (Maple w, Maple m) = Maple $ do
  w' <- w
  m' <- m
  return $ "(" ++ w' ++ " * " ++ m' ++ "(" ++ c ++ "))"

instance Mochastic Maple where
  dirac (Maple a) = Maple $ do
    a' <- a
    c <- gensym "c"
    return ("(" ++ c ++ " -> " ++ c ++ "(" ++ a' ++ "))")
  bind (Maple m) k = Maple $ do
    m2 <- m
    c <- gensym "c"
    a <- gensym "a"
    body <- unMaple $ app1 m2 (lam1 a (\b -> Maple $ do
      k'b <- unMaple $ k b
      kbc <- unMaple $ app1 k'b (constant c)
      return kbc))
    return ("("++c++" -> " ++ body ++")")
  lebesgue      = fquant "Int" (constant "-infinity") (constant "infinity")
  {- Maple $ do
    m <- gensym "m"
    x <- gensym "x"
    return ("("++m++" -> Int("++m++"("++x++"),"++x++"=-infinity..infinity))")
    -}
  superpose l   = Maple $ do
    c <- gensym "c"
    let l' = map (unMaple . wmtom c) l
    res <- fmap (concat . intersperse " + ") (sequence l')
    return $ if res == "" then "(" ++ c ++ " -> 0 )" else "(" ++ c ++ " -> " ++ res ++ ")"
  uniform (Maple a) (Maple b) = Maple $ do
    a' <- a
    b' <- b
    let weight = "(1/("++b'++" - "++a'++")) *"
    x <- gensym "x"
    f <- gensym "f"
    return $ "(proc ("++f++") local "++x++"; "++x++" := gensym(`h`);" ++
           "Int(" ++ weight ++ f++"("++x++")"++
               ","++x++"=" ++ a' ++ ".." ++ b' ++") end proc)"
    -- return ("("++m++" -> Int("++weight ++ m++"("++x++"),"++x++"="++a'++".."++b'++"))")
  counting      = fquant "Sum" (constant "-infinity") (constant "infinity")
    {-Maple $ do
    m <- gensym "m"
    i <- gensym "i"
    return ("("++m++" -> Sum("++m++"("++i++"),"++i++"=-infinity..infinity))")
    -}
  categorical _ = Maple (return "missing_categorical")

op :: Int -> Maple a -> Maple b 
op n (Maple x) = Maple $ x >>= \x' -> return ("op(" ++ show n ++ ", " ++ x' ++ ")")

instance Embed Maple where 
  _Nil = constant "Nil"
  _Cons = app2 "Cons"

  _Z = app1 "Zero"
  _S = app1 "Succ"

  voidSOP _ = constant "HakaruError (`Datatype with no constructors`)"

  tag :: forall xss t . (Embeddable t) => Maple (SOP xss) -> Maple (Tag t xss)
  -- tag = app1 "Tag" 

  tag = app2 "Tag"
         (constant $ datatypeName $ datatypeInfo (Proxy :: Proxy t))

  caseProd x f = f (op 1 x) (op 2 x)

  -- op isn't best here, FIXME
  caseSum (Maple ab) ka kb = Maple $ do
    ab' <- ab
    op0 <- return $ "op(0,"++ ab' ++ ")"
    op1 <- return $ "op(1,"++ ab' ++ ")"
    left <- unMaple $ ka (constant op1)
    right <- unMaple $ kb (constant op1)
    return $ "if_(" ++ op0 ++ " = Zero, " ++ left ++ ", " ++ right ++ ")"

  untag = op 2 
