{-# LANGUAGE GADTs
           , KindSignatures
           , DataKinds
           , TypeOperators
           , TypeFamilies
           , InstanceSigs
           , ScopedTypeVariables
           , FlexibleInstances
           , MultiParamTypeClasses
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.29
-- |
-- Module      :  Language.Hakaru.Maple
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Expect-Maple printing interpretation
-- This fuses two operations:
-- 1. the Expect program transformation
-- 2. the "Expect repr" instantiation at repr = Maple
-- where Maple is a "printing in Maple syntax" interpretation

-- We won't need fancy type gymnastics (which Expect requires) because
-- we're squishing everything into String.
----------------------------------------------------------------
module Language.Hakaru.Maple (Maple(..), runMaple) where

import Data.Ratio
import Control.Monad (liftM, liftM2)
import Control.Monad.Trans.State.Strict (State, evalState, state)
import Data.List (intersperse)

import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.ABT2
{-
import Language.Hakaru.Syntax (Number(..),
    Order(..), Base(..), Integrate(..), Lambda(..), Mochastic(..), 
    sumV, Hakaru(..))
-}
----------------------------------------------------------------


newtype Maple (a :: Hakaru) = Maple { unMaple :: State Int String }

runMaple :: Maple a -> Int -> String
runMaple (Maple a) = evalState a

constant :: String -> Maple a
constant = Maple . return

app1 :: String -> Maple a -> Maple b
app1 fn = Maple . liftM (\z -> fn ++ "(" ++ z ++ ")") . unMaple

app2 :: String -> Maple a -> Maple b -> Maple c
app2 fn (Maple x) (Maple y) = 
    Maple $ liftM2 (\a b -> fn ++ "(" ++ a ++ ", " ++ b ++ ")") x y

lam1 :: String -> (Maple a  -> Maple b) -> Maple (a ':-> b)
lam1 s k = Maple $ do
    x <- gensym s
    cont <- unMaple (k (constant x))
    return ("(" ++ x ++ " -> " ++ cont ++ ")")

-- uncurried 2-argument lambda
lam2 :: String -> (Maple a -> Maple b -> Maple c) -> Maple (HPair a b ':-> c)
lam2 s k = Maple $ do
    x <- gensym s
    y <- gensym s
    cont <- unMaple (k (constant x) (constant y))
    return ("( (" ++ x ++ " , " ++ y ++ ") -> " ++ cont ++ ")")

-- curried 2-argument lambda
lam2c :: String -> (Maple a -> Maple b -> Maple c) -> Maple (a ':-> b ':-> c)
lam2c s k = Maple $ do
    x <- gensym s
    y <- gensym s
    cont <- unMaple (k (constant x) (constant y))
    return ("(" ++ x ++ " -> " ++ y ++ "-> " ++ cont ++ ")")

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
    -- rather than a new Undef symbol, or undefined, pick an absurd
    -- value which has a decent chance of being easy to spot.
    liftM (\a -> "(x -> piecewise(x<0, -337, " ++ fn ++ "(x)))(" ++ a ++ ")") x

{-
-- TODO: reimplement using the new AST

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
        return $ "if_(" ++ b' ++ ", " ++ et' ++ ", " ++ ef' ++ ")"
    -- fix       = app1 "(proc (f) local x; x := f(x) end proc)" . lam
    reduce r z v = Maple $ do
        z' <- unMaple z
        v' <- unMaple v
        body <- unMaple $ lam2c "z" r
        return (
            "Reduce(" ++ body ++ "," ++ z' ++ ", " ++ v' ++ ")")

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
wmtom :: String -> (Maple 'HProb, Maple ('HMeasure b)) -> Maple b
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
    counting      = fquant "Sum" (constant "-infinity") (constant "infinity")
    categorical (Maple v) = Maple $ do
        a <- unMaple $ constant "0"
        sz <- unMaple $ size $ Maple v
        b <- unMaple $ constant ("(" ++ sz ++ "-1)")
        v' <- unMaple $ sumV (Maple v)
        weight <- unMaple $ constant ("(1/("++v'++"))")
        w <- gensym "w"
        x <- gensym "i"
        f <- gensym "f"
        return $ "(proc ("++f++") local "++x++","++w++"; "++
                x++ " := gensym(`h`);" ++
                w++ " := " ++ weight ++ ";" ++
            "Sum(" ++ w ++ " * " ++ f++"("++x++")"++
                ","++x++"=" ++ a ++ ".." ++ b ++") end proc)"
-}

op :: Int -> Maple a -> Maple b 
op n (Maple x) =
    Maple $ x >>= \x' -> return ("op(" ++ show n ++ ", " ++ x' ++ ")")

{-
instance Embed Maple where 
  _Nil = constant "Nil"
  _Cons = app2 "Cons"

  _Z = app1 "Zero"
  _S = app1 "Succ"

  muE = app1 "Mu" 
  unMuE = op 1 

  konst = app1 "K" 
  unKonst = op 1 

  ident = app1 "Id"
  unIdent = op 1 

  voidSOP _ = constant "HakaruError (`Datatype with no constructors`)"

  tag :: forall f t . (Embeddable t) => Maple (HMu f) -> Maple (HTag t f)
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

  -- This is probably not the best way of doing this. 
  natFn f x = Maple $ do 
    xs <- unMaple x 
    fs <- unMaple (lam f)   
    return $ "subsindets( " ++ xs ++ " , 'Id'(anything), (x) -> 'Id' (" ++ fs ++ "(op(1, x)) ))" 
-}

----------------------------------------------------------------
----------------------------------------------------------- fin.
