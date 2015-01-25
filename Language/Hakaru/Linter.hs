{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
module Language.Hakaru.Linter where

import Language.Hakaru.Syntax

newtype Linter a = Linter Bool

instance (Number a) => Order Linter a where
    less  = apply2
    equal = apply2

instance Num (Linter a) where
    fromInteger x = Linter True
    (+)           = apply2
    (-)           = apply2
    (*)           = apply2
    abs           = apply1
    negate        = apply1
    signum        = apply1

instance Fractional (Linter a) where
    (/)             = apply2
    recip           = apply1
    fromRational x  = Linter True

instance Floating (Linter a) where
    pi       = Linter True
    exp      = apply1
    sqrt     = apply1
    log      = apply1
    (**)     = apply2
    logBase  = apply2
    sin      = apply1
    cos      = apply1
    asin     = apply1
    acos     = apply1
    atan     = apply1
    sinh     = apply1
    cosh     = apply1
    tanh     = apply1
    asinh    = apply1
    atanh    = apply1
    acosh    = apply1

instance Base Linter where
    unit               = Linter True
    pair               = apply2
    unpair xy k        = apply2 (apply1 xy) (fun2 k)
    inl                = apply1
    inr                = apply1
    uneither xy kx ky  = apply3 (apply1 xy) (fun1 kx) (fun1 ky)
    true               = Linter True
    false              = Linter True
    if_                = apply3
    nil                = Linter True
    cons               = apply2
    unlist an kn kc    = apply3 an kn (fun2 kc)
    unsafeProb         = apply1
    fromProb           = apply1
    fromInt            = apply1
    pi_                = Linter True
    exp_               = apply1
    erf                = const1 (Linter False)
    erf_               = const1 (Linter False)
    log_               = apply1
    sqrt_              = apply1
    pow_               = apply2
    infinity           = Linter False
    negativeInfinity   = Linter False
    gammaFunc          = const1 (Linter False)
    betaFunc           = const2 (Linter False)
    fix                = apply1 . fun1

instance Mochastic Linter where
    dirac              = apply1
    bind m k           = apply2 m (fun1 k)
    lebesgue           = Linter False
    counting           = Linter False
    superpose          = applyPairs
    uniform            = apply2
    normal             = apply2
    mix                = applyPairs
    categorical        = applyPairs
    poisson            = apply1
    gamma              = apply2
    beta               = apply2

instance Integrate Linter where
    integrate = const3 (Linter False)
    summate   = const3 (Linter False)

instance Lambda Linter where
    lam  = fun1
    app  = apply2

runLinter :: Linter a -> Bool
runLinter (Linter a)  = a

apply1 :: Linter a -> Linter b
apply1 (Linter a) = Linter a

apply2 :: Linter a -> Linter b -> Linter c
apply2 (Linter a) (Linter b) = Linter $ and [a,b] 

apply3 :: Linter a -> Linter b -> Linter c -> Linter d
apply3 (Linter a) (Linter b) (Linter c) = Linter $ and [a,b,c]

applyPairs :: [(Linter a, Linter b)] -> Linter c
applyPairs []                       = Linter True
applyPairs ((Linter a,Linter b):xs) =
    apply2 (Linter $ and [a,b]) (applyPairs xs)

fun1 :: (Linter a -> Linter b) -> Linter (a -> b)
fun1 f = apply1 $ f $ Linter True

fun2 :: (Linter a -> Linter b -> Linter c) ->
        Linter (a -> b -> c)
fun2 f = apply1 $ f (Linter True) (Linter True)

const1 :: a -> b -> a
const1 = const

const2 :: a -> b -> c -> a
const2 a b c   = a

const3 :: a -> b -> c -> d -> a
const3 a b c d = a
