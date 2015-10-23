-- TODO: [wrengr 2015.10.23] remove this file entirely. There are only three files that depend on this: "Tests.ImportanceSampler", "Tests.Metropolis", @Examples/@"Examples"

-- The lambda-calculus part of the language, which can be shared
module Language.Hakaru.Lambda(lit, dbl, lam, app, fix, ifThenElse) where

lit :: (Eq a) => a -> a
lit = id

-- raw lit is a pain to use.  These are nicer
dbl :: Double -> Double
dbl = lit

lam :: (a -> b) -> (a -> b)
lam f = f

app :: (a -> b) -> a -> b
app f x = f x

fix :: ((a -> b) -> (a -> b)) -> (a -> b)
fix g = f where f = g f

ifThenElse :: Bool -> a -> a -> a
ifThenElse True  t _ = t
ifThenElse False _ f = f
