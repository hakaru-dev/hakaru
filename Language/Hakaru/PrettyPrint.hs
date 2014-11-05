{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# OPTIONS -Wall #-}
module Language.Hakaru.PrettyPrint (PrettyPrint, runPrettyPrint) where

-- Pretty-printing interpretation

import Language.Hakaru.Syntax
import Language.Hakaru.Util.Pretty
import Text.PrettyPrint hiding (parens)

newtype PrettyPrint a = PP ([String] -> Int -> [Doc])

runPrettyPrint :: PrettyPrint a -> Doc
runPrettyPrint (PP a) = sep (a [ 'x' : show i | i <- [0::Int ..] ] 0)

apply1 :: String -> PrettyPrint a -> PrettyPrint b
apply2 :: String -> PrettyPrint a -> PrettyPrint b -> PrettyPrint c
apply3 :: String -> PrettyPrint a -> PrettyPrint b -> PrettyPrint c ->
          PrettyPrint d

apply1 f (PP a) =
  PP (\xs p -> [prettyFun (p > 10) f (sep (a xs 11))])
apply2 f (PP a) (PP b) =
  PP (\xs p -> [prettyFun (p > 10) f (sep [sep (d xs 11) | d <- [a,b]])])
apply3 f (PP a) (PP b) (PP c) =
  PP (\xs p -> [prettyFun (p > 10) f (sep [sep (d xs 11) | d <- [a,b,c]])])

adjustHead :: (Doc -> Doc) -> [Doc] -> [Doc]
adjustHead f []     = [f empty]
adjustHead f (d:ds) = f d : ds

adjustLast :: (Doc -> Doc) -> [Doc] -> [Doc]
adjustLast f []     = [f empty]
adjustLast f [d]    = [f d]
adjustLast f (d:ds) = d : adjustLast f ds

parens :: Bool -> [Doc] -> [Doc]
parens True  = adjustHead (char '(' <>)
             . adjustLast (<> char ')')
             . map (nest 1)
parens False = id

fun1 :: (PrettyPrint a -> PrettyPrint b) -> PrettyPrint (a -> b)
fun1 f = PP (\(x:xs) p ->
  let PP b = f (PP (\_ _ -> [text x])) in
  parens (p > 10) (text ('\\' : x ++ " ->") : b xs 0))

fun2 :: (PrettyPrint a -> PrettyPrint b -> PrettyPrint c) ->
        PrettyPrint (a -> b -> c)
fun2 f = PP (\(x:x':xs) p ->
  let PP b = f (PP (\_ _ -> [text x])) (PP (\_ _ -> [text x'])) in
  parens (p > 10) (text ('\\' : x ++ ' ' : x' ++ " ->") : b xs 0))

instance Order PrettyPrint a where
  less = op 4 "<" 5 5

instance Num (PrettyPrint a) where
  (+)           = op 6 "+" 6 7
  (*)           = op 7 "*" 7 8
  (-)           = op 6 "-" 6 7
  negate (PP b) = PP (\xs p -> [prettyParen (p > 6) (char '-' <> sep (b xs 7))])
  abs           = apply1 "abs"
  signum        = apply1 "signum"
  fromInteger n = PP (\_ _ -> [integer n])

instance Fractional (PrettyPrint a) where
  (/)            = op 7 "/" 7 8
  recip          = apply1 "recip"
  fromRational n = PP (\_ p -> [text (showRatio p n "")])

instance Floating (PrettyPrint a) where
  pi      = PP (\_ _ -> [text "pi"])
  exp     = apply1 "exp"
  sqrt    = apply1 "sqrt"
  log     = apply1 "log"
  (**)    = op 8 "**" 9 8
  logBase = apply2 "logBase"
  sin     = apply1 "sin"
  cos     = apply1 "cos"
  tan     = apply1 "tan"
  asin    = apply1 "asin"
  acos    = apply1 "acos"
  atan    = apply1 "atan"
  sinh    = apply1 "sinh"
  cosh    = apply1 "cosh"
  tanh    = apply1 "tanh"
  asinh   = apply1 "asinh"
  atanh   = apply1 "atanh"
  acosh   = apply1 "acosh"

instance Base PrettyPrint where
  unit              = PP (\_ _ -> [text "unit"])
  pair              = apply2 "pair"
  unpair (PP xy) k  = let PP k' = fun2 k in PP (\xs p -> parens (p > 9)
                    $ adjustHead (sep (xy xs 9) <+> text "`unpair`" <+>)
                    $ k' xs 10)
  inl               = apply1 "inl"
  inr               = apply1 "inr"
  uneither xy kx ky = apply3 "uneither" xy (fun1 kx) (fun1 ky)
  unsafeProb        = apply1 "unsafeProb"
  fromProb          = apply1 "fromProb"
  pi_               = PP (\_ _ -> [text "pi_"])
  exp_              = apply1 "exp_"
  log_              = apply1 "log_"
  sqrt_             = apply1 "sqrt_"
  pow_              = apply2 "pow_"
  betaFunc          = apply2 "betaFunc"
  fix f             = apply1 "fix" (fun1 f)

instance Mochastic PrettyPrint where
  dirac         = apply1 "dirac"
  bind (PP m) k = let PP k' = fun1 k in PP (\xs p -> parens (p > 1)
                $ adjustHead (sep (m xs 1) <+> text "`bind`" <+>)
                $ k' xs 2)
  lebesgue      = PP (\_ _ -> [text "lebesgue"])
  superpose pms = apply1 "superpose" (PP (\xs _ ->
                    [brackets (nest 1 (sep (punctuate comma
                       [ prettyPair (sep (p xs 0)) (sep (m xs 0))
                       | (PP p, PP m) <- pms ])))]))

instance Integrate PrettyPrint where
  integrate a b f  = apply3 "integrate" a b (fun1 f)
  infinity         = PP (\_ _ -> [text "infinity"])
  negativeInfinity = PP (\_ _ -> [text "negativeInfinity"])

instance Lambda PrettyPrint where
  lam f = let PP f' = fun1 f in
          PP (\xs p -> parens (p > 0) (adjustHead (text "lam $" <+>) (f' xs 0)))
  app   = op 9 "`app`" 9 10

op :: Int -> String -> Int -> Int ->
      PrettyPrint a -> PrettyPrint b -> PrettyPrint c
op p0 s p1 p2 (PP a) (PP b) =
  PP (\xs p -> [prettyOp (p > p0) s (sep (a xs p1)) (sep (b xs p2))])
