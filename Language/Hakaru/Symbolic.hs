{-# LANGUAGE GADTs, TypeFamilies, ScopedTypeVariables, FlexibleContexts #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Symbolic where

import Prelude hiding (Real)

data Real
data Prob
data Measure a
data Dist a
data Exact

class IntComp repr where
  int                  :: Integer -> repr Integer

class BoolComp repr where
  bool                 :: Bool -> repr Bool

class RealComp repr where
  real                 :: Rational -> repr Real
  exp                  :: repr Real -> repr Real -> repr Real
  sqrt, cos, sin       :: repr Real -> repr Real

-- polymorphic operations and integer powering
-- probably should restrict 'a' to be some kind of numeric type?
class SymbComp repr where
  add, minus, mul :: repr a -> repr a -> repr a
  pow             :: repr Real -> repr Integer -> repr Real
  scale           :: repr Integer -> repr Real -> repr Real

class MeasMonad repr where
  bind                 :: repr (Measure a) -> (repr a -> repr (Measure b)) 
                          -> repr (Measure b)
  ret                  :: repr a -> repr (Measure a)

class Distrib repr where
  uniform, normal :: repr Real -> repr Real -> repr (Dist Real)
  uniformD        :: repr Integer -> repr Integer -> repr (Dist Integer)

class Conditioning repr where
  conditioned, unconditioned :: repr (Dist a) -> repr (Measure a)

-- Printer (to Maple)
data Pos = Front | Back
type VarCounter = Int
newtype Maple a = Maple { unMaple :: Pos -> VarCounter -> String }

type family MPL a
type instance MPL Real     = Rational
type instance MPL Integer  = Integer
type instance MPL Bool     = Bool

-- if it weren't for the constraints, we could/should use Applicative
pure :: Show (MPL a) => MPL a -> Maple a
pure x = Maple $ \_ _ -> show x

liftA1 :: (String -> String) -> Maple a -> Maple a
liftA1 pr x = Maple $ \f h -> pr (unMaple x f h)

liftA2 :: (String -> String -> String) -> Maple a -> Maple a -> Maple a
liftA2 pr e1 e2 = Maple $ \f h -> pr (unMaple e1 f h) (unMaple e2 f h)

-- variant for ret
liftA1M :: (String -> String) -> Maple a -> Maple (Measure a)
liftA1M pr x = Maple $ \f h -> pr (unMaple x f h)

-- variant for pow
liftA2aba :: (String -> String -> String) -> Maple a -> Maple b -> Maple a
liftA2aba pr e1 e2 = Maple $ \f h -> pr (unMaple e1 f h) (unMaple e2 f h)

-- variant for scale
liftA2baa :: (String -> String -> String) -> Maple b -> Maple a -> Maple a
liftA2baa pr e1 e2 = Maple $ \f h -> pr (unMaple e1 f h) (unMaple e2 f h)

mkPr :: String -> (String -> String)
mkPr s t = s ++ "(" ++ t ++ ")"

d2m :: Maple (Dist a) -> Maple (Measure a)
d2m e = Maple $ unMaple e

infixPr :: String -> (String -> String -> String)
infixPr s a b = a ++ s ++ b

-- This is quite scary.  Probably a mistake.
reify :: forall a. Read a => Pos -> VarCounter -> Maple a -> a
reify f h e = (read (unMaple e f h) :: a)

name :: String -> VarCounter -> String
name s h = s ++ show h

var :: String -> VarCounter -> Maple a
var s h = Maple $ \_ _ -> name s h

binder :: (String -> String -> Maybe String) -> 
          (String -> String -> VarCounter -> Maybe String) ->
          String -> 
          Maple a -> Maple a -> Maple (Dist a)
binder pr1 pr2 oper e1 e2 = Maple $ pr_
  where
    pr_ Front h = let x1 = unMaple e1 Front h
                      x2 = unMaple e2 Front h in
                  case (pr1 x1 x2, pr2 x1 x2 h) of
                    (Just z, Just w)   -> z ++ " * " ++ oper ++ " (" ++ w ++ " * "
                    (Nothing, Just w)  -> oper ++ " (" ++ w ++ " * "
                    (Just z, Nothing)  -> z ++ " * " ++ oper ++ " ("
                    (Nothing, Nothing) -> oper ++ " ("
    pr_ Back h  = ", " ++ (name "x" h) ++ "=" ++ unMaple e1 Back h ++
                  ".." ++ unMaple e2 Back h ++ ")"

instance RealComp Maple where
   -- serious problem here: all exact numbers will be printed as
   -- floats, which will really hamper the use of Maple in any 
   -- serious way.  This needs a rethink.
  real  = pure
  exp   = liftA2 $ infixPr "^"
  sqrt  = liftA1 $ mkPr "sqrt"
  cos   = liftA1 $ mkPr "cos"
  sin   = liftA1 $ mkPr "sin"

instance SymbComp Maple where
  add   = liftA2    $ infixPr "+"
  minus = liftA2    $ infixPr "-"
  mul   = liftA2    $ infixPr "*"
  pow   = liftA2aba $ infixPr "^"
  scale = liftA2baa $ infixPr "*"

instance IntComp Maple where
  int  = pure

instance BoolComp Maple where
  bool  = pure

instance MeasMonad Maple where
  ret      = liftA1M $ mkPr "g"
  bind m c = Maple $ \f h -> unMaple m Front h ++ 
                             unMaple (c $ var "x" h) f (succ h) ++
                             unMaple m Back h 

instance Distrib Maple where
  uniform = binder (\e1 e2 -> Just $ 
                     show (1/((read e2 :: Rational) - (read e1 :: Rational)))) 
                   (\_ _ _ -> Nothing) "Int"
  uniformD = binder (\e1 e2 -> 
                      let d = (read e2 :: Integer) - (read e1) in
                      if d == 1 then Nothing
                      else Just $ "(1 / " ++ show d ++ ")")
                   (\_ _ _ -> Nothing) "Sum"
  normal = binder (\_ _ -> Nothing) 
                  (\e1 e2 h -> Just $ "PDF (Normal (" ++ e1 ++ ", " ++ e2 ++ "), " ++ (name "x" h) ++ ")")
                  "Int"

instance Conditioning Maple where
  unconditioned = d2m
  conditioned   = d2m

view :: Maple a -> String
view e = unMaple e Front 0

lift :: Maple Integer -> Maple Real
lift x = Maple $ \f h -> unMaple x f h

-- TEST CASES
exp1, exp2, exp3, exp4 :: Maple (Measure Real)
exp1 = unconditioned (uniform (real 1) (real 3)) `bind` ret

-- Borel's Paradox Simplified
exp2 = unconditioned (uniformD (int 1) (int 3)) `bind` \s ->
       unconditioned (uniform  (real (-1)) (real 1)) `bind` \x ->
       let y = s `scale` x in ret y

-- Borel's Paradox
exp3 = unconditioned (uniformD (int 1) (int 2)) `bind` \s ->
       unconditioned (uniform  (real (-1)) (real 1)) `bind` \x ->
       let y = (Language.Hakaru.Symbolic.sqrt ((real 1 ) `minus` 
               (Language.Hakaru.Symbolic.pow (lift s) (int 2)))) `mul`
               (Language.Hakaru.Symbolic.sin x) in ret y  

exp4 = unconditioned (normal (real 1) (real 4)) `bind` ret

test, test2, test3, test4 :: String
test = view exp1
test2 = view exp2
test3 = view exp3
test4 = view exp4
