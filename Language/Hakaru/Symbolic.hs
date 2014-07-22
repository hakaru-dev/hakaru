{-# LANGUAGE GADTs, TypeFamilies, ScopedTypeVariables #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Symbolic where

data Prob
data Measure a
data Dist a
data Exact

class RealComp repr where
  real                 :: Double -> repr Double
  exp                  :: repr Double -> repr Double -> repr Double
  sqrt, cos, sin       :: repr a -> repr Double

-- polymorphic operations and integer powering
class SymbComp repr where
  add, minus, mul :: repr a -> repr a -> repr a
  pow             :: repr a -> repr Integer -> repr a
  scale           :: repr Integer -> repr a -> repr a

class IntComp repr where
  int                  :: Integer -> repr Integer

class BoolComp repr where
  bool                 :: Bool -> repr Bool

class MeasMonad repr where
  bind                 :: repr (Measure a) -> (repr a -> repr (Measure b)) 
                          -> repr (Measure b)
  ret                  :: repr a -> repr (Measure a)

class Distrib repr where
  uniform, normal :: repr Double -> repr Double -> repr (Dist Double)
  uniformD        :: repr Integer -> repr Integer -> repr (Dist Integer)

class Conditioning repr where
  conditioned, unconditioned :: repr (Dist a) -> repr (Measure a)

-- Printer (to Maple)
data Pos = Front | Back
type VarCounter = Int
newtype Maple a = Maple { unMaple :: Pos -> VarCounter -> String }

-- if it weren't for the constraints, we could/should use Applicative
pure :: Show a => a -> Maple a
pure x = Maple $ \_ _ -> show x

liftA1 :: (String -> String) -> Maple a -> Maple a
liftA1 pr x = Maple $ \f h -> pr (unMaple x f h)

liftA2 :: (String -> String -> String) -> Maple a -> Maple a -> Maple a
liftA2 pr e1 e2 = Maple $ \f h -> pr (unMaple e1 f h) (unMaple e2 f h)

-- variant for ret
liftA1M :: (String -> String) -> Maple a -> Maple (Measure a)
liftA1M pr x = Maple $ \f h -> pr (unMaple x f h)

-- variant for things that go into Double
liftA1D :: (String -> String) -> Maple a -> Maple Double
liftA1D pr x = Maple $ \f h -> pr (unMaple x f h)

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
  sqrt  = liftA1D $ mkPr "sqrt"
  cos   = liftA1D $ mkPr "cos"
  sin   = liftA1D $ mkPr "sin"

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
                     show (1/((read e2 :: Double) - (read e1)))) 
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

-- TEST CASES
exp1, exp2, exp3, exp4 :: Maple (Measure Double)
exp1 = unconditioned (uniform (real 1) (real 3)) `bind` ret

-- Borel's Paradox Simplified
exp2 = unconditioned (uniformD (int 1) (int 3)) `bind` \s ->
       unconditioned (uniform  (real (-1)) (real 1)) `bind` \x ->
       let y = s `scale` x in ret y

-- Borel's Paradox
exp3 = unconditioned (uniformD (int 1) (int 2)) `bind` \s ->
       unconditioned (uniform  (real (-1)) (real 1)) `bind` \x ->
       let y = (Language.Hakaru.Symbolic.sqrt ((int 1 ) `minus` 
               (Language.Hakaru.Symbolic.pow s (int 2)))) `mul`
               (Language.Hakaru.Symbolic.sin x) in ret y  

exp4 = unconditioned (normal (real 1) (real 4)) `bind` ret

test, test2, test3, test4 :: String
test = view exp1
test2 = view exp2
test3 = view exp3
test4 = view exp4
