{-# LANGUAGE GADTs, TypeFamilies #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Symbolic where

data Prob
data Measure a
data Dist a

-- Symbolic AST (from Syntax.hs)
class RealComp repr where
  real                 :: Double -> repr Double
  add, minus, mul, exp :: repr Double -> repr Double -> repr Double
  sqrt, cos, sin       :: repr Double -> repr Double

class BoolComp repr where
  bool                 :: Bool -> repr Bool

class MeasMonad repr where
  bind                 :: repr (Measure a) -> (repr a -> repr (Measure a)) 
                          -> repr (Measure a)
  ret                  :: repr a -> repr (Measure a)

class Distrib repr where
  uniformD, uniform, normal :: repr Double -> repr Double -> repr (Dist Double)

class Conditioning repr where
  conditioned, unconditioned :: repr (Dist a) -> repr (Measure a)

-- Printer (to Maple)
type VarCounter = Int
newtype Maple a = Maple { unMaple :: Bool -> VarCounter -> String }

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

mkPr :: String -> (String -> String)
mkPr s t = s ++ "(" ++ t ++ ")"

d2m :: Maple (Dist a) -> Maple (Measure a)
d2m e = Maple $ unMaple e

infixPr :: String -> (String -> String -> String)
infixPr s a b = a ++ s ++ b

instance RealComp Maple where
  real  = pure
  add   = liftA2 $ infixPr "+"
  minus = liftA2 $ infixPr "-"
  mul   = liftA2 $ infixPr "*"
  exp   = liftA2 $ infixPr "^"
  sqrt  = liftA1 $ mkPr "sqrt"
  cos   = liftA1 $ mkPr "cos"
  sin   = liftA1 $ mkPr "sin"

instance BoolComp Maple where
  bool  = pure

instance MeasMonad Maple where
  ret      = liftA1M $ mkPr "g"
  bind m c = Maple $ \f h -> unMaple m True h ++ 
                    unMaple (c (Maple $ \_ _ -> ("x" ++ show h))) (f) (succ h)
                    ++ unMaple m False h 

instance Distrib Maple where
  uniform e1 e2  = Maple $ \f h -> if f == True then  
                  show (1/((read (unMaple e2 f h) :: Double) - 
                  (read (unMaple e1 f h) :: Double))) ++ " * Int (" 
                  else ", x" ++ show h ++ "=" ++ unMaple e1 f h ++ ".." ++ 
                  unMaple e2 f h ++ ")"
  uniformD e1 e2 = Maple $ \f h -> if f == True then  
                  show (1/((read (unMaple e2 f h) :: Double) - 
                  (read (unMaple e1 f h) :: Double))) ++ " * Sum (" 
                  else ", x" ++ show h ++ "=" ++ unMaple e1 f h ++ ".." ++ 
                  unMaple e2 f h ++ ")"                  
  normal e1 e2     = Maple $ \f h -> if f == True then  
                  "Int (PDF (Normal (" ++ unMaple e1 f h ++ ", " ++
                  unMaple e2 f h ++ ", x" ++ show h ++ ") * "  
                  else ", x" ++ show h ++ "=" ++ unMaple e1 f h ++ ".." ++ 
                  unMaple e2 f h ++ ")"              

instance Conditioning Maple where
  unconditioned = d2m
  conditioned   = d2m

view :: Maple a -> String
view e = unMaple e True 0

-- TEST CASES
exp1, exp2, exp3 :: Maple (Measure Double)
exp1 = unconditioned (uniform (real 1) (real 3)) `bind` ret

-- Borel's Paradox Simplified
exp2 = unconditioned (uniformD (real 1) (real 3)) `bind` \s ->
       unconditioned (uniform  (real (-1)) (real 1)) `bind` \x ->
       let y = s `mul` x in ret y

-- Borel's Paradox
exp3 = unconditioned (uniformD (real 1) (real 2)) `bind` \s ->
       unconditioned (uniform  (real (-1)) (real 1)) `bind` \x ->
       let y = (Language.Hakaru.Symbolic.sqrt ((real 1 ) `minus` 
               (Language.Hakaru.Symbolic.exp s (real 2)))) `mul`
               (Language.Hakaru.Symbolic.sin x) in ret y  

test, test2, test3 :: String
test = view exp1
test2 = view exp2
test3 = view exp3
