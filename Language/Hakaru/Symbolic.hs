{-# LANGUAGE GADTs, TypeFamilies #-}
{-# OPTIONS -W #-}

module Language.Hakaru.Symbolic where

data Prob
data Measure a
data Dist a

-- Symbolic AST (from Syntax.hs)
class Symbolic repr where
  real 			    :: Double -> repr Double
  bool 			    :: Bool -> repr Bool
  add, minus, mul, exp  	:: repr Double -> repr Double -> repr Double
  sqrt, cos, sin	:: repr Double -> repr Double
  bind	 		    :: repr (Measure a) -> (repr a -> repr (Measure a)) 
	   		           -> repr (Measure a)
  ret 			    :: repr a -> repr (Measure a)
  uniformD, uniform, normal :: repr Double -> repr Double -> repr (Dist Double)
  conditioned, unconditioned :: repr (Dist a) -> repr (Measure a)

-- Printer (to Maple)
type VarCounter = Int
newtype Maple a = Maple { unMaple :: Bool -> VarCounter -> String }

instance Symbolic Maple where
  real x 	= Maple $ \_ _ -> show x
  bool x 	= Maple $ \_ _ -> show x
  add e1 e2 	= Maple $ \f h -> unMaple e1 f h ++ "+" ++ unMaple e2 f h
  minus e1 e2 	= Maple $ \f h -> unMaple e1 f h ++ "-" ++ unMaple e2 f h  
  mul e1 e2 	= Maple $ \f h -> unMaple e1 f h ++ "*" ++ unMaple e2 f h
  exp e1 e2     = Maple $ \f h -> unMaple e1 f h ++ "^" ++ unMaple e2 f h
  sqrt e	= Maple $ \f h -> "sqrt(" ++ unMaple e f h ++ ")"
  cos e		= Maple $ \f h -> "cos(" ++ unMaple e f h ++ ")"
  sin e		= Maple $ \f h -> "sin(" ++ unMaple e f h ++ ")"
  bind m c 	= Maple $ \f h -> unMaple m True h ++ 
  		          unMaple (c (Maple $ \_ _ -> ("x" ++ show h))) (f) (succ h)
  		          ++ unMaple m False h 
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
  normal e1 e2 	= Maple $ \f h -> if f == True then  
		          "Int (PDF (Normal (" ++ unMaple e1 f h ++ ", " ++
		          unMaple e2 f h ++ ", x" ++ show h ++ ") * "  
		          else ", x" ++ show h ++ "=" ++ unMaple e1 f h ++ ".." ++ 
		          unMaple e2 f h ++ ")"			  
  unconditioned e = Maple $ \f h -> unMaple e f h
  conditioned e   = Maple $ \f h -> unMaple e f h  
  ret e 	      = Maple $ \f h -> "g(" ++ unMaple e f h ++ ")"

view e = unMaple e True 0

-- TEST CASES
exp1 = unconditioned (uniform (real 1) (real 3)) `bind` \s ->
       ret s

-- Borel's Paradox Simplified
exp2 = unconditioned (uniformD (real 1) (real 3)) `bind` \s ->
       unconditioned (uniform  (real (-1)) (real 1)) `bind` \x ->
       let y = s `mul` x in ret y

-- Borel's Paradox
exp3 = unconditioned (uniformD (real 1) (real 2)) `bind` \s ->
       unconditioned (uniform  (real (-1)) (real 1)) `bind` \x ->
       let y = (Language.Hakaru.Symbolic.sqrt ((real 1 ) `minus` 
			   (Language.Hakaru.Symbolic.exp s (real 2)))) `mul`
	           (Language.Hakaru.sin x) in ret y  

test = view exp1
test2 = view exp2
test3 = view exp3
