{-# LANGUAGE GADTs, TypeFamilies #-}
{-# OPTIONS -W #-}

module InterpreterSymbolic where

data Prob
data Measure a
data Dist a

-- symbolic AST (pulled from Syntax.hs for now)
class Symbolic repr where
  real 			:: Double -> repr Double
  bool 			:: Bool -> repr Bool
  add, mul  		:: repr Double -> repr Double -> repr Double
  bind	 		:: repr (Measure a) -> (repr a -> repr (Measure a)) 
	   		   -> repr (Measure a)
  ret 			:: repr a -> repr (Measure a)
  conditioned, unconditioned :: repr (Dist a) -> repr (Measure a)
  uniform, normal :: repr Double -> repr Double -> repr (Dist Double)

-- printer
type VarCounter = Int
newtype S a = S { unS :: Bool -> VarCounter -> String }

instance Symbolic S where
  real x 	= S $ \_ _ -> show x
  bool x 	= S $ \_ _ -> show x
  add e1 e2 	= S $ \f h -> unS e1 f h ++ "+" ++ unS e2 f h
  mul e1 e2 	= S $ \f h -> unS e1 f h ++ "*" ++ unS e2 f h
  bind m c 	= S $ \f h -> unS m True h ++ 
  		  unS (c (S $ \_ _ -> ("x" ++ show h))) (f) (succ h)
  		  ++ unS m False h 
  uniform e1 e2 = S $ \f h -> if f == True then  
		  show (1/((read (unS e2 f h) :: Double) - 
		  (read (unS e1 f h) :: Double))) ++ " * Int (" 
		  else ", x" ++ show h ++ "=" ++ unS e1 f h ++ ".." ++ 
		  unS e2 f h ++ ")"
  normal e1 e2 	= S $ \f h -> if f == True then  
		  "Int (PDF (Normal (" ++ unS e1 f h ++ ", " ++
		  unS e2 f h ++ ", x" ++ show h ++ ") * "  
		  else ", x" ++ show h ++ "=" ++ unS e1 f h ++ ".." ++ 
		  unS e2 f h ++ ")"			  
  unconditioned e = S $ \f h -> unS e f h
  conditioned e  = S $ \f h -> unS e f h  
  ret e 	 = S $ \f h -> "g(" ++ unS e f h ++ ")"

view e = unS e True 0

-- testing
exp1 = unconditioned (uniform (real 1) (real 3)) `bind` \s ->
       ret s

exp2 = unconditioned (uniform (real 1) (real 3)) `bind` \s ->
       unconditioned (uniform (real (-1)) (real 1)) `bind` \x ->
       let y = s `mul` x in ret y

exp3 = unconditioned (uniform (real 1) (real 3)) `bind` \s ->
       unconditioned (normal (real 0) (real 2)) `bind` \x ->
       let y = s `add` x in ret y
	   
test = view exp1
test2 = view exp2
test3 = view exp3
