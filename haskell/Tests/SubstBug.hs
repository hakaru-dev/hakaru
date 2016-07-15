{-# LANGUAGE TypeOperators
           , DataKinds
           #-}

module Tests.SubstBug where

import Data.Text (pack)
import Language.Hakaru.Syntax.ABT    
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Prelude (pair)
import Language.Hakaru.Types.Sing
import Language.Hakaru.Types.DataKind

z :: Variable 'HInt
z = Variable (pack "z") 3 SInt    

y :: Variable 'HReal
y = Variable (pack "y") 2 SReal

x :: Variable 'HReal
x = Variable (pack "x") 1 SReal

w :: Variable 'HInt
w = Variable (pack "w") 0 SInt

f0 :: TrivialABT Term '[] ('HReal ':-> HPair 'HReal 'HInt)
f0 = syn (Lam_ :$ bind x (pair (var y) (var w)) :* End)

-- Works
f1 :: TrivialABT Term '[] ('HReal ':-> HPair 'HReal 'HInt)
f1 = subst y (var x) f0

-- Crashes
f2 :: TrivialABT Term '[] ('HReal ':-> HPair 'HReal 'HInt)
f2 = subst w (var z) f1

-- Crashes     
f3 :: TrivialABT Term '[] ('HReal ':-> HPair 'HReal 'HInt)
f3 = subst z (var w) f1


{- | What's going on here?

Consider an expression:
  
  f0 = \ (x::real) -> ( (y::real) , (w::int) )

We want to substitute (x::real) for (y::real) in f0.
Calling (subst y x f0) will:

1. Check varEq (y::real) (x::real), which is false.
2. Check using varEq if (x::real) occurs in the set {x::real, y::real, w::int}.
   This returns true, so a new variable (z::real) is generated.
   The variable z is only guaranteed to be different from x, y, and w.
3. Return the expression:

  f1 = \ (z::real) -> ( (x::real) , (w::int) )

Now we want to substitute (z::int) for (w::int) in f1.
This is legal -- we could have had a variable (z::int) from a long time ago,
and we are simply calling subst with it now.
Calling (subst w z f1) will:

1. Check varEq (w::int) (z::real), which is false.
2. Check using varEq if (z::int) occurs in {z::real, x::real, w::int}.
   This returns a VarEqTypeError while comparing (z::int) with (z::real).

Ok that didn't work, whatever. Now we want to substitute (w::int) for (z::int) in f1.
Calling (subst z w f1) will:

1. Check varEq (z::int) (z::real), which returns a VarEqTypeError.

-}     
