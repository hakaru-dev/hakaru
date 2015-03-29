{-# LANGUAGE Rank2Types, ImpredicativeTypes #-}

module Tests.Lazy where

import Prelude hiding (Real)

import Language.Hakaru.Lazy
import Language.Hakaru.Any (Any(Any, unAny))
import Language.Hakaru.Syntax (Real, Measure, Base(..),
                               ununit, max_, liftM, liftM2, bind_,
                               Mochastic(..), Lambda(..))
import Language.Hakaru.Compose
import Language.Hakaru.PrettyPrint (PrettyPrint, runPrettyPrint, leftMode)
import Language.Hakaru.Simplify (Simplifiable, closeLoop, simplify)
import Language.Hakaru.Expect (Expect)
import Language.Hakaru.Maple (Maple)
import Tests.TestTools    

import Data.Typeable (Typeable)    
import Test.HUnit
import Control.Monad ((>=>))
import Data.Function (on)
import Data.List (elem)
import Control.Exception (catch)
    
type Cond repr env ab =
    forall s t. Lazy s (Compose [] t repr) env
        -> Lazy s (Compose [] t repr) ab

try :: (Mochastic repr, Lambda repr, Backward a a) =>
       Cond repr env (Measure (a,b))
    -> [repr (env -> (a -> Measure (a, b)))]
try m = runCompose
      $ lam $ \env ->
      lam $ \t -> runLazy
      -- $ liftM snd_
      $ disintegrate (pair (scalar0 t) unit) (m (scalar0 env))

recover :: (Typeable a) => PrettyPrint a -> IO (Any a)
recover hakaru = closeLoop ("Any (" ++ leftMode (runPrettyPrint hakaru) ++ ")")

testS' :: (Simplifiable a) => Any a -> Assertion
testS' t = do
    p <- simplify (unAny t) `catch` handleSimplify (unAny t)
    let s = result (unAny p)
    assertResult (show s)

testL :: (Backward a a, Typeable a, Typeable b,
         Simplifiable a, Simplifiable b, Simplifiable env) => 
         Cond PrettyPrint env (Measure (a,b))
      -> [(Expect Maple env, Expect Maple a, Any (Measure (a, b)))]
      -> Assertion
testL f slices = do
  ds <- mapM recover (try f)
  assertResult ds
  mapM_ testS' ds
  mapM_ (\(env,a,t') ->
         testSS [(app (app (unAny d) env) a) | d <- ds] (unAny t')) slices
         
exists :: PrettyPrint a -> [PrettyPrint a] -> Assertion
exists t ts' = assertBool "no correct disintegration" $
               elem (result t) (map result ts')

allTests :: Test
allTests = test [ "t0"  ~: testL t0 []
                , "t1"  ~: testL t1 []
                , "t2"  ~: testL t2 []
                , "t3"  ~: testL t3 []
                , "t4"  ~: testL t4 []
                , "t5"  ~: testL t5 []
                , "t6"  ~: testL t6 []
                , "t7"  ~: testL t7 []
                , "t8"  ~: testL t8 []
                , "t9"  ~: testL t9 []
                , "t10" ~: testL t10 [] ]
                 
t0 :: (Mochastic repr) => Cond repr () (Measure (Real,Real))
t0 = \u -> ununit u $
     normal 0 1 `bind` \x ->
     normal x 1 `bind` \y ->
     dirac (pair y x)

t1 :: (Mochastic repr) => Cond repr () (Measure (Real,Real)) 
t1 = \u -> ununit u $
     uniform 0 1 `bind` \x ->
     uniform 0 1 `bind` \y ->
     dirac (pair (exp x) (y + x))

t2 :: (Mochastic repr) => Cond repr () (Measure (Real,Real))
t2 = \u -> ununit u $
     uniform 0 1 `bind` \x ->
     uniform 0 1 `bind` \y ->
     dirac (pair (y + x) (exp x))

t3 :: (Mochastic repr) => Cond repr () (Measure (Real, (Real,Real)))
t3 = \u -> ununit u $
     uniform 0 1 `bind` \x ->
     uniform 0 1 `bind` \y ->
     dirac (pair (max_ x y) (pair x y))

t4 :: (Mochastic repr) => Cond repr () (Measure (Real,Real))
t4 = \u -> ununit u $
     uniform 0 1 `bind` \x ->
     dirac (pair (exp x) (-x))

t5 :: (Mochastic repr) => Cond repr () (Measure (Real,()))
t5 = \u -> ununit u $
     liftM (`pair` unit) $
     let m = superpose (replicate 2 (1, uniform 0 1))
     in let add = liftM2 (+)
        in add (add m m) m

t6 :: (Mochastic repr) => Cond repr () (Measure (Real,Real))
t6 = \u -> ununit u $
     uniform 0 1 `bind` \x ->
     uniform 0 1 `bind` \y ->
     dirac (pair (x+y) (x-y))

t7 :: (Mochastic repr) => Cond repr () (Measure (Real,(Measure Real)))
t7 = \u -> ununit u $
     uniform 0 1 `bind` \y ->
     uniform 0 1 `bind` \x ->
     dirac (pair (x+y) (uniform 0 1 `bind_` dirac y))

t8 :: (Mochastic repr) => Cond repr () (Measure (Real,Real))
t8 = \u -> ununit u $
     dirac (uniform 0 1 `bind` \x -> dirac (1+x)) `bind` \m ->
     m `bind` \x ->
     m `bind` \y ->
     dirac (pair x y)

t9 :: (Mochastic repr) => Cond repr () (Measure (Real,Real))
t9 = \u -> ununit u $
     (uniform 0 1 `bind` \x -> dirac (dirac (1+x))) `bind` \m ->
     m `bind` \x ->
     m `bind` \y ->
     dirac (pair x y)

t10 :: (Mochastic repr) => Cond repr () (Measure ((Real,Real), Real))
t10 = \u -> ununit u $
      normal 0 1 `bind` \x ->
      plate (vector 10 (\i -> normal x (unsafeProb (fromInt i) + 1))) `bind` \ys ->
      dirac (pair (pair (index ys 3) (index ys 4)) x)
