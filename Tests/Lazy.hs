{-# LANGUAGE Rank2Types, ImpredicativeTypes #-}

module Tests.Lazy where

import Prelude hiding (Real)

import Language.Hakaru.Lazy
import Language.Hakaru.Any (Any(Any, unAny))
import Language.Hakaru.Syntax (Real, Prob, Measure, Base(..),
                               ununit, max_, liftM, liftM2, bind_,
                               swap_, snd_, bern, 
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
    -> [repr (env -> (a -> Measure b))]
try m = runCompose
      $ lam $ \env ->
      lam $ \t -> runLazy
      $ liftM snd_
      $ disintegrate (pair (scalar0 t) unit) (m (scalar0 env))

recover :: (Typeable a) => PrettyPrint a -> IO (Any a)
recover hakaru = closeLoop ("Any (" ++ leftMode (runPrettyPrint hakaru) ++ ")")

simp :: (Simplifiable a) => Any a -> IO (Any a)
simp = simplify . unAny

testS' :: (Simplifiable a) => Any a -> Assertion
testS' t = do
    p <- simplify (unAny t) `catch` handleSimplify (unAny t)
    let s = result (unAny p)
    assertResult (show s)

testL :: (Backward a a, Typeable a, Typeable b,
         Simplifiable a, Simplifiable b, Simplifiable env) => 
         Cond PrettyPrint env (Measure (a,b))
      -> [(Expect Maple env, Expect Maple a, Any (Measure b))]
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

main :: IO ()
main = do
  -- runTestTT allTests >> return ()
  print . map runPrettyPrint $ try zeroPlusFst

allTests :: Test
allTests = test [ "zeroDiv" ~: testL zeroDiv [(unit, 0, Any $ dirac 0)]
                , "zeroPlusFst" ~: testL zeroPlusFst [(unit, 2, Any $ dirac 2)]
                , "zeroPlusSnd" ~: testL zeroPlusSnd [(unit, unit, Any $ dirac 0)]
                , "prog1s" ~: testL prog1s []
                , "prog2s" ~: testL prog2s []
                , "prog3s" ~: testL prog3s []
                -- , "pair1fst" ~: testL pair1fst []
                -- , "pair1fstSwap" ~: testL pair1fstSwap []
                -- , "borelishSub" ~: testL borelishSub
                --                     [(unit, 0, Any (uniform 0 1))]
                -- , "borelishDiv" ~: testL borelishDiv
                --                     [(unit, 1, Any
                --                       (superpose [(1/2, liftM fromProb (beta 2 1))]))]
                -- , "culpepper" ~: testL (const culpepper)
                --                   [(unit, 0, Any
                --                     (superpose [(fromRational (1/8), dirac true)
                --                                ,(fromRational (1/8), dirac false)]))]
                -- , "density1" ~: testL density1 []
                -- , "density2" ~: testL density2 []
                -- , "density3" ~: testL density3 []
                -- , "t0"  ~: testL t0 []
                -- , "t1"  ~: testL t1 []
                -- , "t2"  ~: testL t2 []
                -- , "t3"  ~: testL t3 []
                -- , "t4"  ~: testL t4 []
                -- , "t5"  ~: testL t5 []
                -- , "t6"  ~: testL t6 []
                -- , "t7"  ~: testL t7 []
                -- , "t8"  ~: testL t8 []
                -- , "t9"  ~: testL t9 []
                -- , "t10" ~: testL t10 []
                ]

zeroDiv :: (Mochastic repr) => Cond repr () (Measure (Real,Real))
zeroDiv = \u -> ununit u $
          normal 0 1 `bind` \x ->
          -- normal x (0 / 2) `bind` \y ->
          dirac (pair x (0 / x))

zeroPlusFst :: (Mochastic repr) => Cond repr () (Measure (Int,Int))
zeroPlusFst = \u -> ununit u $
              counting `bind` \x ->
              dirac (pair (0+x) 3)

zeroPlusSnd :: (Mochastic repr) => Cond repr () (Measure ((),Real))
zeroPlusSnd = \u -> ununit u $
              normal 0 1 `bind` \x ->
              dirac (pair unit (0 + x))

-- Jacques on 2014-11-18: "From an email of Oleg's, could someone please
-- translate the following 3 programs into new Hakaru?"  The 3 programs below
-- are equivalent.
prog1s, prog2s, prog3s :: (Mochastic repr) =>
                          Cond repr () (Measure (Real, Bool))
prog1s = \u -> ununit u $
         bern 0.5 `bind` \c ->
         if_ c (normal 0 1)
               (uniform 10 20) `bind` \x ->
         dirac (pair x c)
prog2s = \u -> ununit u $
         bern 0.5 `bind` \c ->
         if_ c (normal 0 1)
               (dirac 10 `bind` \d ->
                uniform d 20) `bind` \x ->
         dirac (pair x c)
prog3s = \u -> ununit u $
         bern 0.5 `bind` \c ->
         if_ c (normal 0 1)
               (dirac false `bind` \e ->
                uniform (10 + if_ e 1 0) 20) `bind` \x ->
         dirac (pair x c)               

pair1fst :: (Mochastic repr) => Cond repr () (Measure (Bool, Prob))
pair1fst = \u -> ununit u $
           beta 1 1 `bind` \bias ->
           bern bias `bind` \coin ->
           dirac (pair coin bias)

pair1fstSwap :: (Mochastic repr) => Cond repr () (Measure (Prob, Bool))
pair1fstSwap = \u -> ununit u $
               liftM swap_ $
               beta 1 1 `bind` \bias ->
               bern bias `bind` \coin ->
               dirac (pair coin bias)

borelishSub :: (Mochastic repr) => Cond repr () (Measure (Real,Real))
borelishSub = const (borelish (-))

borelishDiv :: (Mochastic repr) => Cond repr () (Measure (Real,Real))
borelishDiv = const (borelish (/))

borelish :: (Mochastic repr) =>
            (repr Real -> repr Real -> repr a) -> repr (Measure (a, Real))
borelish compare =
    uniform 0 1 `bind` \x ->
    uniform 0 1 `bind` \y ->
    dirac (pair (compare x y) x)

culpepper :: (Mochastic repr) => repr (Measure (Real, Bool))
culpepper = bern 0.5 `bind` \a ->
            if_ a (uniform (-2) 2) (liftM (2*) (uniform (-1) 1)) `bind` \b ->
            dirac (pair b a)

density1 :: (Mochastic repr) => Cond repr () (Measure (Real,()))
density1 = \u -> ununit u $
           liftM (`pair` unit) $
           uniform 0 1 `bind` \x ->
           uniform 0 1 `bind` \y ->
           dirac (x + exp (-y))

density2 :: (Mochastic repr) => Cond repr () (Measure (Real,()))
density2 = \u -> ununit u $
           liftM (`pair` unit) $
           liftM2 (*) (uniform 0 1) $
           liftM2 (+) (uniform 0 1) (uniform 0 1)

-- density3 :: (Mochastic repr) => Cond repr () (Measure (Real,()))
-- density3 = \u -> ununit u $
--            liftM (`pair` unit) $
--            mix [(7, liftM (\x -> x - 1/2 + 0) (uniform 0 1)),
--                 (3, liftM (\x -> (x - 1/2) * 10) (uniform 0 1))]
                 
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

