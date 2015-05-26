{-# LANGUAGE TypeFamilies, Rank2Types, ImpredicativeTypes #-}

module Tests.Lazy where

import Prelude hiding (Real)

import Language.Hakaru.Lazy
import Language.Hakaru.Any (Any(Any, unAny))
import Language.Hakaru.Syntax (Real, Prob, Measure, Base(..),
                               ununit, max_, liftM, liftM2, bind_,
                               swap_, bern, fst_,
                               Mochastic(..), Lambda(..), Integrate(..),
                               Order_(..))
import Language.Hakaru.PrettyPrint (PrettyPrint, runPrettyPrint, leftMode)
import Language.Hakaru.Simplify (Simplifiable, closeLoop, simplify)
import Language.Hakaru.Expect (Expect(Expect), Expect', normalize)
import Language.Hakaru.Maple (Maple)
import Language.Hakaru.Inference
import Tests.TestTools
import qualified Tests.Models as RT
import qualified Examples.EasierRoadmap as RM    

import Data.Typeable (Typeable)    
import Test.HUnit
import qualified Data.List as L

recover :: (Typeable a) => PrettyPrint a -> IO (Any a)
recover hakaru = closeLoop ("Any (" ++ leftMode (runPrettyPrint hakaru) ++ ")")

simp :: (Simplifiable a) => Any a -> IO (Any a)
simp = simplify . unAny

testS' :: (Simplifiable a) => Any a -> Assertion
testS' t = testS (unAny t)

testL :: (Backward a a, Typeable a, Typeable b,
         Simplifiable a, Simplifiable b, Simplifiable env) => 
         Cond PrettyPrint env (Measure (a,b))
      -> [(Maple env, Maple a, Any (Measure b))]
      -> Assertion
testL f slices = do
  ds <- mapM recover (runDisintegrate f)
  assertResult ds
  mapM_ testS' ds
  mapM_ (\(env,a,t') ->
         testSS [(app (app (unAny d) env) a) | d <- ds] (unAny t')) slices
         
exists :: PrettyPrint a -> [PrettyPrint a] -> Assertion
exists t ts' = assertBool "no correct disintegration" $
               elem (result t) (map result ts')

runDisintegratePretty :: (Backward a a) =>
                         Cond PrettyPrint env (Measure (a,b)) -> IO ()
runDisintegratePretty = print . map runPrettyPrint . runDisintegrate

nonDefault :: (Backward a a) => String
           -> Cond PrettyPrint env (Measure (a,b)) -> Assertion
nonDefault s = assertBool "not calling non-default implementation" . any id .
               map (L.isInfixOf s . leftMode . runPrettyPrint) . runDisintegrate

justRun :: Test -> IO ()
justRun t = runTestTT t >> return ()
                   
main :: IO ()
main = -- justRun nonDefaultTests
       runDisintegratePretty prog1s

-- | TODO: understand why the following fail to use non-default uniform
-- prog1s, prog2s, prog3s, (const culpepper), t3, t4, t9, marsaglia
nonDefaultTests :: Test
nonDefaultTests = test [ nonDefault "uniform" borelishSub
                       , nonDefault "uniform" borelishDiv
                       , nonDefault "uniform" density1
                       , nonDefault "uniform" density2
                       , nonDefault "uniform" t1
                       , nonDefault "uniform" t2
                       , nonDefault "uniform" t5
                       , nonDefault "uniform" t6
                       , nonDefault "uniform" t7
                       , nonDefault "uniform" t8
                       ]

-- 2015-04-09
--------------------------------------------------------------------------------
important :: Test
important = test [ "zeroAddInt" ~: testL zeroAddInt [(unit, 0, Any $ dirac 3)]
                 , "zeroAddReal" ~: testL zeroAddReal [(unit, 0, Any $ dirac 3)]
                 , "easierRoadmapProg1" ~: testL easierRoadmapProg1 []
                 ]
--------------------------------------------------------------------------------
            
allTests :: Test
allTests = test [ "easierRoadmapProg1" ~: testL easierRoadmapProg1 []
                , "normalFB1" ~: testL normalFB1 []
                , "normalFB2" ~: testL normalFB2 []
                , "zeroDiv" ~: testL zeroDiv [(unit, 0, Any $ dirac 0)]
                , "zeroAddInt" ~: testL zeroAddInt [(unit, 0, Any $ dirac 3)]
                , "zeroPlusSnd" ~: testL zeroPlusSnd []
                , "prog1s" ~: testL prog1s []
                , "prog2s" ~: testL prog2s []
                , "prog3s" ~: testL prog3s []
                , "pair1fst" ~: testL pair1fst []
                , "pair1fstSwap" ~: testL pair1fstSwap []
                , "borelishSub" ~: testL borelishSub
                                    [(unit, 0, Any (uniform 0 1))]
                , "borelishDiv" ~: testL borelishDiv
                                    [(unit, 1, Any
                                      (superpose [(1/2, liftM fromProb (beta 2 1))]))]
                , "culpepper" ~: testL (const culpepper)
                                  [(unit, 0, Any
                                    (superpose [(fromRational (1/8), dirac true)
                                               ,(fromRational (1/8), dirac false)]))]
                , "beta" ~: testL testBetaConj
                              [(unit, true, Any
                                (superpose [(fromRational (1/2), beta 2 1)]))]
                , "betaNorm" ~: testSS [testBetaConjNorm] (beta 2 1)
                , "testGibbsPropUnif" ~: testS testGibbsPropUnif
                , "testGibbs0" ~: testSS [testGibbsProp0]
                                   (lam $ \x ->
                                    normal (x * fromRational (1/2))
                                           (sqrt_ 2 * fromRational (1/2)))
                , "testGibbs1" ~: testSS [testGibbsProp1]
                                   (lam $ \x ->
                                    normal (fst_ x) 1 `bind` \y ->
                                    dirac (pair (fst_ x) y))
                -- , "testGibbs2" ~: testSS [testGibbsProp2]
                --                    (lam $ \x ->
                --                     normal ((snd_ x) * fromRational (1/2))
                --                            (sqrt_ 2 * fromRational (1/2))
                --                            `bind` \y ->
                --                     dirac (pair y (snd_ x)))
                , "density1" ~: testL density1 []
                , "density2" ~: testL density2 []
                -- , "density3" ~: testL density3 []
                , "t0"  ~: testL t0
                            [(unit, 1, Any
                              (superpose 
                               [( recip (sqrt_ pi_) *
                                  exp_ (1 * 1 * fromRational (-1/4)) *
                                  fromRational (1/2)
                                , normal
                                  (1 * fromRational (1/2))
                                  ((sqrt_ 2) * fromRational (1/2)) )]))]
                , "t1"  ~: testL t1 []
                , "t2"  ~: testL t2 []
                , "t3"  ~: testL t3 []
                , "t4"  ~: testL t4 []
                , "t5"  ~: testL t5 []
                , "t6"  ~: testL t6 []
                , "t7"  ~: testL t7 []
                , "t8"  ~: testL t8 []
                , "t9"  ~: testL t9 []
                , "t10" ~: testL t10 []
                , "marsaglia" ~: testL marsaglia [] -- needs heavy disintegration
                ]

normalFB1 :: (Mochastic repr) => Cond repr () (Measure (Real, ()))
normalFB1 = \u -> ununit u $
            normal 0 1 `bind` \x ->
            normal x 1 `bind` \y ->
            dirac (pair ((y + y) + x) unit)

normalFB2 :: (Mochastic repr) => Cond repr () (Measure (Real, ()))
normalFB2 = \u -> ununit u $
            normal 0 1 `bind` \x ->
            normal x 1 `bind` \y ->
            dirac (pair (y + x) unit)

easierRoadmapProg1 :: (Mochastic repr) =>
                      Cond repr () (Measure ((Real, Real), (Prob, Prob)))
easierRoadmapProg1 = \u -> ununit u $ RM.easierRoadmapProg1

zeroDiv :: (Mochastic repr) => Cond repr () (Measure (Real,Real))
zeroDiv = \u -> ununit u $
          normal 0 1 `bind` \x ->
          dirac (pair x (0 / x))

zeroAddInt :: (Mochastic repr) => Cond repr () (Measure (Int,Int))
zeroAddInt = \u -> ununit u $
             counting `bind` \x ->
             dirac (pair (0+x) 3)

zeroAddReal :: (Mochastic repr) => Cond repr () (Measure (Real,Real))
zeroAddReal = \u -> ununit u $
              lebesgue `bind` \x ->
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
borelish comp =
    uniform 0 1 `bind` \x ->
    uniform 0 1 `bind` \y ->
    dirac (pair (comp x y) x)

culpepper :: (Mochastic repr) => repr (Measure (Real, Bool))
culpepper = bern 0.5 `bind` \a ->
            if_ a (uniform (-2) 2) (liftM (2*) (uniform (-1) 1)) `bind` \b ->
            dirac (pair b a)

-- | testBetaConj is like RT.t4, but we condition on the coin coming up true,
-- so a different sampling procedure for the bias is called for.
testBetaConj :: (Mochastic repr) => Cond repr () (Measure (Bool, Prob))
testBetaConj = \u -> ununit u $ liftM swap_ RT.t4

-- | This is a test of normalizing post disintegration
testBetaConjNorm :: (Mochastic repr, Integrate repr, Lambda repr) =>
                    repr (Measure Prob)
testBetaConjNorm = normalize (app (app d unit) true)
  where d:_ = runDisintegrate testBetaConj

testGibbsPropUnif :: (Lambda repr, Mochastic repr, Integrate repr) =>
                     repr (Real -> Measure Real)
testGibbsPropUnif = lam $ \x -> normalize (app (app d unit) (Expect x))
  where d:_ = runDisintegrate (const (liftM swap_ RT.unif2))

testGibbsProp0 :: (Lambda repr, Mochastic repr, Integrate repr) =>
                  repr (Real -> Measure Real)
testGibbsProp0 = lam $ \x -> normalize (app (app d unit) (Expect x))
  where d:_ = runDisintegrate t0

testGibbsProp1 :: (Lambda repr, Mochastic repr, Integrate repr) =>
                  repr ((Real, Real) -> Measure (Real, Real))
testGibbsProp1 = lam (gibbsProposal norm)

onSnd :: (Mochastic repr, Mochastic repr1, Lambda repr) =>
               (repr1 (Measure (b1, a1))
                -> repr (b2, a2) -> repr (Measure (a, b)))
               -> repr1 (Measure (a1, b1)) -> repr ((a2, b2) -> Measure (b, a))
onSnd tr f = lam (liftM swap_ . tr (liftM swap_ f) . swap_)

-- testGibbsProp2 :: (Lambda repr, Mochastic repr, Integrate repr) =>
--                   repr ((Real, Real) -> Measure (Real, Real))
-- testGibbsProp2 = lam (liftM swap_ . gibbsProposal (liftM swap_ norm) . swap_)
-- testGibbsProp2 = onSnd gibbsProposal norm

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

norm :: (Mochastic repr) => Cond repr () (Measure (Real, Real))
norm = \u -> ununit u $ RT.norm
                 
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

marsaglia :: (Mochastic repr) => repr () -> repr (Measure (Real,()))
marsaglia _ =
  uniform (-1) 1 `bind` \x ->
  uniform (-1) 1 `bind` \y ->
  let s = x ** 2 + y ** 2 in
  if_ (s `less_` 1)
      (dirac (pair (x * sqrt (-2 * log s / s)) unit))
      (superpose [])

-- | Show that uniform should not always evaluate its arguments
-- Here disintegrate goes forward on x before going backward on x,
-- causing the non-default implementation of uniform
-- (which evaluates the lower bound x) to fail
t11 :: (Mochastic repr) => Cond repr () (Measure (Real, ()))
t11 = \u -> ununit u $
      uniform 0 1 `bind` \x ->
      uniform x 1 `bind` \y ->
      dirac (pair (x + (y + y)) unit)
