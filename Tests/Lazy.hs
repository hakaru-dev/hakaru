{-# LANGUAGE TypeFamilies, Rank2Types, ImpredicativeTypes, DataKinds #-}

module Tests.Lazy where

import Prelude hiding (Real)

import Language.Hakaru.Lazy
import Language.Hakaru.Any (Any(Any, unAny))
import Language.Hakaru.Syntax (Hakaru(..), Base(..),
                               ununit, max_, liftM, liftM2, bind_,
                               swap_, bern, fst_, not_, equal_, weight,
                               Mochastic(..), Lambda(..), Integrate(..),
                               Order_(..))
import Language.Hakaru.PrettyPrint (PrettyPrint, runPrettyPrint, leftMode)
import Language.Hakaru.Simplify (Simplifiable, closeLoop, simplify)
import Language.Hakaru.Expect (Expect(Expect), Expect', normalize, total)
import Language.Hakaru.Maple (Maple)
import Language.Hakaru.Inference
import Tests.TestTools
import qualified Tests.Models as RT
import qualified Examples.EasierRoadmap as RM

import Data.Typeable (Typeable)    
import Test.HUnit
import qualified Data.List as L

import Text.PrettyPrint    

recover :: (Typeable a) => PrettyPrint a -> IO (Any a)
recover hakaru = closeLoop ("Any (" ++ leftMode (runPrettyPrint hakaru) ++ ")")

simp :: (Simplifiable a) => Any a -> IO (Any a)
simp = simplify . unAny

testS' :: (Simplifiable a) => Any a -> Assertion
testS' t = testS (unAny t)

testL
    :: (Backward a a, Typeable a, Typeable b,
        Simplifiable a, Simplifiable b, Simplifiable env)
    => Cond PrettyPrint env (HMeasure (HPair a b))
    -> [(Maple env, Maple a, Any (HMeasure b))]
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

disp = print . map runPrettyPrint

runExpect :: (Lambda repr, Base repr) =>
              Expect repr (HMeasure HProb) -> repr HProb
runExpect (Expect m) = unpair m (\ m1 m2 -> m2 `app` lam id)

nonDefault
    :: (Backward a a)
    => String
    -> Cond PrettyPrint env (HMeasure (HPair a b))
    -> Assertion
nonDefault s = assertBool "not calling non-default implementation" . any id .
               map (L.isInfixOf s . leftMode . runPrettyPrint) . runDisintegrate

justRun :: Test -> IO ()
justRun t = runTestTT t >> return ()
                   
main :: IO ()
main = -- justRun nonDefaultTests
       disp (runDisintegrate burgalarm)

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
                       , nonDefault "sqrt_"   fwdSqrt_
                       , nonDefault "sqrt"    fwdSqrt
                       , nonDefault "**"      fwdPow
                       , nonDefault "pow_"    fwdPow_
                       , nonDefault "logBase" fwdLogBase
                       ]

-- 2015-04-09
--------------------------------------------------------------------------------
important :: Test
important = test
    [ "zeroAddInt" ~: testL zeroAddInt [(unit, 0, Any $ dirac 3)]
    , "zeroAddReal" ~: testL zeroAddReal [(unit, 0, Any $ dirac 3)]
    , "easierRoadmapProg1" ~: testL easierRoadmapProg1 []
    ]
--------------------------------------------------------------------------------
            
allTests :: Test
allTests = test
    [ "easierRoadmapProg1" ~: testL easierRoadmapProg1 []
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
    , "borelishSub" ~: testL borelishSub [(unit, 0, Any (uniform 0 1))]
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

burgalarm
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HBool HBool))
burgalarm = \u -> ununit u $
            bern 0.0001 `bind` \burglary ->
            bern (if_ burglary 0.95 0.01) `bind` \alarm ->
            dirac (pair alarm burglary)

burgRaw = disp (runDisintegrate burgalarm)

burgSimpl = mapM simplify $ runDisintegrate burgalarm

burgObs b = simplify (d `app` unit `app` b)
    where d:_ = runDisintegrate burgalarm

normalFB1
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HReal HUnit))
normalFB1 = \u -> ununit u $
            normal 0 1 `bind` \x ->
            normal x 1 `bind` \y ->
            dirac (pair ((y + y) + x) unit)

normalFB2
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HReal HUnit))
normalFB2 = \u -> ununit u $
            normal 0 1 `bind` \x ->
            normal x 1 `bind` \y ->
            dirac (pair (y + x) unit)

easierRoadmapProg1
    :: (Mochastic repr)
    => Cond repr HUnit
        (HMeasure (HPair (HPair HReal HReal) (HPair HProb HProb)))
easierRoadmapProg1 = \u -> ununit u $ RM.easierRoadmapProg1

zeroDiv
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HReal HReal))
zeroDiv = \u -> ununit u $
          normal 0 1 `bind` \x ->
          dirac (pair x (0 / x))
            
cushing :: (Mochastic repr) => Cond repr HUnit (HMeasure (HPair HReal HReal))
cushing = \u -> ununit u $
          uniform 0 1 `bind` \x ->
          if_ (not_ (equal_ x (1/2)))
              (uniform 0 x)
              (uniform x 1) `bind` \y ->
          dirac (pair y x)

cushingObs n = simplify (d `app` unit `app` n)
    where d:_ = runDisintegrate cushing

cushingSimpl = mapM simplify (runDisintegrate cushing)

cobb :: (Mochastic repr) => Cond repr HUnit (HMeasure (HPair HReal HReal))
cobb = \u -> ununit u $
       uniform 0 1 `bind` \x ->
       uniform (-x) x `bind` \y ->
       dirac (pair y x)

cobbSimpl = mapM simplify (runDisintegrate cobb)
             
cobbObs n = simplify (d `app` unit `app` n)
    where d:_ = runDisintegrate cobb

cobb0 :: (Mochastic repr, Lambda repr, Integrate repr)
         => Expect repr (HMeasure HProb)
cobb0 = uniform 0 1 `bind` \x0 ->
        weight (recip (unsafeProb x0) * (1/2)) $
        dirac (unsafeProb x0)

expectCobb0 :: Doc
expectCobb0 = runPrettyPrint (runExpect cobb0)

totalCobb0 :: Doc
totalCobb0 = runPrettyPrint (total cobb0)

thenSimpl1 = simplify $ dirac (total cobb0)
thenSimpl2 = simplify $ dirac (runExpect cobb0)
thenSimpl3 = simplify $ normalize cobb0
                          
zeroAddInt
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HInt HInt))
zeroAddInt = \u -> ununit u $
             counting `bind` \x ->
             dirac (pair (0+x) 3)

zeroAddReal
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HReal HReal))
zeroAddReal = \u -> ununit u $
              lebesgue `bind` \x ->
              dirac (pair (0+x) 3)                    

zeroPlusSnd
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HUnit HReal))
zeroPlusSnd = \u -> ununit u $
              normal 0 1 `bind` \x ->
              dirac (pair unit (0 + x))                   

-- Jacques on 2014-11-18: "From an email of Oleg's, could someone please
-- translate the following 3 programs into new Hakaru?"  The 3 programs below
-- are equivalent.
prog1s, prog2s, prog3s
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HReal HBool))
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

pair1fst
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HBool HProb))
pair1fst = \u -> ununit u $
           beta 1 1 `bind` \bias ->
           bern bias `bind` \coin ->
           dirac (pair coin bias)

pair1fstSwap
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HProb HBool))
pair1fstSwap = \u -> ununit u $
               liftM swap_ $
               beta 1 1 `bind` \bias ->
               bern bias `bind` \coin ->
               dirac (pair coin bias)

borelishSub
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HReal HReal))
borelishSub = const (borelish (-))

borelishDiv
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HReal HReal))
borelishDiv = const (borelish (/))

borelish
    :: (Mochastic repr)
    => (repr HReal -> repr HReal -> repr a)
    -> repr (HMeasure (HPair a HReal))
borelish comp =
    uniform 0 1 `bind` \x ->
    uniform 0 1 `bind` \y ->
    dirac (pair (comp x y) x)

culpepper :: (Mochastic repr) => repr (HMeasure (HPair HReal HBool))
culpepper = bern 0.5 `bind` \a ->
            if_ a (uniform (-2) 2) (liftM (2*) (uniform (-1) 1)) `bind` \b ->
            dirac (pair b a)

-- | testBetaConj is like RT.t4, but we condition on the coin coming up true,
-- so a different sampling procedure for the bias is called for.
testBetaConj
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HBool HProb))
testBetaConj = \u -> ununit u $ liftM swap_ RT.t4

-- | This is a test of normalizing post disintegration
testBetaConjNorm
    :: (Mochastic repr, Integrate repr, Lambda repr)
    => repr (HMeasure HProb)
testBetaConjNorm = normalize (app (app d unit) true)
  where d:_ = runDisintegrate testBetaConj

testGibbsPropUnif
    :: (Lambda repr, Mochastic repr, Integrate repr)
    => repr (HFun HReal (HMeasure HReal))
testGibbsPropUnif = lam $ \x -> normalize (app (app d unit) (Expect x))
  where d:_ = runDisintegrate (const (liftM swap_ RT.unif2))

testGibbsProp0
    :: (Lambda repr, Mochastic repr, Integrate repr)
    => repr (HFun HReal (HMeasure HReal))
testGibbsProp0 = lam $ \x -> normalize (app (app d unit) (Expect x))
  where d:_ = runDisintegrate t0

testGibbsProp1
    :: (Lambda repr, Mochastic repr, Integrate repr)
    => repr (HFun (HPair HReal HReal) (HMeasure (HPair HReal HReal)))
testGibbsProp1 = lam (gibbsProposal norm)

onSnd
    :: (Mochastic repr, Mochastic repr1, Lambda repr)
    => (repr1 (HMeasure (HPair b1 a1))
        -> repr (HPair b2 a2)
        -> repr (HMeasure (HPair a b)))
    -> repr1 (HMeasure (HPair a1 b1))
    -> repr (HFun (HPair a2 b2) (HMeasure (HPair b a)))
onSnd tr f = lam (liftM swap_ . tr (liftM swap_ f) . swap_)

-- testGibbsProp2
--     :: (Lambda repr, Mochastic repr, Integrate repr)
--     => repr (HFun (HPair HReal HReal) (HMeasure (HPair HReal HReal)))
-- testGibbsProp2 = lam (liftM swap_ . gibbsProposal (liftM swap_ norm) . swap_)
-- testGibbsProp2 = onSnd gibbsProposal norm

density1
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HReal HUnit))
density1 = \u -> ununit u $
           liftM (`pair` unit) $
           uniform 0 1 `bind` \x ->
           uniform 0 1 `bind` \y ->
           dirac (x + exp (-y))

density2
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HReal HUnit))
density2 = \u -> ununit u $
           liftM (`pair` unit) $
           liftM2 (*) (uniform 0 1) $
           liftM2 (+) (uniform 0 1) (uniform 0 1)

-- density3
--     :: (Mochastic repr)
--     => Cond repr HUnit (HMeasure (HPair HReal HUnit))
-- density3 = \u -> ununit u $
--            liftM (`pair` unit) $
--            mix [(7, liftM (\x -> x - 1/2 + 0) (uniform 0 1)),
--                 (3, liftM (\x -> (x - 1/2) * 10) (uniform 0 1))]

norm :: (Mochastic repr) => Cond repr HUnit (HMeasure (HPair HReal HReal))
norm = \u -> ununit u $ RT.norm
                 
t0 :: (Mochastic repr) => Cond repr HUnit (HMeasure (HPair HReal HReal))
t0 = \u -> ununit u $
     normal 0 1 `bind` \x ->
     normal x 1 `bind` \y ->
     dirac (pair y x)

t1 :: (Mochastic repr) => Cond repr HUnit (HMeasure (HPair HReal HReal))
t1 = \u -> ununit u $
     uniform 0 1 `bind` \x ->
     uniform 0 1 `bind` \y ->
     dirac (pair (exp x) (y + x))

t2 :: (Mochastic repr) => Cond repr HUnit (HMeasure (HPair HReal HReal))
t2 = \u -> ununit u $
     uniform 0 1 `bind` \x ->
     uniform 0 1 `bind` \y ->
     dirac (pair (y + x) (exp x))

t3  :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HReal (HPair HReal HReal)))
t3 = \u -> ununit u $
     uniform 0 1 `bind` \x ->
     uniform 0 1 `bind` \y ->
     dirac (pair (max_ x y) (pair x y))

t4 :: (Mochastic repr) => Cond repr HUnit (HMeasure (HPair HReal HReal))
t4 = \u -> ununit u $
     uniform 0 1 `bind` \x ->
     dirac (pair (exp x) (-x))

t5 :: (Mochastic repr) => Cond repr HUnit (HMeasure (HPair HReal HUnit))
t5 = \u -> ununit u $
     liftM (`pair` unit) $
     let m = superpose (replicate 2 (1, uniform 0 1))
     in let add = liftM2 (+)
        in add (add m m) m

t6 :: (Mochastic repr) => Cond repr HUnit (HMeasure (HPair HReal HReal))
t6 = \u -> ununit u $
     uniform 0 1 `bind` \x ->
     uniform 0 1 `bind` \y ->
     dirac (pair (x+y) (x-y))

t7  :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HReal (HMeasure HReal)))
t7 = \u -> ununit u $
     uniform 0 1 `bind` \y ->
     uniform 0 1 `bind` \x ->
     dirac (pair (x+y) (uniform 0 1 `bind_` dirac y))

t8 :: (Mochastic repr) => Cond repr HUnit (HMeasure (HPair HReal HReal))
t8 = \u -> ununit u $
     dirac (uniform 0 1 `bind` \x -> dirac (1+x)) `bind` \m ->
     m `bind` \x ->
     m `bind` \y ->
     dirac (pair x y)

t9 :: (Mochastic repr) => Cond repr HUnit (HMeasure (HPair HReal HReal))
t9 = \u -> ununit u $
     (uniform 0 1 `bind` \x -> dirac (dirac (1+x))) `bind` \m ->
     m `bind` \x ->
     m `bind` \y ->
     dirac (pair x y)

t10 :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair (HPair HReal HReal) HReal))
t10 = \u -> ununit u $
      normal 0 1 `bind` \x ->
      plate (vector 10 (\i -> normal x (unsafeProb (fromInt i) + 1))) `bind` \ys ->
      dirac (pair (pair (index ys 3) (index ys 4)) x)

marsaglia
    :: (Mochastic repr)
    => repr HUnit
    -> repr (HMeasure (HPair HReal HUnit))
marsaglia _ =
  uniform (-1) 1 `bind` \x ->
  uniform (-1) 1 `bind` \y ->
  let s = x ** 2 + y ** 2 in
  if_ (s `less_` 1)
      (dirac (pair (x * sqrt (-2 * log s / s)) unit))
      (superpose [])

-- | Show that uniform should not always evaluate its arguments
-- Here disintegrate goes forward on x before going backward on x,
-- causing the failure of the non-default implementation of uniform
-- (which evaluates the lower bound x)
t11 :: (Mochastic repr) => Cond repr HUnit (HMeasure (HPair HReal HUnit))
t11 = \u -> ununit u $
      uniform 0 1 `bind` \x ->
      uniform x 1 `bind` \y ->
      dirac (pair (x + (y + y)) unit)

bwdSqrt_
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HProb HReal))
bwdSqrt_ = \u -> ununit u $
           uniform 0 10 `bind` \x ->
           dirac (pair (sqrt_ (unsafeProb x)) x)

fwdSqrt_
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HReal HProb))
fwdSqrt_ = \u -> ununit u $
           uniform 0 10 `bind` \x ->
           dirac (pair x (sqrt_ (unsafeProb x)))

bwdSqrt
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HReal HReal))
bwdSqrt = \u -> ununit u $
          uniform 0 10 `bind` \x ->
          dirac (pair (sqrt x) x)

fwdSqrt
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HReal HReal))
fwdSqrt = \u -> ununit u $
          uniform 0 10 `bind` \x ->
          dirac (pair x (sqrt x)) 

bwdLogBase
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HReal HUnit))
bwdLogBase = \u -> ununit u $
             uniform 2 4 `bind` \x ->
             uniform 5 7 `bind` \y ->
             dirac (pair (logBase x y) unit)

fwdLogBase
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HUnit HReal))
fwdLogBase = \u -> ununit u $
             uniform 2 4 `bind` \x ->
             uniform 5 7 `bind` \y ->
             dirac (pair unit (logBase x y))

bwdPow
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HReal HUnit))
bwdPow = \u -> ununit u $
         uniform 2 4 `bind` \x ->
         uniform 5 7 `bind` \y ->
         dirac (pair (x ** y) unit)

fwdPow
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HUnit HReal))
fwdPow = \u -> ununit u $
         uniform 2 4 `bind` \x ->
         uniform 5 7 `bind` \y ->
         dirac (pair unit (x ** y)) 
                   
bwdPow_
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HProb HUnit))
bwdPow_ = \u -> ununit u $
          uniform 2 4 `bind` \x ->
          uniform 5 7 `bind` \y ->
          dirac (pair (pow_ (unsafeProb x) y) unit)

fwdPow_
    :: (Mochastic repr)
    => Cond repr HUnit (HMeasure (HPair HUnit HProb))
fwdPow_ = \u -> ununit u $
          uniform 2 4 `bind` \x ->
          uniform 5 7 `bind` \y ->
          dirac (pair unit (pow_ (unsafeProb x) y))
