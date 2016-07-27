{-# LANGUAGE DataKinds
           , GADTs
           , TypeOperators
           , NoImplicitPrelude
           , FlexibleContexts
           #-}

module Tests.Disintegrate where

import           Prelude (($), (.), (++), head, String, Maybe(..))
import qualified Prelude
import qualified Data.List.NonEmpty  as L    

import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.Prelude
import Language.Hakaru.Syntax.IClasses (Some2(..), TypeEq(..), jmEq1)
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing
import Language.Hakaru.Pretty.Concrete
import Language.Hakaru.Syntax.TypeCheck
import Language.Hakaru.Evaluation.Types               (fromWhnf)
import Language.Hakaru.Evaluation.DisintegrationMonad (runDis)
import Language.Hakaru.Disintegrate

import Test.HUnit
import Tests.TestTools
import Tests.Models hiding (easyRoad)

----------------------------------------------------------------
----------------------------------------------------------------

-- | A very simple program. Is sufficient for testing escape and
-- capture of substitution.
norm0a :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
norm0a =
    normal (real_ 0) (prob_ 1) >>= \x ->
    normal x         (prob_ 1) >>= \y ->
    dirac (pair y x)

-- | A version of 'norm0' which adds a type annotation at the
-- top-level; useful for testing that using 'Ann_' doesn't cause
-- perform\/disintegrate to loop.
norm0b :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
norm0b = ann_ sing norm0a

-- | A version of 'norm0' which inserts an annotation around the
-- 'Datum' constructor itself. The goal here is to circumvent the
-- @typeOf_{Datum_}@ issue without needing to change the 'Datum'
-- type nor the 'typeOf' definition.
norm0c :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
norm0c =
    normal (real_ 0) (prob_ 1) >>= \x ->
    normal x         (prob_ 1) >>= \y ->
    dirac (ann_ sing $ pair y x)

-- | What we expect 'norm0a' (and variants) to disintegrate to.
norm0' :: TrivialABT Term '[] ('HReal ':-> 'HMeasure 'HReal)
norm0' =
    lam $ \y ->
    normal (real_ 0) (prob_ 1) >>= \x ->
    weight (densityNormal x (prob_ 1) y) >>
    dirac x

{-
-- Eliminating some redexes of 'norm0'', that is:
    lam $ \y ->
    normal (real_ 0) (prob_ 1) >>= \x ->
    withWeight
        (exp ((x - y) ^ nat_ 2 / real_ 2)
        / (nat_ 2 `thRootOf` (prob_ 2 * pi)))
    $ dirac x

-- N.B., calling 'evaluate' on 'norm0'' doesn't catch those redexes because they're not on the way to computing stuff. need to call 'constantPropagation' to get rid of them.
-}


testPerform0a, testPerform0b, testPerform0c
    :: [TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))]
testPerform0a = runPerform norm0a
testPerform0b = runPerform norm0b
testPerform0c = runPerform norm0c

testDisintegrate0a, testDisintegrate0b, testDisintegrate0c
    :: [TrivialABT Term '[] ('HReal ':-> 'HMeasure 'HReal)]
testDisintegrate0a = disintegrate norm0a
testDisintegrate0b = disintegrate norm0b
testDisintegrate0c = disintegrate norm0c

-- | The goal of this test is to be sure we maintain proper hygiene
-- for the weight component when disintegrating superpose. Moreover,
-- in earlier versions it used to throw VarEqTypeError due to
-- 'disintegrate' not choosing a sufficiently fresh variable name
-- for its lambda; thus this also serves as a regression test to
-- make sure we don't run into that problem again.
testHygiene0b :: [TrivialABT Term '[] ('HReal ':-> 'HMeasure 'HReal)]
testHygiene0b =
    disintegrate $
        let_ (prob_ 1) $ \x ->
        withWeight x norm0b

----------------------------------------------------------------
-- | This simple progam is to check for disintegrating case analysis
-- when the scrutinee contains a heap-bound variable.
norm1a :: TrivialABT Term '[] ('HMeasure (HPair 'HReal HUnit))
norm1a =
    normal (real_ 3) (prob_ 2) >>= \x ->
    dirac $ if_ (x < real_ 0)
        (ann_ sing $ pair (negate x) unit)
        (ann_ sing $ pair         x  unit)

norm1b :: TrivialABT Term '[] ('HMeasure (HPair 'HReal HUnit))
norm1b =
    normal (real_ 3) (prob_ 2) >>= \x ->
    if_ (x < real_ 0)
        (ann_ sing . dirac $ pair (negate x) unit)
        (ann_ sing . dirac $ pair         x  unit)

norm1c :: TrivialABT Term '[] ('HMeasure (HPair 'HReal HUnit))
norm1c =
    normal (real_ 3) (prob_ 2) >>= \x ->
    if_ (x < real_ 0)
        (dirac . ann_ sing $ pair (negate x) unit)
        (dirac . ann_ sing $ pair         x  unit)

norm1' :: TrivialABT Term '[] ('HReal ':-> 'HMeasure HUnit)
norm1' =
    lam $ \t -> superpose $
     L.fromList 
      [ (one,
         weight (densityNormal (real_ 3) (prob_ 2) (negate t)) >>= \_ ->
         let_ (negate t) $ \x ->
         case_ (x < zero) [branch pTrue (dirac unit)])
      , (one,
         weight (densityNormal (real_ 3) (prob_ 2) t) >>= \_ ->
         case_ (t < zero) [branch pFalse (dirac unit)]) ]

-- BUG: the first solutions returned by 'testPerform1b' and 'testPerform1c' break hygiene! They drops the variable bound by 'normal' and has all the uses of @x@ become free.
testPerform1a, testPerform1b, testPerform1c
    :: [TrivialABT Term '[] ('HMeasure (HPair 'HReal HUnit))]
testPerform1a = runPerform norm1a
testPerform1b = runPerform norm1b
testPerform1c = runPerform norm1c

testDisintegrate1a, testDisintegrate1b, testDisintegrate1c
    :: [TrivialABT Term '[] ('HReal ':-> 'HMeasure HUnit)]
testDisintegrate1a = disintegrate norm1a
testDisintegrate1b = disintegrate norm1b
testDisintegrate1c = disintegrate norm1c


----------------------------------------------------------------
norm2 :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
norm2 =
    normal (real_ 3) (prob_ 2) >>= \x ->
    normal (real_ 5) (prob_ 4) >>= \y ->
    dirac $ if_ (x < y)
        (pair y x)
        (pair x x)

norm2' :: TrivialABT Term '[] ('HReal ':-> 'HMeasure 'HReal)
norm2' =
    lam $ \t -> superpose $
     L.fromList
      [ (one,
         normal (real_ 3) (prob_ 2) >>= \x ->
         weight (densityNormal (real_ 5) (prob_ 4) t) >>= \_ ->
         case_ (x < t) [branch pTrue (dirac x)])
      , (one,
         weight (densityNormal (real_ 3) (prob_ 2) t) >>= \_ ->
         normal (real_ 5) (prob_ 4) >>= \y ->
         case_ (t < y) [branch pFalse (dirac t)]) ]   

testPerform2
    :: [TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))]
testPerform2 = runPerform norm2

testDisintegrate2
    :: [TrivialABT Term '[] ('HReal ':-> 'HMeasure 'HReal)]
testDisintegrate2 = disintegrate norm2

----------------------------------------------------------------
easyRoad
    :: TrivialABT Term '[]
        ('HMeasure (HPair (HPair 'HReal 'HReal) (HPair 'HProb 'HProb)))
easyRoad =
    uniform (real_ 3) (real_ 8) >>= \noiseT_ ->
    uniform (real_ 1) (real_ 4) >>= \noiseE_ ->
    let_ (unsafeProb noiseT_) $ \noiseT ->
    let_ (unsafeProb noiseE_) $ \noiseE ->
    normal (real_ 0) noiseT >>= \x1 ->
    normal x1 noiseE >>= \m1 ->
    normal x1 noiseT >>= \x2 ->
    normal x2 noiseE >>= \m2 ->
    dirac (pair (pair m1 m2) (pair noiseT noiseE))

easyRoad'
    :: TrivialABT Term '[]
        (HPair 'HReal 'HReal ':-> 'HMeasure (HPair 'HProb 'HProb))
easyRoad' =
    lam $ \t ->
    unpair t (\t1 t2 ->
              uniform (real_ 3) (real_ 8) >>= \noiseT_ ->
              uniform (real_ 1) (real_ 4) >>= \noiseE_ ->
              let_ (unsafeProb noiseT_) $ \noiseT ->
              let_ (unsafeProb noiseE_) $ \noiseE ->
              normal (real_ 0) noiseT >>= \x1 ->
              weight (densityNormal x1 noiseE t1) >>= \_ ->
              normal x1 noiseT >>= \x2 ->
              weight (densityNormal x2 noiseE t2) >>
              dirac (pair noiseT noiseE))
                                     
testPerformEasyRoad
    :: [TrivialABT Term '[]
        ('HMeasure (HPair (HPair 'HReal 'HReal) (HPair 'HProb 'HProb)))]
testPerformEasyRoad = runPerform easyRoad


testDisintegrateEasyRoad
    :: [TrivialABT Term '[]
        (HPair 'HReal 'HReal ':-> 'HMeasure (HPair 'HProb 'HProb))]
testDisintegrateEasyRoad = disintegrate easyRoad

----------------------------------------------------------------
helloWorld100
    :: TrivialABT Term '[] ('HMeasure (HPair ('HArray 'HReal) 'HReal))
helloWorld100 =
    normal (real_ 0) (prob_ 1) >>= \mu ->
    plate (nat_ 100) (\_ -> normal mu (prob_ 1)) >>= \v ->
    dirac (pair v mu)

helloWorld100'
    :: TrivialABT Term '[] ('HArray 'HReal ':-> 'HMeasure 'HReal)
helloWorld100' =
    lam $ \t ->
    normal (real_ 0) (prob_ 1) >>= \mu ->
    plate (nat_ 100)
          (\i -> weight (densityNormal mu (prob_ 1) (t ! i))) >>
    dirac mu

testHelloWorld100
    :: [TrivialABT Term '[] ('HArray 'HReal ':-> 'HMeasure 'HReal)]
testHelloWorld100 = disintegrate helloWorld100

----------------------------------------------------------------
copy1 :: TrivialABT Term '[] ('HMeasure (HPair ('HArray 'HReal) HUnit))
copy1 =
    plate n (\_ -> normal (real_ 0) (prob_ 1)) >>= \u ->
    dirac (array n (\i -> u ! i)) >>= \v ->
    dirac (pair v unit)
    where n = nat_ 100

copy1' :: TrivialABT Term '[] ('HArray 'HReal ':-> 'HMeasure HUnit)
copy1' =
    lam $ \t ->        
    plate (nat_ 100)
          (\i -> weight (densityNormal (real_ 0) (prob_ 1) (t ! i))) >>
    dirac unit

testCopy1 :: [TrivialABT Term '[] ('HArray 'HReal ':-> 'HMeasure HUnit)]
testCopy1 = disintegrate copy1

----------------------------------------------------------------
copy2 :: TrivialABT Term '[] ('HMeasure (HPair ('HArray 'HReal) HUnit))
copy2 =
    plate n (\_ -> normal (real_ 0) (prob_ 1)) >>= \u ->
    plate n (\j -> dirac (u ! j)) >>= \v ->
    dirac (pair v unit)
    where n = nat_ 100

testCopy2 :: [TrivialABT Term '[] ('HArray 'HReal ':-> 'HMeasure HUnit)]
testCopy2 = disintegrate copy2


----------------------------------------------------------------
sizeVocab, numLabels, numDocs, sizeEachDoc :: (ABT Term abt) => abt '[] 'HNat

sizeVocab   = nat_ 1000
numLabels   = nat_ 40
numDocs     = nat_ 200
sizeEachDoc = nat_ 5000

naiveBayes
    :: TrivialABT Term '[]
        ('HMeasure (HPair ('HArray ('HArray 'HNat)) ('HArray 'HNat)))
naiveBayes =
    plate numLabels (\_ -> dirichlet (array sizeVocab (\_ -> prob_ 1))) >>= \bs ->
    dirichlet (array numLabels (\_ -> prob_ 1)) >>= \ts ->
    plate numDocs (\_ -> categorical ts) >>= \zs ->
    plate numDocs (\i -> plate sizeEachDoc
                               (\_ -> categorical (bs ! (zs ! i)))) >>= \ds ->
    dirac (pair ds zs)

naiveBayes'
    :: TrivialABT Term '[] ('HArray ('HArray 'HNat) ':-> ('HMeasure ('HArray 'HNat)))
naiveBayes' =
    lam $ \t ->
    Prelude.error "TODO define naiveBayes'"

testNaiveBayes
    :: [TrivialABT Term '[] ('HArray ('HArray 'HNat) ':-> ('HMeasure ('HArray 'HNat)))]
testNaiveBayes = disintegrate naiveBayes
          
----------------------------------------------------------------
----------------------------------------------------------------
runPerform
    :: TrivialABT Term '[] ('HMeasure a)
    -> [TrivialABT Term '[] ('HMeasure a)]
runPerform e = runDis (fromWhnf `Prelude.fmap` perform e) [Some2 e]               

-- | Tests that disintegration doesn't error and produces at least
-- one solution.
testDis
    :: (ABT Term abt)
    => String
    -> abt '[] ('HMeasure (HPair a b))
    -> Assertion
testDis p =
    assertBool (p ++ ": no disintegration found")
    . Prelude.not
    . Prelude.null
    . disintegrate

showFirst :: TrivialABT Term '[] ('HMeasure (HPair a b)) -> Prelude.IO ()
showFirst e = let anss = disintegrate e
              in if Prelude.null anss
                 then Prelude.putStrLn $ "no disintegration found"
                 else Prelude.print    $ pretty (head anss)

-- TODO: put all the "perform" tests in here
allTests :: Test
allTests = test
    [ testDis "testDisintegrate0a" norm0a
    , testDis "testDisintegrate0b" norm0b
    , testDis "testDisintegrate0c" norm0c
    , assertAlphaEq "testDisintegrate0a" (head testDisintegrate0a) norm0'
    , assertAlphaEq "testDisintegrate0b" (head testDisintegrate0b) norm0'
    , assertAlphaEq "testDisintegrate0c" (head testDisintegrate0c) norm0'
    , assertBool "testHygiene0b" $ Prelude.not (Prelude.null testHygiene0b)
    , testDis "testDisintegrate1a" norm1a
    , testDis "testDisintegrate1b" norm1b
    , testDis "testDisintegrate1c" norm1c
    , assertAlphaEq "testDisintegrate1a" (head testDisintegrate1a) norm1'
    , assertAlphaEq "testDisintegrate1b" (head testDisintegrate1b) norm1'
    , assertAlphaEq "testDisintegrate1c" (head testDisintegrate1c) norm1'
    , testDis "testDisintegrate2" norm2
    , assertAlphaEq "testDisintegrate2" (head testDisintegrate2) norm2'
    , testWithConcrete' match_norm_unif LaxMode $ \_typ ast ->
        case jmEq1 _typ (SMeasure $ sPair SReal sBool) of
        Just Refl -> testDis "testMatchNormUnif" ast
        Nothing   -> assertFailure "BUG: jmEq1 got the wrong type"
    , testWithConcrete' dont_atomize_weights LaxMode $ \_typ ast ->
        case jmEq1 _typ (SMeasure $ sPair SReal sUnit) of
        Just Refl -> testDis "testAtomizeWeights" ast
        Nothing   -> assertFailure "BUG: jmEq1 got the wrong type"
    , assertBool "testPerformEasyRoad" $ Prelude.not (Prelude.null testPerformEasyRoad)
    , testDis "testDisintegrateEasyRoad" easyRoad
    , assertAlphaEq "testDisintegrateEasyRoad" (head testDisintegrateEasyRoad) easyRoad'
    , testDis "testHelloWorld100" helloWorld100
    , assertAlphaEq "testHelloWorld100" (head testHelloWorld100) helloWorld100'
    , testDis "testCopy1" copy1
    , assertAlphaEq "testCopy1" (head testCopy1) copy1'
    , testDis "testCopy2" copy2
    , assertAlphaEq "testCopy2" (head testCopy2) copy1'
    , testDis "testNaiveBayes" naiveBayes
    ]


----------------------------------------------------------------
----------------------------------------------------------- fin.
