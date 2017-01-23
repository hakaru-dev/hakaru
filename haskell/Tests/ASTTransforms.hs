{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE EmptyCase                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}

module Tests.ASTTransforms (allTests) where

import           Prelude                          hiding (product, (*), (+), (-), (==))
import           Language.Hakaru.Syntax.ANF       (normalize)
import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.AST.Eq    (alphaEq)
import           Language.Hakaru.Syntax.Datum
import           Language.Hakaru.Syntax.DatumCase
import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Syntax.Prelude
import           Language.Hakaru.Syntax.Variable
import           Language.Hakaru.Types.Coercion
import           Language.Hakaru.Types.DataKind
import           Language.Hakaru.Types.HClasses
import           Language.Hakaru.Types.Sing
import           Test.HUnit
import           Tests.TestTools

allTests :: Test
allTests = test [ "example1" ~: testExample1
                , "example2" ~: testExample2
                , "example3" ~: testExample3
                ]

example1 :: TrivialABT Term '[] 'HReal
example1 = if_ (real_ 1 == real_ 2)
               (real_ 2 + real_ 3)
               (real_ 3 + real_ 4)

example1' :: TrivialABT Term '[] 'HReal
example1' = let_ (real_ 1 == real_ 2) $ \v ->
            if_ v (real_ 2 + real_ 3)
                  (real_ 3 + real_ 4)

example2 :: TrivialABT Term '[] 'HNat
example2 = let_ (nat_ 1) $ \ a -> triv ((summate a (a + (nat_ 10)) (\i -> i)) +
                                        (product a (a + (nat_ 10)) (\i -> i)))

example2' :: TrivialABT Term '[] 'HNat
example2' = let_ (nat_ 1) $ \ x4 ->
            let_ (x4 + nat_ 10) $ \ x3 ->
            let_ (summate x4 x3 (\ x0 -> x0)) $ \ x2 ->
            let_ (x4 + nat_ 10) $ \ x1 ->
            let_ (product x4 x1 (\ x0 -> x0)) $ \ x0 ->
            x2 + x0

example3 :: TrivialABT Term '[] 'HReal
example3 = triv (real_ 1 * (real_ 2 + real_ 3) * (real_ 4 + (real_ 5 + (real_ 6 * real_ 7))))


example3' :: TrivialABT Term '[] 'HReal
example3' = let_ (real_ 2 + real_ 3) $ \ x2 ->
            let_ (real_ 6 * real_ 7) $ \ x1 ->
            let_ (real_ 4 + real_ 5 + x1) $ \ x0 ->
            real_ 1 * x2 * x0

testNormalizer :: (ABT Term abt) => String -> abt '[] a -> abt '[] a -> Assertion
testNormalizer name a b = assertBool name (alphaEq (normalize a) b)

testExample1 = testNormalizer "example1" example1 example1'
testExample2 = testNormalizer "example2" example2 example2'
testExample3 = testNormalizer "example3" example3 example3'
