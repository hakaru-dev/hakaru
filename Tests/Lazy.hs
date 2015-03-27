{-# LANGUAGE Rank2Types, ImpredicativeTypes #-}

module Tests.Lazy where

import Prelude hiding (Real)

import Language.Hakaru.Lazy
import Language.Hakaru.Any (Any(unAny), Any')
import Language.Hakaru.Syntax (Real, Prob, Measure, Vector,
       Number, Fraction(..), EqType(Refl), Order(..), Base(..),
       Mochastic(..), weight, equal_, Lambda(..), Lub(..))
import Language.Hakaru.Compose
import Language.Hakaru.PrettyPrint (PrettyPrint, runPrettyPrint, leftMode)    
import Tests.TestTools

import Data.Typeable (Typeable)    
import Test.HUnit

-- allTests :: Test
-- allTests = test ["t1" ~: t1]

t1 = assertEqual "" 3 4

condT :: (Backward a a, Typeable a, Typeable b) =>
         (forall s t. Lazy s (Compose [] t PrettyPrint) (Measure (a, b)))
      -> IO [Any (a -> Measure (a, b))]
condT = mapM convert . try
    where convert t = (recover t)

-- cond' :: [Any (a -> Measure (a, b))] -> IO [Any' (a -> Measure (a, b))]
-- cond' ls = return $ map unAny ls

    -- mapM (unAny . recover) . try

atLeastOne :: (Eq (repr a)) => repr a -> [repr a] -> Assertion
atLeastOne t ts' = assertBool "no correct disintegration" $
                   or (map ((==) t) ts')

-- assertEach :: [Any' a] -> [Any' a] -> Assertion
-- assertEach ts ts' = 
                 
-- t1 :: repr (Measure (Real,Real))
-- t1 = try (normal 0 1 `bind` \x ->
--           normal x 1 `bind` \y ->
--           dirac (pair y x))

-- main :: IO ()
-- main = runTestTT allTests >> return ()
