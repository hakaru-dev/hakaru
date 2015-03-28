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
import Language.Hakaru.Simplify (Simplifiable, closeLoop, simplify)
import Tests.TestTools

import Data.Typeable (Typeable)    
import Test.HUnit
import Control.Monad ((>=>))
import Data.Function (on)
import Data.List (elem)    

condSimp :: (Backward a a, Typeable a, Typeable b,
             Simplifiable a, Simplifiable b, Simplifiable env) =>
            (forall s t.
             LazyCompose s t PrettyPrint env
             -> LazyCompose s t PrettyPrint (Measure (a,b)))
         -> IO [Any (env -> (a -> Measure (a, b)))]
condSimp = mapM (recover >=> simp) . try

exists :: PrettyPrint a -> [PrettyPrint a] -> Assertion
exists t ts' = assertBool "no correct disintegration" $
               elem (result t) (map result ts')
                 
t1 :: (Mochastic repr) => repr (Measure (Real,Real))
t1 = normal 0 1 `bind` \x ->
     normal x 1 `bind` \y ->
     dirac (pair y x)
