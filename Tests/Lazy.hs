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

type LazyCompose s t repr a = Lazy s (Compose [] t repr) a

try :: (Mochastic repr, Lambda repr, Backward a a) =>
       (forall s t.
        LazyCompose s t repr env -> LazyCompose s t repr (Measure (a,b)))
    -> [repr (env -> (a -> Measure (a, b)))]
try m = runCompose
      $ lam $ \env ->
      lam $ \t -> runLazy
      -- $ liftM snd_
      $ disintegrate (pair (scalar0 t) unit) (m (scalar0 env))

recover :: (Typeable a) => PrettyPrint a -> IO (Any a)
recover hakaru = closeLoop ("Any (" ++ leftMode (runPrettyPrint hakaru) ++ ")")

simp :: (Simplifiable a) => Any a -> IO (Any a)
simp = simplify . unAny

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

-- main :: IO ()
-- main = do
--   let test1 = try (normal 0 1 `bind` \x ->
--                    normal x 1 `bind` \y ->
--                    dirac (pair y x))
--       test2 = try (normal 0 1 `bind` \x ->
--                    plate (vector 10 (\i -> normal x (unsafeProb (fromInt i) + 1))) `bind` \ys ->
-- 		   dirac (pair (pair (index ys 3) (index ys 4)) x))
--   return                  test1 >>= print . pretty
--   mapM (recover >=> simp) test1 >>= print . pretty
--   return                  test2 >>= print . pretty
--   return                  test2 >>= writeFile "/tmp/test2.hk" . show . pretty
