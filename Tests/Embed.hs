{-# LANGUAGE TypeFamilies, Rank2Types, FlexibleContexts, DeriveGeneric, 
  TemplateHaskell, UndecidableInstances, ConstraintKinds, DeriveDataTypeable
  , ScopedTypeVariables, DataKinds #-}
{-# OPTIONS -W -ddump-splices #-}

module Tests.Embed (allTests) where

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Real, Prob, Measure,
       Order(..), Base(..), ununit, and_, fst_, snd_, swap_, min_,
       Mochastic(..), Lambda(..), Integrate(..), bind_, liftM, factor, beta, bern, lam)
import Language.Hakaru.Util.Pretty (Pretty (pretty), prettyPair)
import Language.Hakaru.Disintegrate hiding (Nil)

import Control.Monad (zipWithM_, replicateM)
import Control.Applicative (Const(Const))
import Text.PrettyPrint (text, (<>), ($$), nest)
import Data.Function(on)
import Language.Hakaru.Sample
import Language.Hakaru.Expect
import Language.Hakaru.Embed
import Language.Hakaru.Maple 
import Language.Hakaru.Simplify 
import Control.Exception
import Data.Typeable 
import Test.HUnit
import Tests.TestTools
import Language.Hakaru.Any (Any(unAny))

-- Variant of testSS for Embeddable a 
-- type TesteeEmbed a =
--   forall repr. (Mochastic repr, Integrate repr, Lambda repr, Embed repr) => repr a

-- testSE :: (Simplifiable a) => TesteeEmbed a -> Assertion
-- testSE t = do
--     p <- simplify t `catch` handleSimplify t
--     let s = result (unAny p)
--     assertResult (show s)

-- testSSE :: (Simplifiable a) => [Expect Maple a] -> TesteeEmbed a -> Assertion
-- testSSE ts t' =
--     mapM_ (\t -> do p <- simplify t --`catch` handleSimplify t
--                     (assertEqual "testSS" `on` result) t' (unAny p))
--           (t' : ts)


embeddable' [d| data BoolProb = BoolProb Bool Prob |] 

embeddable' [d| data Real5 = Real5 { r1, r2, r3, r4, r5 :: Real} |]

--  deriving (GHC.Generic, Typeable)
-- $(deriveEmbed ''BoolProb)

-- data P2 a b = P2 a b deriving (GHC.Generic, Typeable)
-- $(deriveEmbed ''P2)

-- fstP2 :: Embed repr => repr (P2 a b) -> repr a 
-- fstP2 x = case_ x (NFn (\a _ -> a) :* Nil)

-- sndP2 :: Embed repr => repr (P2 a b) -> repr b 
-- sndP2 x = case_ x (NFn (\_ a -> a) :* Nil)

-- p2 :: Embed repr => repr a -> repr b -> repr (P2 a b)
-- p2 a b = sop (Z $ a :* b :* Nil)

-- Test must come after Template Haskell splices

allTests :: Test
allTests = error "TODO: write tests" 
-- allTests = test 
--   [
--     "pair-elim" ~: testSSE [t1] (uniform 1 2)
--   -- , "P2-elim" ~: testSSE [t0] (uniform 1 2)  
--   ]

-- t0 :: forall repr . (Mochastic repr, Embed repr) => repr (Measure Real)
-- t0 = case_ (p2 1 2) (NFn uniform :* Nil)

-- t1 :: forall repr . (Mochastic repr) => repr (Measure Real)
-- t1 = unpair (pair 1 2) uniform 

-- norm :: (Embed repr, Mochastic repr) => repr (Measure (P2 Real Real))
-- norm = normal 0 1 `bind` \x ->
--        normal x 1 `bind` \y ->
--        dirac (p2 x y)
