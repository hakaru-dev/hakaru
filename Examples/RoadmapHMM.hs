{-# LANGUAGE RankNTypes, TypeOperators, ScopedTypeVariables, TypeFamilies, FlexibleContexts #-}

module Examples.RoadmapHMM where

import Prelude hiding (Real)
import qualified Control.Monad

import qualified Data.Vector as V

import Language.Hakaru.Syntax
import Language.Hakaru.Sample
import Language.Hakaru.Expect
import Language.Hakaru.Embed


-- To keep things concrete we will assume 5 latent states, 3 observed states
-- and a sequence of 20 transitions. We know we start in latent state 0.

type Table = Vector (Vector Prob)

symDirichlet :: (Lambda repr, Integrate repr, Mochastic repr) =>
                repr Int -> repr Prob -> repr (Measure (Vector Prob))
symDirichlet n a = liftM normalizeV (plate (constV n (gamma a 1)))

start :: Base repr => repr Int
start = 0

transMat :: (Lambda repr, Integrate repr, Mochastic repr) =>
            repr (Measure Table)
transMat = plate (vector 5 (\ i ->
                            symDirichlet 5 1))

emitMat :: (Lambda repr, Integrate repr, Mochastic repr) =>
            repr (Measure Table)
emitMat =  plate (vector 5 (\ i ->
                            symDirichlet 3 1))

transition :: (Lambda repr, Integrate repr, Mochastic repr) =>
              repr Table -> repr Int -> repr (Measure Int)
transition v s = categorical (index v s)

emission   :: (Lambda repr, Integrate repr, Mochastic repr) =>
              repr Table -> repr Int -> repr (Measure Int)
emission v s = categorical (index v s)

roadmapProg1 :: (Integrate repr, Lambda repr, Mochastic repr) =>
                repr (Measure (Vector Int, (Table, Table)))
roadmapProg1 = transMat `bind` \trans ->
               emitMat `bind`  \emit  ->
               app (chain (vector 20
                  (\ _ -> lam $ \s ->
                   transition trans s `bind` \s' ->
                   emission emit s' `bind` \o ->
                   dirac $ pair o s'
                  ))) start `bind` \x ->
               dirac (pair (fst_ x) (pair trans emit))
