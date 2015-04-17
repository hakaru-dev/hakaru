{-# LANGUAGE RankNTypes, TypeOperators, ScopedTypeVariables, TypeFamilies, FlexibleContexts #-}

module Examples.RoadmapHMM where

import Prelude hiding (Real)
import qualified Control.Monad

import qualified Data.Vector as V

import Language.Hakaru.Syntax
import Language.Hakaru.Sample
import Language.Hakaru.Expect
import Language.Hakaru.Embed
import Language.Hakaru.Lazy

-- To keep things concrete we will assume 5 latent states, 3 observed states
-- and a sequence of 20 transitions. We know we start in latent state 0.

type Table = Vector (Vector Prob)
type MCState = (Table,Table)

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

roadmapProg2 :: (Integrate repr, Lambda repr, Mochastic repr) =>
                repr (Vector Int) -> repr (Measure (Table, Table))
roadmapProg2 o = transMat `bind` \trans ->
                 emitMat `bind`  \emit  ->
                 app (chain (vector 20
                  (\ i -> lam $ \s ->
                   transition trans s `bind` \s' ->
                   factor (index (index emit s') (index o i)) `bind` \d ->
                   dirac $ pair d s'
                  ))) start `bind` \x ->
                 dirac (pair trans emit)

reflect :: (Mochastic repr, Lambda repr, Integrate repr) =>
           repr Table -> Expect repr (Int -> Measure Int)
reflect m = lam (\i -> let v = index (Expect m) i
                       in weight (summateV v) (categorical v))

reify :: (Mochastic repr, Lambda repr, Integrate repr) =>
         repr Int -> repr Int ->
         Expect repr (Int -> Measure Int) -> repr Table
reify domainSize rangeSize m =
  vector domainSize (\i ->
  vector rangeSize  (\j ->
  app (snd_ (app (unExpect m) i)) (lam (\j' -> if_ (equal j j') 1 0))))

bindo :: (Mochastic repr, Lambda repr) =>
         repr (a -> Measure b) ->
         repr (b -> Measure c) ->
         repr (a -> Measure c)
bindo f g = lam (\x -> app f x `bind` app g)

chain'' :: (Mochastic repr, Lambda repr, Integrate repr) =>
           repr (Vector Table) -> repr Table
chain'' = reduce bindo' (reify 5 5 (lam dirac))

bindo' :: (Mochastic repr, Lambda repr, Integrate repr) =>
          repr Table -> repr Table -> repr Table
bindo' m n = reify 5 5 (bindo (reflect m) (reflect n))

roadmapProg3 :: (Integrate repr, Lambda repr, Mochastic repr) =>
                Expect repr (Vector Int) -> Expect repr (Measure (Table, Table))
roadmapProg3 o = transMat `bind` \trans ->
                 emitMat `bind`  \emit  ->
                 app (reflect (chain'' (vector 20 $ \i ->
                                        reify 5 5 $
                                        lam $ \s ->
                                        transition trans s `bind` \s' ->
                                        factor (index
                                                (index emit s')
                                                (index o (Expect i))) `bind` \d ->
                                        dirac s'))) start `bind` \x ->
                 dirac (pair trans emit)

mcmc' :: (Lambda repr, Integrate repr, Mochastic repr) =>
         repr (Vector Int) -> repr MCState -> repr MCState ->
         repr (Measure MCState)
mcmc' o old new =
  let_ (densProg o new / densProg o old) $ \ratio ->
    bern (min_ 1 ratio) `bind` \accept ->
    dirac (if_ accept new old)

-- Assumes prior came from symmetric dirichlet with alpha=1
densTable :: Mochastic repr => repr Table -> repr Prob
densTable t = reduce (*) 1 $ vector (size t)
              (\i -> gammaFunc $ fromInt $ size (index t i))
            
densProg :: (Lambda repr, Integrate repr, Mochastic repr) =>
            repr (Vector Int) -> repr MCState -> repr Prob
densProg o x = unpair x (\ trans emit ->
               reduce (*) 0 (vector 20 $ \t ->
                             sumV $ vector 5  $ \i ->
                             sumV $ vector 5  $ \j ->
                             index (index trans i) j * index (index emit j) (index o t)
                            ))
                           

resampleRow :: (Lambda repr, Integrate repr, Mochastic repr) =>
               repr Table -> repr (Measure Table)
resampleRow t = symDirichlet (size t) 1 `bind`
                categorical `bind` \ri ->
                let_ (index t ri) (\row ->
                symDirichlet (size row) 1 `bind` \row' ->
                dirac $ vector (size t) (\ i ->
                                         if_ (equal_ i ri)
                                         row'
                                         (index t i)))

-- Resample a row of both the emission and transmission matrices

roadmapProg4  :: (Integrate repr, Lambda repr, Mochastic repr) =>
                Expect repr (Vector Int) ->
                Expect repr MCState ->
                Expect repr (Measure MCState)
roadmapProg4 o x = unpair x (\ trans emit ->
                   resampleRow trans `bind` \trans' ->
                   resampleRow emit  `bind` \emit' ->
                   mcmc' o (pair trans  emit)
                           (pair trans' emit'))
