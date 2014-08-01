{-# LANGUAGE RankNTypes, DataKinds, NoMonomorphismRestriction, BangPatterns #-}

module Examples (test_gaussian_mixture) where

import Language.Hakaru.Types
import Data.Dynamic
import Control.Monad

import Language.Hakaru.ImportanceSampler
import Language.Hakaru.Distribution
import Language.Hakaru.Lambda

bayesian_polynomial_regression = undefined

sparse_linear_regression = undefined

logistic_regression = undefined

outlier_detection = undefined

change_point_model = undefined

friends_who_smoke = undefined

latent_dirichelt_allocation = undefined

categorical_mixture = undefined

gaussian_mixture :: Measure [Double]
gaussian_mixture = do
  p <- unconditioned (beta 2 2)
  m1:m2:_ <- replicateM 2 $ unconditioned (normal 0 10)
  s1:s2:_ <- replicateM 2 $ unconditioned (uniform 0 1)
  let makePoint = do        
        b <- unconditioned (bern p)
        unconditioned (ifThenElse b (normal m1 s1)
                                    (normal m2 s2))
  replicateM 20 makePoint

test_gaussian_mixture :: IO ()
test_gaussian_mixture = sample gaussian_mixture [] >>= print . take 1

naive_bayes = undefined

hidden_markov_model = undefined

matrix_factorization = undefined

rvm = undefined

item_response_theory = undefined

gaussian_process = undefined

hawkes_process = undefined

bayesian_neural_network = undefined
