{-# LANGUAGE RankNTypes, DataKinds, NoMonomorphismRestriction, BangPatterns #-}

module Examples where

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
  let makePoint = do
        p <- unconditioned (beta 2 2)
        b <- unconditioned (bern p)
        unconditioned (ifThenElse b (normal (lit (1 :: Double)) (lit 1))
                                    (normal (lit (5 :: Double)) (lit 1)))
  replicateM 20 makePoint

naive_bayes = undefined

hidden_markov_model = undefined

matrix_factorization = undefined

rvm = undefined

item_response_theory = undefined

gaussian_process = undefined

hawkes_process = undefined

bayesian_neural_network = undefined
