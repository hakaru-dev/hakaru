module Util.Coda where

import Statistics.Autocorrelation
import qualified Data.Packed.Vector as V
import qualified Data.Vector.Generic as G

effectiveSampleSize :: [Double] -> Double
effectiveSampleSize samples = n / (1 + 2*(G.sum rho))
  where n = fromIntegral (V.dim vec)
        vec = V.fromList samples
        cov = autocovariance vec
        rho = G.map (/ G.head cov) cov
