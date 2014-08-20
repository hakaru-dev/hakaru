import Criterion.Main

import Control.Monad

import Language.Hakaru.Distribution
import qualified Language.Hakaru.Metropolis as MH
import qualified Language.Hakaru.ImportanceSampler as IS

giveLast :: IO [(a,b)] -> IO (a,b)
giveLast samples = do s <- samples
                      return $ last (take 100 s)

main = defaultMain [
   bcompare [
     bench "is normal 10"  $ whnfIO $ giveLast (IS.sample (replicateM 10 (IS.unconditioned (normal 0 10))) [])
   , bench "is normal 20"  $ whnfIO $ giveLast (IS.sample (replicateM 20 (IS.unconditioned (normal 0 10))) [])
   , bench "mh normal 10"  $ whnfIO $ giveLast (MH.sample (replicateM 10 (MH.unconditioned (normal 0 10))) [])
   , bench "mh normal 20"  $ whnfIO $ giveLast (MH.sample (replicateM 20 (MH.unconditioned (normal 0 10))) [])
   ]
 ]
