{-# LANGUAGE FlexibleInstances,
             UndecidableInstances #-}
module Language.Hakaru.Runtime.CmdLine where

import qualified Data.Vector                     as V
import qualified Data.Vector.Unboxed             as U
import qualified Data.Vector.Generic             as G
import qualified Data.Vector.Generic.Mutable     as M
import Data.Number.LogFloat
-- import Language.Hakaru.Syntax.IClasses
import System.Environment

class Parseable a where
  parse :: String -> IO a

instance Parseable Int where
  parse = return . read

instance Parseable Double where
  parse = return . read

instance Parseable LogFloat where
  parse = return . logFloat . read

-- instance (U.Unbox a, Read a) => Parseable (U.Vector a) where
--   parse s = U.fromList . fmap read . lines <$> readFile s


{-
Make main needs to recur down the function type while at the term level build up
a continuation of parses and partial application of the function

The continuation, takes an
-}
class Main p where
  makeMain :: (p,[String]) -> IO (p,[String])

instance Main Int where
  makeMain = return

instance Main Double where
  makeMain = return

instance Main LogFloat where
  makeMain = return

instance (Parseable a, Main b, Show b) => Main (a -> b) where
  makeMain (prog,a:as) = do a' <- parse a
                            return (prog a', as)
