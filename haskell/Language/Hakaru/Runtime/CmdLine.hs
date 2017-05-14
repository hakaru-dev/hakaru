{-# LANGUAGE FlexibleInstances,
             UndecidableInstances #-}
module Language.Hakaru.Runtime.CmdLine where

import qualified Data.Number.LogFloat            as LF
import qualified Data.Vector                     as V
import qualified Data.Vector.Unboxed             as U
import qualified Data.Vector.Generic             as G
import qualified Data.Vector.Generic.Mutable     as M
import Language.Hakaru.Syntax.IClasses
import System.Environment

parseRank0 :: (Read a) => String -> IO a
parseRank0 = return . read

parseRank1 :: (U.Unbox a, Read a) => String -> IO (U.Vector a)
parseRank1 s = U.fromList . fmap read . lines <$> readFile s


class Parseable a where
  parse :: String -> IO a

instance Parseable Int where
  parse = return . read

instance Parseable Double where
  parse = return . read

instance Parseable LF.LogFloat where
  parse = return . LF.logFloat . read

-- instance (U.Unbox a, Read a) => Parseable (U.Vector a) where
--   parse s = U.fromList . fmap read . lines <$> readFile s


{-
Make main needs to recur down the function type while at the term level build up
a continuation of parses and partial application of the function

The continuation, takes an
-}
class Main p where
  makeMain :: p -> ([String] -> IO (p',[String])) -> IO ()

-- instance (Parseable a, Main b) => Main (a -> b) where
--   makeMain prog []     = error "Insufficient arguments"
--   makeMain prog (a:as) = do p' <- prog <$> parse a
--                             return (p',as)

-- instance Main Int where
--   makeMain p _ = print p

-- instance Main Double where
--   makeMain p k = k >> print p

-- instance Main LF.LogFloat where
--   makeMain p k = k >> print p
