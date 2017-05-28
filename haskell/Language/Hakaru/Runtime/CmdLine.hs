{-# LANGUAGE CPP,
             FlexibleContexts,
             FlexibleInstances,
             UndecidableInstances,
             TypeFamilies #-}
module Language.Hakaru.Runtime.CmdLine where

import qualified Data.Vector.Unboxed             as U
import qualified Data.Vector.Generic             as G
import qualified System.Random.MWC               as MWC
import Language.Hakaru.Runtime.LogFloatPrelude
import Data.Number.LogFloat
import Control.Monad (forever)

#if __GLASGOW_HASKELL__ < 710
import Data.Functor
#endif



-- A class of types that can be parsed from command line arguments
class Parseable a where
  parse :: String -> IO a

instance Parseable Int where
  parse = return . read

instance Parseable Double where
  parse = return . read

instance Parseable LogFloat where
  parse = return . logFloat . read

instance (U.Unbox a, Parseable a) => Parseable (U.Vector a) where
  parse s = U.fromList <$> ((mapM parse) =<< (lines <$> readFile s))

{- Make main needs to recur down the function type while at the term level build
-- up a continuation of parses and partial application of the function
-}
class MakeMain p where
  makeMain :: p -> [String] -> IO ()

instance MakeMain Int where
  makeMain p _ = print p

instance MakeMain Double where
  makeMain p _ = print p

instance MakeMain LogFloat where
  makeMain p _ = print p

instance Show a => MakeMain (Measure a) where
  makeMain p _ = MWC.createSystemRandom >>= \gen ->
                   forever $ do
                     ms <- unMeasure p gen
                     case ms of
                       Nothing -> return ()
                       Just s  -> print s

instance {-# OVERLAPPABLE #-}
         ( Show (v a), (G.Vector (MayBoxVec a) a), v ~ MayBoxVec a)
         => MakeMain (v a) where
  makeMain p _ = print p

instance {-# OVERLAPPING #-}(Parseable a, MakeMain b)
         => MakeMain (a -> b) where
  makeMain p (a:as) = do a' <- parse a
                         makeMain (p a') as
  makeMain _ [] = error "not enough arguments"
