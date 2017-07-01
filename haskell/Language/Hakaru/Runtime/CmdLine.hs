{-# LANGUAGE CPP,
             FlexibleContexts,
             FlexibleInstances,
             UndecidableInstances,
             TypeFamilies #-}
module Language.Hakaru.Runtime.CmdLine where

import qualified Data.Vector.Unboxed             as U
import qualified System.Random.MWC               as MWC
import           Control.Monad                   (liftM, ap, forever)

#if __GLASGOW_HASKELL__ < 710
import           Data.Functor
import           Control.Applicative             (Applicative(..))
#endif

newtype Measure a = Measure { unMeasure :: MWC.GenIO -> IO (Maybe a) }

instance Functor Measure where
    fmap  = liftM
    {-# INLINE fmap #-}

instance Applicative Measure where
    pure x = Measure $ \_ -> return (Just x)
    {-# INLINE pure #-}
    (<*>)  = ap
    {-# INLINE (<*>) #-}

instance Monad Measure where
    return  = pure
    {-# INLINE return #-}
    m >>= f = Measure $ \g -> do
                          Just x <- unMeasure m g
                          unMeasure (f x) g
    {-# INLINE (>>=) #-}

makeMeasure :: (MWC.GenIO -> IO a) -> Measure a
makeMeasure f = Measure $ \g -> Just <$> f g
{-# INLINE makeMeasure #-}

-- A class of types that can be parsed from command line arguments
class Parseable a where
  parse :: String -> IO a

instance Parseable Int where
  parse = return . read

instance Parseable Double where
  parse = return . read

instance (U.Unbox a, Parseable a) => Parseable (U.Vector a) where
  parse s = U.fromList <$> ((mapM parse) =<< (lines <$> readFile s))

instance (Read a, Read b) => Parseable (a, b) where
  parse = return . read

{- Make main needs to recur down the function type while at the term level build
-- up a continuation of parses and partial application of the function
-}
class MakeMain p where
  makeMain :: p -> [String] -> IO ()

instance {-# OVERLAPPABLE #-}
         Show a => MakeMain a where
  makeMain p _ = print p

instance Show a => MakeMain (Measure a) where
  makeMain p _ = MWC.createSystemRandom >>= \gen ->
                   forever $ do
                     ms <- unMeasure p gen
                     case ms of
                       Nothing -> return ()
                       Just s  -> print s

instance (Parseable a, MakeMain b)
         => MakeMain (a -> b) where
  makeMain p (a:as) = do a' <- parse a
                         makeMain (p a') as
  makeMain _ [] = error "not enough arguments"
