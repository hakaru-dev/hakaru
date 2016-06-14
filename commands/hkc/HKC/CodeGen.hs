{-# LANGUAGE OverloadedStrings,
             DataKinds,
             GADTs,
             KindSignatures #-}

module HKC.CodeGen where

import           Language.Hakaru.Syntax.ABT
import qualified Language.Hakaru.Syntax.AST as T
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Types.Sing
import Language.Hakaru.Types.DataKind (Hakaru(..))

import qualified Language.C.Pretty as C

import HKC.Flatten

import Prelude hiding (unlines,concat)
import Data.Text
import Text.PrettyPrint


-- | Create program is the top level C codegen. Depending on the type a program
--   will have a different construction. HNat will just return while a measure
--   returns a sampling program.
createProgram :: TypedAST (TrivialABT T.Term) -> Text
createProgram (TypedAST typ abt) = mainWith typ body
  where body = pack $ render $ C.pretty $ flatten abt

header :: Text
header = unlines
       [ "#include <time.h>"
       , "#include <stdlib.h>"
       , "#include <stdio.h>"
       , "#include <math.h>" ]

normalC :: Text
normalC = unlines
        [ "double normal(double mu, double sd) {"
        , "  double u = ((double)rand() / (RAND_MAX)) * 2 - 1;"
        , "  double v = ((double)rand() / (RAND_MAX)) * 2 - 1;"
        , "  double r = u*u + v*v;"
        , "  if (r==0 || r>1) return normal(mu,sd);"
        , "  double c = sqrt(-2 * log(r) / r);"
        , "  return mu + u * c * sd;"
        , "}" ]

mainWith :: Sing (a :: Hakaru) -> Text -> Text
mainWith typ body = unlines
 [ "void main(){"
 , "  srand(time(NULL));"
 , ""
 , concat ["  int result = ",body]
 , ""
 , case typ of
     SMeasure _ -> "  while(1) printf(\"%.17g\\n\",result);"
     _          -> "  printf(\"%.17g\\n\",result);"
 , "}" ]

{-
let_ :: a -> (a -> b) -> b
let_ x f = let x1 = x in f x1

normal :: Double -> Double -> MWC.GenIO -> IO Double
normal mu sd g = MWCD.normal mu sd g

(>>=) :: (MWC.GenIO -> IO a)
      -> (a -> MWC.GenIO -> IO b)
      -> MWC.GenIO
      -> IO b
m >>= f = \g -> m g M.>>= flip f g

dirac :: a -> MWC.GenIO -> IO a
dirac x _ = return x

nat_ :: Integer -> Integer
nat_ = id

nat2prob :: Integer -> Double
nat2prob = fromIntegral

nat2real :: Integer -> Double
nat2real = fromIntegral

real_ :: Rational -> Double
real_ = fromRational

prob_ :: NonNegativeRational -> Double
prob_ = fromRational . fromNonNegativeRational

run :: Show a => MWC.GenIO -> (MWC.GenIO -> IO a) -> IO ()
run g k = k g M.>>= print
-}
