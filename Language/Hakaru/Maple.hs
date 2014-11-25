{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable, GADTs, Rank2Types #-}
{-# OPTIONS -W -fno-warn-warnings-deprecations -fno-warn-unused-binds #-}

module Language.Hakaru.Maple (Maple(..), runMaple, Any(..), closeLoop, roundTrip, RoundTrip) where

-- Maple printing interpretation

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Bool_, Measure, ggcast, Uneither(Uneither),
    Order(..), Base(..), Summate(..), Integrate(..), Lambda(..), Mochastic(..))
import Data.Ratio
import Data.Typeable (Typeable, Typeable1, typeOf, gcast)
import Data.Maybe (fromMaybe)
import Control.Monad (liftM2)
import Control.Monad.Trans.Reader (ReaderT(ReaderT), runReaderT)
import Control.Monad.Trans.Cont (Cont, cont, runCont)

import Language.Hakaru.PrettyPrint (runPrettyPrint) -- just for testing closeLoop
import System.MapleSSH -- ditto
import Text.Read (readEither)
import Language.Hakaru.Expect (Expect(unExpect))

import Language.Haskell.Interpreter hiding (typeOf)

newtype Maple a = Maple { unMaple :: ReaderT Int (Cont String) String }

-- "piecewise" in Maple only works when the expression has numeric type.
-- So "runMaple" should only be used when the expression has numeric type.
runMaple :: Maple a -> Int -> String
runMaple (Maple x) i = runCont (runReaderT x i) id

mapleFun1 :: String -> Maple a -> Maple b
mapleFun1 fn (Maple x) =
  Maple (fmap (\y -> fn ++ "(" ++ y ++ ")") x)

mapleFun2 :: String -> Maple a -> Maple b -> Maple c
mapleFun2 fn (Maple x) (Maple y) =
  Maple (liftM2 (\w z -> fn ++ "(" ++ w ++ ", " ++ z ++ ")") x y)

mapleOp2 :: String -> Maple a -> Maple b -> Maple c
mapleOp2 fn (Maple x) (Maple y) =
  Maple (liftM2 (\w z -> "(" ++ w ++ fn ++ z ++ ")") x y)

mapleBind :: (Maple a -> Maple b) -> Int -> (String, String)
mapleBind f i = (x, runMaple (f (Maple (return x))) (i + 1))
  where x = "x" ++ show i

instance Order Maple a where
  less = mapleOp2 "<"

instance Num (Maple a) where
  (+)              = mapleOp2 "+"
  (*)              = mapleOp2 "*"
  (-)              = mapleOp2 "-"
  negate (Maple x) = Maple (fmap (\u -> "(-" ++ u ++ ")") x)
  abs              = mapleFun1 "abs"
  signum           = mapleFun1 "signum"
  fromInteger x    = Maple (return (show x))

instance Fractional (Maple a) where
  (/)            = mapleOp2 "/"
  fromRational x = Maple (return ("(" ++ show (numerator   x) ++
                                  "/" ++ show (denominator x) ++ ")"))

instance Floating (Maple a) where
  pi    = Maple (return "Pi")
  exp   = mapleFun1 "exp"
  sqrt  = mapleFun1 "sqrt"
  log   = mapleFun1 "log"
  (**)  = mapleOp2 "^"
  logBase (Maple b) (Maple y) =
    Maple (liftM2 (\b' y' -> "log[" ++ b' ++ "]" ++ "(" ++ y' ++ ")") b y)
  sin   = mapleFun1 "sin"
  tan   = mapleFun1 "tan"
  cos   = mapleFun1 "cos"
  asin  = mapleFun1 "asin"
  atan  = mapleFun1 "atan"
  acos  = mapleFun1 "acos"
  sinh  = mapleFun1 "sinh"
  tanh  = mapleFun1 "tanh"
  cosh  = mapleFun1 "cosh"
  asinh = mapleFun1 "asinh"
  atanh = mapleFun1 "atanh"
  acosh = mapleFun1 "acosh"

instance Base Maple where
  unit = Maple (return "Unit")
  pair = mapleFun2 "Pair"
  unpair (Maple ab) k = Maple (ab >>= \ab' ->
    let opab :: Int -> String
        opab n = "op(" ++ show n ++ ", " ++ ab' ++ ")" 
    in
    unMaple (k (Maple (return (opab 1))) (Maple (return (opab 2)))))
  inl (Maple a) = fromMaybe defaultCase (gcast booleanCase)
    where defaultCase = Maple (fmap (\a' -> "Left("  ++ a' ++ ")") a)
          booleanCase :: Maple Bool_
          booleanCase = Maple (return "true")
  inr (Maple b) = fromMaybe defaultCase (gcast booleanCase)
    where defaultCase = Maple (fmap (\b' -> "Right(" ++ b' ++ ")") b)
          booleanCase :: Maple Bool_
          booleanCase = Maple (return "false")
  uneither = r where
    Uneither r = fromMaybe defaultCase (ggcast booleanCase)
    defaultCase = Uneither (\(Maple ab) ka kb -> Maple (ab >>= \ab' ->
      ReaderT $ \i -> cont $ \c ->
      let opab :: Int -> String
          opab n = "op(" ++ show n ++ ", " ++ ab' ++ ")" in
      let arm tag k = opab 0 ++ " = " ++ tag ++ ", " ++
                      runCont (runReaderT (k (return (opab 1))) i) c
      in "piecewise(" ++ arm "Left"  (unMaple . ka . Maple)
              ++ ", " ++ arm "Right" (unMaple . kb . Maple) ++ ")"))
    booleanCase :: Uneither Maple () ()
    booleanCase = Uneither (\(Maple ab) ka kb -> Maple (ab >>= \ab' ->
      ReaderT $ \i -> cont $ \c ->
      let arm k = runCont (runReaderT (unMaple (k unit)) i) c
      in "piecewise(" ++ ab' ++ ", " ++ arm ka
                             ++ ", " ++ arm kb ++ ")"))
  unsafeProb (Maple x) = Maple x
  fromProb   (Maple x) = Maple x
  fromInt    (Maple x) = Maple x
  sqrt_ = mapleFun1 "sqrt"
  pow_ = mapleOp2 "^"
  infinity         = Maple (return  "infinity")
  negativeInfinity = Maple (return "-infinity")
  gammaFunc = mapleFun1 "GAMMA"
  betaFunc = mapleFun2 "Beta"
  fix = mapleFun1 "(proc (f) local x; x := f(x) end proc)" . lam

instance Summate Maple where
  summate (Maple lo) (Maple hi) f = Maple (lo >>= \lo' -> hi >>= \hi' ->
    ReaderT $ \i -> return $
    let (x, body) = mapleBind f i
    in "sum(" ++ body ++ "," ++ x ++ "=" ++ lo' ++ ".." ++ hi' ++ ")")

instance Integrate Maple where
  integrate (Maple lo) (Maple hi) f = Maple (lo >>= \lo' -> hi >>= \hi' ->
    ReaderT $ \i -> return $
    let (x, body) = mapleBind f i
    in "int(" ++ body ++ "," ++ x ++ "=" ++ lo' ++ ".." ++ hi' ++ ")")

instance Lambda Maple where
  lam f = Maple (ReaderT $ \i -> return $
    let (x, body) = mapleBind f i in "(" ++ x ++ "->" ++ body ++ ")")
  app (Maple rator) (Maple rand) =
    Maple (liftM2 (\rator' rand' -> rator' ++ "(" ++ rand' ++ ")") rator rand)

-- and now for the other way around: take things that came from Maple
-- (as strings), and interpret in Haskell.  This is probably not the best
-- place for this code, since Maple is supposed to produce proper Haskell,
-- but this is a start.
ourContext :: MonadInterpreter m => m ()
ourContext = do
  let modules = ["Language.Hakaru.RoundTrip"]
  loadModules modules
  setImports (modules)

-- This is silly, as all we can read back in right now are fractions.
-- But at least this much works!
closeLoop :: (Typeable1 repr) => String -> IO (Either InterpreterError (repr ()))
closeLoop s = runInterpreter (ourContext >> interpret s undefined)

newtype Any a = Any
  { unAny :: forall repr. (Base repr, Lambda repr, Mochastic repr) => repr a }
  deriving Typeable
  -- beware GHC 7.8 https://ghc.haskell.org/trac/ghc/wiki/GhcKinds/PolyTypeable

pMaple :: String -> IO () 
pMaple s = do
  result <- closeLoop ("Any (" ++ s ++ ")")
  case result of
    Left err -> print err
    Right a -> do
      print (runPrettyPrint (unAny a))
      -- putStrLn (runMaple (unAny a) 0)

main :: IO () -- should print "(lam $ \x0 -> x0) `app` unit"
main = do
  result <- closeLoop "Any (lam id `app` unit)"
  case result of
    Left err -> print err
    Right a -> do
      print (runPrettyPrint (unAny a))
      -- putStrLn (runMaple (unAny a) 0)

class (Typeable a) => RoundTrip a where
  roundTrip' :: (Monad m) => Int -> a{-unused-} -> String ->
                (String -> m String) -> m String

instance (Typeable a) => RoundTrip (Measure a) where
  -- The type "a" should not contain "Measure"
  roundTrip' _ _ s k = k s

instance (Typeable a, RoundTrip b) => RoundTrip (a -> b) where
  -- The type "a" should not contain "Measure"
  roundTrip' n dummy s k = do
    let arrrg = "arrrg" ++ show n
    maple <- roundTrip' (succ n) (undefined `asTypeOf` dummy undefined) s
               (\maple -> k (maple ++ "(" ++ arrrg ++ ")"))
    return ("lam $ \\" ++ arrrg ++ " -> " ++ maple)

roundTrip :: (RoundTrip a) => Expect Maple a -> IO (Any a)
roundTrip e = do
  let getArg :: Expect Maple a -> a
      getArg = undefined
  hakaru <- roundTrip' 0 (getArg e) (runMaple (unExpect e) 0) (\slo -> do
    putStrLn ("To Maple: " ++ slo)
    hopeString <- maple ("Haskell(SLO:-AST(SLO(" ++ slo ++ ")));")
    case readEither hopeString of
      Right hakaru -> return hakaru
      Left err -> error ("roundTrip: " ++ err ++ " for " ++ show hopeString))
  putStrLn ("From Maple: " ++ hakaru)
  let cl s = runInterpreter (ourContext >> interpret s undefined)
      typ = "" `asTypeOf` (" :: Any (" ++ show (typeOf (getArg e)) ++ ")")
  result <- cl ("Any (" ++ hakaru ++ ")" ++ typ)
  case result of
    Left err -> error $ show err
    Right a -> return a
