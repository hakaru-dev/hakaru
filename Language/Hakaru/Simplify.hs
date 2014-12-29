{-# LANGUAGE ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances #-}
{-# OPTIONS -W #-}

module Language.Hakaru.Simplify
  ( closeLoop
  , simplify
  , toMaple
  , Simplifiable) where

-- Take strings from Maple and interpret them in Haskell (Hakaru)

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Measure, Prob, Real)
import Language.Hakaru.Expect (Expect, unExpect)
import Language.Hakaru.Maple (Maple, runMaple)
import Language.Hakaru.Any (Any)
import Data.Typeable (Typeable, typeOf)
import System.MapleSSH (maple)
import Language.Haskell.Interpreter hiding (typeOf)

import Language.Hakaru.Util.Lex (readMapleString)

ourContext :: MonadInterpreter m => m ()
ourContext = do
  let modules = ["Language.Hakaru.RoundTrip"]
  loadModules modules
  setImports modules

closeLoop :: (Typeable a) => String -> IO a
closeLoop s = action where
  action = do
    -- putStrLn ("To Haskell: " ++ s')
    result <- runInterpreter (ourContext >> interpret s' undefined)
    case result of
      Left err -> error (show err)
      Right a -> return a
  s' :: String
  s' = s ++ " :: " ++ show (typeOf (getArg action))

class (Typeable a) => Simplifiable a where
  mapleType :: a{-unused-} -> String

instance Simplifiable () where mapleType _ = "Unit"
instance Simplifiable Real where mapleType _ = "Real"
instance Simplifiable Prob where mapleType _ = "Prob"
instance Simplifiable Bool where mapleType _ = "Bool"

instance (Simplifiable a, Simplifiable b) => Simplifiable (a,b) where
  mapleType _ = "Pair(" ++ mapleType (undefined :: a) ++ "," ++
                           mapleType (undefined :: b) ++ ")"

instance Simplifiable a => Simplifiable [a] where
  mapleType _ = "List(" ++ mapleType (undefined :: a) ++ ")"

instance Simplifiable a => Simplifiable (Measure a) where
  mapleType _ = "Measure(" ++ mapleType (undefined :: a) ++ ")"

instance (Simplifiable a, Simplifiable b) => Simplifiable (a -> b) where
  mapleType _ = "Arrow(" ++ mapleType (undefined :: a) ++ "," ++
                            mapleType (undefined :: b) ++ ")"

mkTypeString :: (Simplifiable a) => String -> a -> String
mkTypeString s t = "Typed(" ++ s ++ ", " ++ mapleType t ++ ")"

simplify :: (Simplifiable a) => Expect Maple a -> IO (Any a)
simplify e = do
  let slo = toMaple e
  hakaru <- do
    -- putStrLn ("\nTo Maple: " ++ slo)
    hopeString <- maple ("Haskell(SLO:-AST(SLO(" ++ slo ++ ")));")
    case readMapleString hopeString of
      Just hakaru -> return hakaru
      Nothing -> error ("From Maple: " ++ hopeString)
  closeLoop ("Any (" ++ hakaru ++ ")")

getArg :: f a -> a
getArg = undefined

toMaple :: (Simplifiable a) => Expect Maple a -> String
toMaple e = mkTypeString (runMaple (unExpect e) 0) (getArg e)
