{-# LANGUAGE ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances, DeriveDataTypeable #-}
{-# LANGUAGE UndecidableInstances, ConstraintKinds #-}
{-# OPTIONS -W #-}

module Language.Hakaru.Simplify
  ( closeLoop
  , simplify
  , toMaple
  , Simplifiable
  , SimplifyException(MapleException,InterpreterException)) where

-- Take strings from Maple and interpret them in Haskell (Hakaru)

import Prelude hiding (Real)
import Control.Exception
import Language.Hakaru.Syntax (Measure, Vector, Prob, Real)
import Language.Hakaru.Expect (Expect, unExpect)
import Language.Hakaru.Embed 
import Language.Hakaru.Maple (Maple, runMaple)
import Language.Hakaru.Any (Any)
import Data.Typeable (Typeable, typeOf)
import System.MapleSSH (maple)
import Language.Haskell.Interpreter hiding (typeOf)

import Language.Hakaru.Util.Lex (readMapleString)


data SimplifyException = MapleException String String
                       | InterpreterException String
                       deriving (Typeable)
                       -- deriving (Show, Typeable)

-- Maple prints errors with "cursors" (^) which point to the specific position
-- of the error on the line above. The derived show instance doesn't preserve
-- positioning of the cursor. 
instance Show SimplifyException where 
  show (MapleException a b) = "MapleException: \n" ++ a ++ "\n" ++ b
  show (InterpreterException a) = "InterpreterException: \n" ++ a

instance Exception SimplifyException


ourContext :: MonadInterpreter m => m ()
ourContext = do
  let modules = ["Language.Hakaru.RoundTrip"]

  loadModules modules

  -- "Tag" requires DataKinds to use type list syntax 
  exts <- get languageExtensions
  set [ languageExtensions := (UnknownExtension "DataKinds" : exts) ] 

  setImports modules


closeLoop :: (Typeable a) => String -> IO a
closeLoop s = action where
  action = do
    -- putStrLn ("To Haskell: " ++ s')
    result <- runInterpreter (ourContext >> interpret s' undefined)
    case result of
      Left err -> throw $ InterpreterException $ unlines ["Error when interpretting", s', show err]
      Right a -> return a

  s' :: String
  s' = s ++ " :: " ++ show (typeOf (getArg action))

class (Typeable a) => Simplifiable a where
  mapleType :: a{-unused-} -> String

instance Simplifiable () where mapleType _ = "Unit"
instance Simplifiable Int where mapleType _ = "Int"
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

instance Simplifiable a => Simplifiable (Vector a) where
  mapleType _ = "MVector(" ++ mapleType (undefined :: a) ++ ")"

instance (Simplifiable a, Simplifiable b) => Simplifiable (a -> b) where
  mapleType _ = "Arrow(" ++ mapleType (undefined :: a) ++ "," ++
                            mapleType (undefined :: b) ++ ")"

instance (SingI xss, All2 Typeable xss, Typeable t, Typeable (Tag t xss)) => Simplifiable (Tag t xss) where 
  mapleType = mapleTypeTag 

mkTypeString :: (Simplifiable a) => String -> a -> String
mkTypeString s t = "Typed(" ++ s ++ ", " ++ mapleType t ++ ")"

simplify :: (Simplifiable a) => Expect Maple a -> IO (Any a)
simplify e = do
  let slo = toMaple e
  hakaru <- do
    -- putStrLn ("\nTo Maple: " ++ slo)
    hopeString <- maple ("timelimit(5,Haskell(SLO:-AST(SLO(" ++ slo ++ "))));")
    case readMapleString hopeString of
      Just hakaru -> return hakaru
      Nothing -> throw $ MapleException slo hopeString
  closeLoop ("Any (" ++ hakaru ++ ")")

getArg :: f a -> a
getArg = undefined

toMaple :: (Simplifiable a) => Expect Maple a -> String
toMaple e = mkTypeString (runMaple (unExpect e) 0) (getArg e)
