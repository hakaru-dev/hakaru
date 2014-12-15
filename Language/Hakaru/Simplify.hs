{-# LANGUAGE DeriveDataTypeable, Rank2Types, ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# OPTIONS -W #-}

module Language.Hakaru.Simplify (Any(..), closeLoop, simplify, Simplify) where

-- Take strings from Maple and interpret them in Haskell (Hakaru)

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Measure, Lambda(..), Mochastic(..), 
  Prob, Real, Bool_)
import Language.Hakaru.Expect (Expect, unExpect)
import Language.Hakaru.Maple (Maple, runMaple)
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
    putStrLn ("To Haskell: " ++ s')
    result <- runInterpreter (ourContext >> interpret s' undefined)
    case result of
      Left err -> error (show err)
      Right a -> return a
  s' :: String
  s' = s ++ " :: " ++ show (typeOf (getArg action))

newtype Any a = Any
  { unAny :: forall repr. (Lambda repr, Mochastic repr) => repr a }
  deriving Typeable
  -- beware GHC 7.8 https://ghc.haskell.org/trac/ghc/wiki/GhcKinds/PolyTypeable

class MapleableType a where
  mapleType :: a{-unused-} -> String

instance MapleableType () where mapleType _ = "Unit"
instance MapleableType Real where mapleType _ = "Real"
instance MapleableType Prob where mapleType _ = "Prob"
instance MapleableType Bool_ where mapleType _ = "Bool_"

instance (MapleableType a, MapleableType b) => MapleableType (a,b) where
  mapleType _ = "Pair(" ++ mapleType (undefined :: a) ++ "," ++
                           mapleType (undefined :: b) ++ ")"

instance MapleableType a => MapleableType (Measure a) where
  mapleType _ = "Measure(" ++ mapleType (undefined :: a ) ++ ")"

instance (MapleableType a, MapleableType b) => MapleableType (a -> b) where
  mapleType _ = "Arrow(" ++ mapleType (undefined :: a) ++ "," ++
                            mapleType (undefined :: b) ++ ")"

class (Typeable a) => Simplify a where
  simplify' :: (Monad m) => Int -> a{-unused-} -> String ->
                (String -> m String) -> m String

mkTypeString :: MapleableType a => String -> a -> String
mkTypeString s t = "Typed(" ++ s ++ ", " ++ mapleType t ++ ")"

instance (Typeable a, MapleableType a) => Simplify (Measure a) where
  simplify' _ a s k = k $ mkTypeString s a

instance (Typeable a, Simplify b, MapleableType a, MapleableType b) => 
  Simplify (a -> b) where
  -- The type "a" should not contain "Measure"
  simplify' n dummy s k = do
    let arrrg = "arrrg" ++ show n
    let tarrrg = mapleType (undefined :: a)
    result <- simplify' (succ n) (undefined `asTypeOf` dummy undefined) s
               (\mapleString -> k (mkTypeString 
                 (mapleString ++ "(" ++ arrrg ++ " :: " ++ tarrrg ++ ")") 
                 dummy ))
    return ("lam $ \\" ++ arrrg ++ " -> " ++ result)

simplify :: (Simplify a) => Expect Maple a -> IO (Any a)
simplify e = do
  hakaru <- simplify' 0 (getArg e) (runMaple (unExpect e) 0) (\slo -> do
    putStrLn ("To Maple: " ++ slo)
    hopeString <- maple ("Haskell(SLO:-AST(SLO(" ++ slo ++ ")));")
    case readMapleString hopeString of
      Just hakaru -> return hakaru
      Nothing -> error ("From Maple: " ++ hopeString))
  closeLoop ("Any (" ++ hakaru ++ ")")

getArg :: f a -> a
getArg = undefined
