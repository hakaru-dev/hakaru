{-# LANGUAGE ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances, DeriveDataTypeable #-}
{-# LANGUAGE UndecidableInstances, ConstraintKinds, CPP, GADTs #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Simplify
  ( closeLoop
  , simplify
  , toMaple
  , Simplifiable(mapleType)
  , MapleException(MapleException)
  , InterpreterException(InterpreterException) ) where

-- Take strings from Maple and interpret them in Haskell (Hakaru)

import Prelude hiding (Real)
import Control.Exception
import Language.Hakaru.Syntax (Measure, Vector, Prob, Real)
import Language.Hakaru.Expect (Expect, unExpect)
import Language.Hakaru.Embed
import Language.Hakaru.Maple (Maple, runMaple)
import Language.Hakaru.Any (Any)
import Data.Typeable (Typeable, typeOf)
import Data.List (intercalate)
import Data.List.Utils (replace)
import System.MapleSSH (maple)
import Language.Haskell.Interpreter.Unsafe (unsafeRunInterpreterWithArgs)
import Language.Haskell.Interpreter (
#ifdef PATCHED_HINT
    unsafeInterpret,
#else
    interpret,
#endif
    InterpreterError, MonadInterpreter, set, get, OptionVal((:=)),
    searchPath, languageExtensions, Extension(UnknownExtension),
    loadModules, setImports)

import Language.Hakaru.Util.Lex (readMapleString)
import Language.Hakaru.Paths

data MapleException       = MapleException String String
  deriving Typeable
data InterpreterException = InterpreterException InterpreterError String
  deriving Typeable

-- Maple prints errors with "cursors" (^) which point to the specific position
-- of the error on the line above. The derived show instance doesn't preserve
-- positioning of the cursor.
instance Show MapleException where
  show (MapleException toMaple_ fromMaple)
    = "MapleException:\n" ++ fromMaple ++
      "\nfrom sending to Maple:\n" ++ toMaple_

instance Show InterpreterException where
  show (InterpreterException err cause)
    = "InterpreterException:\n" ++ show err ++
      "\nwhile interpreting:\n" ++ cause

instance Exception MapleException

instance Exception InterpreterException

ourGHCOptions, ourSearchPath :: [String]
ourGHCOptions = case sandboxPackageDB of
                  Nothing -> []
                  Just xs -> "-no-user-package-db" : map ("-package-db " ++) xs
ourSearchPath = [ hakaruRoot ]

ourContext :: MonadInterpreter m => m ()
ourContext = do
  let modules = [ "Tests.Imports", "Tests.EmbedDatatypes" ]

  set [ searchPath := ourSearchPath ]

  loadModules modules

  -- "Tag" requires DataKinds to use type list syntax
  exts <- get languageExtensions
  set [ languageExtensions := (UnknownExtension "DataKinds" : exts) ]

  setImports modules

closeLoop :: (Typeable a) => String -> IO a
closeLoop s = action where
  action = do
    result <- unsafeRunInterpreterWithArgs ourGHCOptions $ ourContext >>
#ifdef PATCHED_HINT
                unsafeInterpret s' typeStr
#else
                interpret s' undefined
#endif
    case result of Left err -> throw (InterpreterException err s')
                   Right a -> return a
  s' = s ++ " :: " ++ typeStr
  typeStr = replace ":" "Cons"
          $ replace "[]" "Nil"
          $ show (typeOf (getArg action))

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

instance (SingI xss, All2 Simplifiable xss, SimplEmbed t, Typeable (Tag t xss)) => Simplifiable (Tag t xss) where
  mapleType _ = concat
    [ "Tagged("
    , mapleTypeEmbed (undefined :: t)
    , ","
    , typeList . map typeList . go2 $ (sing :: Sing xss)
    , ")"
    ]

    where
      argOf :: f x -> x
      argOf _ = undefined

      typeList xs = "[" ++ intercalate "," xs ++ "]"

      go2 :: All2 Simplifiable xs => Sing xs -> [[String]]
      go2 SNil = []
      go2 (SCons x xs) = go1 x : go2 xs

      go1 :: All Simplifiable xs => Sing xs -> [String]
      go1 SNil = []
      go1 (SCons x xs) = mapleType (argOf x) : go1 xs

mkTypeString :: (Simplifiable a) => String -> a -> String
mkTypeString s t = "Typed(" ++ s ++ ", " ++ mapleType t ++ ")"

simplify :: (Simplifiable a) => Expect Maple a -> IO (Any a)
simplify e = do
  let slo = toMaple e
  hakaru <- do
    hopeString <- maple ("timelimit(15,Haskell(SLO:-AST(SLO(" ++ slo ++ "))));")
    case readMapleString hopeString of
      Just hakaru -> return hakaru
      Nothing -> throw $ MapleException slo hopeString
  closeLoop ("Any (" ++ hakaru ++ ")")

getArg :: f a -> a
getArg = undefined

toMaple :: (Simplifiable a) => Expect Maple a -> String
toMaple e = mkTypeString (runMaple (unExpect e) 0) (getArg e)
