{-# LANGUAGE ScopedTypeVariables, UndecidableInstances, ConstraintKinds, GADTs #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Simplifiable (Simplifiable(mapleType)) where

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Measure, Vector, Prob, Real)
import Language.Hakaru.Embed
import Data.Typeable (Typeable)
import Data.List (intercalate)

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
