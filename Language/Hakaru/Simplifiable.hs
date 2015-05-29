{-# LANGUAGE ScopedTypeVariables, UndecidableInstances, ConstraintKinds, GADTs, DataKinds, KindSignatures #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Simplifiable (Simplifiable(mapleType)) where

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Hakaru(..), HProxy)
import Language.Hakaru.Embed
import Data.List (intercalate)

-- N.B., we have Typeable (HProxy a) for all @a@
class Simplifiable (a :: Hakaru *) where
  mapleType :: hproxy a -> String

instance Simplifiable HUnit where mapleType _ = "Unit"
instance Simplifiable HInt  where mapleType _ = "Int"
instance Simplifiable HReal where mapleType _ = "Real"
instance Simplifiable HProb where mapleType _ = "Prob"
instance Simplifiable HBool where mapleType _ = "Bool"

instance (Simplifiable a, Simplifiable b) => Simplifiable (HPair a b) where
  mapleType _ = "Pair(" ++ mapleType (undefined :: HProxy a) ++ "," ++
                           mapleType (undefined :: HProxy b) ++ ")"

instance Simplifiable a => Simplifiable (HList a) where
  mapleType _ = "List(" ++ mapleType (undefined :: HProxy a) ++ ")"

instance Simplifiable a => Simplifiable (HMeasure a) where
  mapleType _ = "Measure(" ++ mapleType (undefined :: HProxy a) ++ ")"

instance Simplifiable a => Simplifiable (HArray a) where
  mapleType _ = "MVector(" ++ mapleType (undefined :: HProxy a) ++ ")"

instance (Simplifiable a, Simplifiable b) => Simplifiable (HFun a b) where
  mapleType _ = "Arrow(" ++ mapleType (undefined :: HProxy a) ++ "," ++
                            mapleType (undefined :: HProxy b) ++ ")"

-- Typeable (Tag t xss)
instance (SingI xss, All2 Simplifiable xss, SimplEmbed t) => Simplifiable (HTag t xss) where
  mapleType _ = concat
    [ "Tagged("
    , mapleTypeEmbed (undefined :: t)
    , ","
    , typeList . map typeList . go2 $ (sing :: Sing xss)
    , ")"
    ]

    where
      typeList xs = "[" ++ intercalate "," xs ++ "]"

      go2 :: All2 Simplifiable xs => Sing xs -> [[String]]
      go2 SNil = []
      go2 (SCons x xs) = go1 x : go2 xs

      go1 :: All Simplifiable xs => Sing xs -> [String]
      go1 SNil = []
      go1 (SCons x xs) = mapleType x : go1 xs
