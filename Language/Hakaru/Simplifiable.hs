{-# LANGUAGE ScopedTypeVariables, UndecidableInstances, ConstraintKinds, GADTs, DataKinds, KindSignatures #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Simplifiable (Simplifiable(mapleType)) where

import Prelude hiding (Real)
--import Data.Proxy (Proxy(..)) -- Is in Prelude for modern GHC?
import Data.Typeable (Typeable)
import Language.Hakaru.Syntax (Hakaru(..))
import Language.Hakaru.Embed
import Data.List (intercalate)

-- TODO: We used to have @Typeable a@ for all Hakaru types @a@, but now that we've moved them into the @Hakaru*@ kind, now what?
-- N.B., 'Typeable' is polykinded...
class Typeable a => Simplifiable (a :: Hakaru *) where
  mapleType :: proxy a -> String

instance Simplifiable 'HUnit where mapleType _ = "Unit"
instance Simplifiable 'HInt  where mapleType _ = "Int"
instance Simplifiable 'HReal where mapleType _ = "Real"
instance Simplifiable 'HProb where mapleType _ = "Prob"
instance Simplifiable 'HBool where mapleType _ = "Bool"

instance (Simplifiable a, Simplifiable b) => Simplifiable ('HPair a b) where
  mapleType _ = "Pair(" ++ mapleType (Proxy :: Proxy a) ++ "," ++
                           mapleType (Proxy :: Proxy b) ++ ")"

instance Simplifiable a => Simplifiable ('HList a) where
  mapleType _ = "List(" ++ mapleType (Proxy :: Proxy a) ++ ")"

instance Simplifiable a => Simplifiable ('HMeasure a) where
  mapleType _ = "Measure(" ++ mapleType (Proxy :: Proxy a) ++ ")"

instance Simplifiable a => Simplifiable ('HArray a) where
  mapleType _ = "MVector(" ++ mapleType (Proxy :: Proxy a) ++ ")"

instance (Simplifiable a, Simplifiable b) => Simplifiable ('HFun a b) where
  mapleType _ = "Arrow(" ++ mapleType (Proxy :: Proxy a) ++ "," ++
                            mapleType (Proxy :: Proxy b) ++ ")"

-- N.B., we replaced the old @Typeable (Tag t xss)@ requirement by it's two prerequisites, becase otherwise we need to give a kind signature to @xss@ which for some strange reason causes a syntax error
instance (SingI xss, All2 Simplifiable xss, SimplEmbed t, Typeable t, Typeable xss) => Simplifiable ('HTag t xss) where
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
