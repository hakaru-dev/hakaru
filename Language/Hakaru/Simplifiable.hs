{-# LANGUAGE GADTs
           , KindSignatures
           , DataKinds
           , TypeOperators
           , ConstraintKinds
           , ScopedTypeVariables
           , UndecidableInstances
           , TypeSynonymInstances
           , FlexibleInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.22
-- |
-- Module      :  Language.Hakaru.Simplifiable
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- TODO: remove the use of @-XTypeSynonymInstances@
----------------------------------------------------------------
module Language.Hakaru.Simplifiable (Simplifiable(mapleType)) where

import Data.Proxy (Proxy(..)) -- TODO: Is this in Prelude for modern GHC?
-- import Data.Typeable (Typeable)
-- import Data.List     (intercalate)
import Language.Hakaru.Syntax.DataKind
----------------------------------------------------------------


-- BUG: in order for Simplify.hs's @closeLoop@ to typecheck, we need this class to require @Typeable a@. However, with the new AST's datakind, that means we need Typeable instances for the type-level symbols used by @HData@, which we don't have...
class Simplifiable (a :: Hakaru) where
    mapleType :: proxy a -> String

instance Simplifiable HUnit  where mapleType _ = "Unit"
instance Simplifiable 'HInt  where mapleType _ = "Int"
instance Simplifiable 'HReal where mapleType _ = "Real"
instance Simplifiable 'HProb where mapleType _ = "Prob"
instance Simplifiable HBool  where mapleType _ = "Bool"

instance (Simplifiable a, Simplifiable b) => Simplifiable (HPair a b) where
    mapleType _ =
        "Pair(" ++ mapleType (Proxy :: Proxy a) ++ "," ++
            mapleType (Proxy :: Proxy b) ++ ")"

instance Simplifiable a => Simplifiable (HList a) where
    mapleType _ = "List(" ++ mapleType (Proxy :: Proxy a) ++ ")"

instance Simplifiable a => Simplifiable ('HMeasure a) where
    mapleType _ = "Measure(" ++ mapleType (Proxy :: Proxy a) ++ ")"

instance Simplifiable a => Simplifiable ('HArray a) where
    mapleType _ = "MVector(" ++ mapleType (Proxy :: Proxy a) ++ ")"

instance (Simplifiable a, Simplifiable b) => Simplifiable (a ':-> b) where
    mapleType _ =
        "Arrow(" ++ mapleType (Proxy :: Proxy a) ++ "," ++
            mapleType (Proxy :: Proxy b) ++ ")"

-- N.B., we replaced the old @Typeable (Tag t xss)@ requirement by it's two
-- prerequisites, becase otherwise we need to give a kind signature to @xss@
-- which for some strange reason causes a syntax error

class SimplifiableFun (x :: HakaruFun) where 
    mapleTypeFn :: proxy x -> String

instance SimplifiableFun I where mapleTypeFn _ = "Id" 
instance Simplifiable x => SimplifiableFun (K x) where 
    mapleTypeFn _ = "Konst("  ++ mapleType (Proxy :: Proxy x) ++ ")" 

{-
instance (SingI xss, All2 SimplifiableFun xss, SimplEmbed t, Typeable t, Typeable xss) => Simplifiable (HTag t xss) where
  mapleType _ = concat
    [ "Tagged("
    , mapleTypeEmbed (undefined :: t)
    , ","
    , typeList . map typeList . go2 $ (sing :: Sing xss)
    , ")"
    ]

    where
      typeList xs = "[" ++ intercalate "," xs ++ "]"

      go2 :: All2 SimplifiableFun xs => Sing xs -> [[String]]
      go2 SNil = []
      go2 (SCons x xs) = go1 x : go2 xs

      go1 :: All SimplifiableFun xs => Sing xs -> [String]
      go1 SNil = []
      go1 (SCons x xs) = mapleTypeFn x : go1 xs
-}

----------------------------------------------------------------
----------------------------------------------------------- fin.