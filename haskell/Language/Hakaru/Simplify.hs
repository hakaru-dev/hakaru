{-# LANGUAGE TypeSynonymInstances
           , FlexibleInstances
           , FlexibleContexts
           , DeriveDataTypeable
           , CPP
           , GADTs
           , DataKinds
           , OverloadedStrings
           , ScopedTypeVariables
           , TypeOperators
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.04.28
-- |
-- Module      :  Language.Hakaru.Simplify
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Take strings from Maple and interpret them in Haskell (Hakaru)
----------------------------------------------------------------
module Language.Hakaru.Simplify
    ( simplify
    , MapleException(MapleException)
    ) where

import Control.Exception

import qualified Language.Hakaru.Pretty.Maple as Maple

import Language.Hakaru.Parser.Maple
import Language.Hakaru.Parser.AST (Name)
import qualified Language.Hakaru.Parser.SymbolResolve as SR (resolveAST', fromVarSet)

import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.TypeCheck
import Language.Hakaru.Syntax.TypeOf

import Data.Typeable (Typeable)

import Data.Text (pack)
import System.MapleSSH (maple)

----------------------------------------------------------------

data MapleException       = MapleException String String
    deriving Typeable

-- Maple prints errors with "cursors" (^) which point to the specific position
-- of the error on the line above. The derived show instance doesn't preserve
-- positioning of the cursor.
instance Show MapleException where
    show (MapleException toMaple_ fromMaple) =
        "MapleException:\n" ++ fromMaple ++
        "\nafter sending to Maple:\n" ++ toMaple_

instance Exception MapleException

simplify
    :: forall abt a
    .  (ABT Term abt) 
    => abt '[] a
    -> IO (abt '[] a)
simplify e = do
    let slo = Maple.pretty e
    let typ = typeOf e          
    hakaru <- maple ("use Hakaru, NewSLO in timelimit(15, RoundTrip("
      ++ slo ++ ", " ++ Maple.mapleType typ ++ ")) end use;")
    either (throw . MapleException slo) return $ do
        past <- leftShow $ parseMaple (pack hakaru)
        let m = checkType typ
                 (SR.resolveAST' (getNames e) (maple2AST past))
        leftShow $ unTCM m (freeVars e) UnsafeMode
            
    where
    leftShow :: forall b c. Show b => Either b c -> Either String c
    leftShow (Left err) = Left (show err)
    leftShow (Right x)  = Right x

    getNames :: abt '[] a -> [Name]
    getNames = SR.fromVarSet . freeVars

----------------------------------------------------------------
----------------------------------------------------------- fin.
