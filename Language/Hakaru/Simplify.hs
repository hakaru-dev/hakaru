{-# LANGUAGE TypeSynonymInstances
           , FlexibleInstances
           , FlexibleContexts
           , DeriveDataTypeable
           , CPP
           , GADTs
           , DataKinds
           , OverloadedStrings
           , ScopedTypeVariables
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.18
-- |
-- Module      :  Language.Hakaru.Simplify
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Take strings from Maple and interpret them in Haskell (Hakaru)
----------------------------------------------------------------
module Language.Hakaru.Simplify
    ( simplify
    , toMaple
    , MapleException(MapleException)
    ) where

import Control.Exception

import Language.Hakaru.MapleNeue (Maple, runMaple)

import Language.Hakaru.Parser.Maple
import Language.Hakaru.Parser.SymbolResolve (resolveAST)

import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.TypeCheck
import Language.Hakaru.Syntax.TypeOf

import Data.Typeable (Typeable)

import Data.Text (replace, pack)
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

simplify :: forall abt a. (ABT AST abt) => abt '[] a -> IO (abt '[] a)
simplify e = do
    hakaru <- simplify' e
    closeLoop' hakaru

 where simplify' :: abt '[] a -> IO String
       simplify' e = do
         let slo = toMaple e
         maple ("timelimit(15,NewSLO:-RoundTripLO(" ++ slo ++ "));")
                          
       closeLoop' :: String -> IO (abt '[] a)
       closeLoop' s = do
           case parseMaple (pack s) of
             Left err -> throw $ MapleException (toMaple e) (show err)
             Right past ->
                 let m = checkType (typeOf e) (resolveAST $ maple2AST past)
                 in case runTCM m LaxMode of
                   Left err -> throw $ MapleException (toMaple e) (show err)
                   Right e  -> return e

toMaple :: (ABT AST abt) => abt '[] a -> String
toMaple = runMaple 

----------------------------------------------------------------
----------------------------------------------------------- fin.
