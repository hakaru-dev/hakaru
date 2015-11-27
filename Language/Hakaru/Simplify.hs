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
import Language.Hakaru.Any (Any(Any), AnySimplifiable(AnySimplifiable))
import Language.Hakaru.PrettyPrint (pretty)

import Language.Hakaru.Parser.Maple
import Language.Hakaru.Parser.SymbolResolve (resolveAST)

import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.TypeCheck
import Language.Hakaru.Syntax.TypeOf

import Data.Typeable (Typeable)

import Control.Monad.Trans.State.Strict (evalState)

import System.IO (stderr, hPrint, hPutStrLn)
import Data.List (tails, stripPrefix)
import Data.Text (replace, pack, unpack)
import Data.Char (isSpace)
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
    TypedAST typ ast <- closeLoop' hakaru
    -- TODO: convince Haskell I can return ast without typeOf
    case jmEq1 (typeOf e) typ of
      Just Refl  -> return ast
      Nothing    -> return e

 where simplify' :: abt '[] a -> IO String
       simplify' e = do
         let slo = toMaple e
         maple ("timelimit(15,NewSLO:-RoundTripLO(" ++ slo ++ "));")
         -- case readMapleString hopeString of
         --   Just hakaru -> return hakaru
         --   Nothing     -> throw (MapleException slo hopeString)
                          
       closeLoop' :: String -> IO (TypedAST abt)
       closeLoop' s = do
           case parseMaple (pack s) of
             Left err -> throw $ MapleException (toMaple e) (show err)
             Right past ->
                 let m = inferType (resolveAST $ maple2AST past) in
                 case runTCM m LaxMode of
                   Left err -> error (show err)
                   Right e  -> return e

toMaple :: (ABT AST abt) => abt '[] a -> String
toMaple = runMaple 

----------------------------------------------------------------
----------------------------------------------------------- fin.
