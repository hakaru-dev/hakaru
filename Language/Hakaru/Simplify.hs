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
    , openLoop
    , main
    , Simplifiable(mapleType)
    , MapleException(MapleException)
    ) where

import Control.Exception

import Language.Hakaru.Simplifiable (Simplifiable(mapleType))
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

import Language.Hakaru.Util.Lex (readMapleString)
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
    -- TODO: convince Haskell I can return ast
    return e

 where simplify' :: abt '[] a -> IO String
       simplify' e = do
         let slo = toMaple e
         hopeString <- maple ("timelimit(15,NewSLO:-RoundTripLO(" ++ slo ++ "));")
         case readMapleString hopeString of
           Just hakaru -> return hakaru
           Nothing     -> throw (MapleException slo hopeString)
                          
       closeLoop' :: String -> IO (TypedAST abt)
       closeLoop' s = do
           case parseMaple (pack s) of
             Left err -> error (show err)
             Right past ->
                 let m = inferType (resolveAST $ maple2AST past) in
                 case runTCM m LaxMode of
                   Left err -> error (show err)
                   Right e  -> return e

toMaple :: (ABT AST abt) => abt '[] a -> String
toMaple = runMaple 

main :: IO ()
main = action `catch` handler0 where
    action :: IO ()
    action = do
        s <- readFile "/tmp/t" -- getContents
        let (before, middle, after) = trim s
        middle' <- undefined -- simplifyAny middle
        putStr (before ++ middle' ++ after)

    handler0 :: SomeException -> IO ()
    handler0 = hPrint stderr

trim :: String -> (String, String, String)
trim s =
    let (before, s') = span isSpace s
        (after', middle') = span isSpace (reverse s')
    in (before, reverse middle', reverse after')

openLoop :: [String] -> String -> IO ([String], AnySimplifiable)
openLoop names s =
    fmap ((,) names) (undefined {- closeLoop ("AnySimplifiable (" ++ s ++ ")") -})

----------------------------------------------------------------
----------------------------------------------------------- fin.
