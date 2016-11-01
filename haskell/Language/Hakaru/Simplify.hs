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
    , simplifyDebug
    , MapleException(MapleException)
    ) where

import Control.Exception
import Control.Monad (when)

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
import System.IO

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
    => abt '[] a -> IO (abt '[] a)
simplify = simplifyDebug False

simplifyDebug
    :: forall abt a
    .  (ABT Term abt) 
    => Bool -> abt '[] a -> IO (abt '[] a)
simplifyDebug debug e = do
    let typ = typeOf e
    let toMaple_ = "use Hakaru, NewSLO in timelimit(90, RoundTrip("
                   ++ Maple.pretty e ++ ", " ++ Maple.mapleType typ ")) end use;"
    when debug (hPutStrLn stderr ("Sent to Maple:\n" ++ toMaple_))
    fromMaple <- maple toMaple_
    case fromMaple of
      '_':'I':'n':'e':'r':'t':_ -> do
        when debug $ do
          ret <- maple ("FromInert(" ++ fromMaple ++ ")")
          hPutStrLn stderr ("Returning from Maple:\n" ++ ret)
        either (throw  . MapleException toMaple_)
               return $ do
          past <- leftShow $ parseMaple (pack fromMaple)
          let m = checkType typ
                   (SR.resolveAST' (getNames e) (maple2AST past))
          leftShow $ unTCM m (freeVars e) Nothing UnsafeMode
      _ -> throw (MapleException toMaple_ fromMaple)

    where
    leftShow :: forall b c. Show b => Either b c -> Either String c
    leftShow (Left err) = Left (show err)
    leftShow (Right x)  = Right x

    getNames :: abt '[] a -> [Name]
    getNames = SR.fromVarSet . freeVars


----------------------------------------------------------------
----------------------------------------------------------- fin.
