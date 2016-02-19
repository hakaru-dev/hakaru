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
--                                                    2015.10.18
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
    , simplifyLam
    , MapleException(MapleException)
    ) where

import Control.Exception

import qualified Language.Hakaru.Pretty.Maple as Maple

import Language.Hakaru.Parser.Maple
import Language.Hakaru.Parser.SymbolResolve (resolveAST)

import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.TypeCheck
import Language.Hakaru.Syntax.TypeOf

import Language.Hakaru.Types.DataKind

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

simplify :: (ABT Term abt) => abt '[] ('HMeasure a) -> IO (abt '[] ('HMeasure a))
simplify e = do
    let slo = Maple.pretty e
    hakaru <- maple ("timelimit(15,NewSLO:-RoundTripLO(" ++ slo ++ "));")
    either (throw . MapleException slo) return $ do
        past <- leftShow $ parseMaple (pack hakaru)
        let m = checkType (typeOf e) (resolveAST $ maple2AST past) 
        leftShow $ unTCM m (freeVars e) UnsafeMode
            
    where
    leftShow :: Show a => Either a b -> Either String b
    leftShow (Left err) = Left (show err)
    leftShow (Right x)  = Right x

simplifyLam :: (ABT Term abt)
            => abt '[] (a ':-> 'HMeasure b)
            -> IO (abt '[] (a ':-> 'HMeasure b))
simplifyLam e = caseVarSyn e (return . var) $ \t ->
                   case t of
                   Lam_ :$ (e1 :* End) ->
                       caseBind e1 $ \x e1' -> do
                           e1'' <- simplify e1'
                           return . syn $
                                  Lam_  :$ (bind x e1'' :* End)
                   _ -> error "TODO: simplifyLam"

----------------------------------------------------------------
----------------------------------------------------------- fin.
