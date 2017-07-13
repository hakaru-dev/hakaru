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
           , RecordWildCards
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
    ( simplify, simplifyWithOpts
    , simplify'
    , simplifyDebug
    ) where

import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Command
import Language.Hakaru.Maple 
import Language.Hakaru.Syntax.TypeCheck

----------------------------------------------------------------

simplify
    :: forall abt a
    .  (ABT Term abt) 
    => abt '[] a -> IO (abt '[] a)
simplify = simplifyWithOpts defaultMapleOptions

simplifyWithOpts
    :: forall abt a
    .  (ABT Term abt) 
    => MapleOptions () -> abt '[] a -> IO (abt '[] a)
simplifyWithOpts o = sendToMaple o{command=injCmd Simplify}

simplify'
    :: forall abt a
    .  (ABT Term (abt Term)) 
    => TypedAST (abt Term)  -> IO (TypedAST (abt Term))
simplify' = sendToMaple' defaultMapleOptions{command="Simplify"}

simplifyDebug
    :: forall abt a
    .  (ABT Term abt) 
    => Bool
    -> Int
    -> abt '[] a
    -> IO (abt '[] a)
simplifyDebug d t = sendToMaple defaultMapleOptions{command=injCmd Simplify,
                                                    debug=d,timelimit=t}

----------------------------------------------------------------
----------------------------------------------------------- fin.
