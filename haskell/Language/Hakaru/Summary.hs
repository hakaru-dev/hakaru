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
--                                                    2017.06.19
-- |
-- Module      :  Language.Hakaru.Summary
-- Copyright   :  Copyright (c) 2017 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Take strings from Maple and interpret them in Haskell (Hakaru)
----------------------------------------------------------------
module Language.Hakaru.Summary
    ( summary
    , summaryDebug
    , MapleException(MapleException)
    ) where

import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Command
import Language.Hakaru.Maple 

----------------------------------------------------------------

summary
    :: forall abt a
    .  (ABT Term abt) 
    => abt '[] a -> IO (abt '[] a)
summary = sendToMaple defaultMapleOptions{command=Summarize}

summaryDebug
    :: forall abt a
    .  (ABT Term abt) 
    => Bool -> abt '[] a -> IO (abt '[] a)
summaryDebug d = sendToMaple defaultMapleOptions{command=Summarize,debug=d}

----------------------------------------------------------------
----------------------------------------------------------- fin.
