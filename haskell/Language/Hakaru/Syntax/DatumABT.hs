{-# LANGUAGE CPP
           , DataKinds
           , PolyKinds
           , GADTs
           , TypeOperators
           , TypeFamilies
           , ExistentialQuantification
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.05.24
-- |
-- Module      :  Language.Hakaru.Syntax.DatumABT
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Stuff that depends on both "Language.Hakaru.Syntax.ABT" and
-- "Language.Hakaru.Syntax.Datum"; factored out to avoid the cyclic
-- dependency issues.
----------------------------------------------------------------
module Language.Hakaru.Syntax.DatumABT
    ( fromGBranch
    , toGBranch
    ) where

import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.Datum

----------------------------------------------------------------
----------------------------------------------------------------

fromGBranch
    :: (ABT syn abt)
    => GBranch a (abt '[] b)
    -> Branch a abt b
fromGBranch (GBranch pat vars e) =
    Branch pat (binds_ vars e)

toGBranch
    :: (ABT syn abt)
    => Branch a abt b
    -> GBranch a (abt '[] b)
toGBranch (Branch pat body) =
    uncurry (GBranch pat) (caseBinds body)

----------------------------------------------------------------
----------------------------------------------------------- fin.
