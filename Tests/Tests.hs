module Main where

import Prelude hiding (Real)

import qualified Tests.ImportanceSampler as IS
import qualified Tests.Metropolis as MH
import qualified Tests.Distribution as D

import Language.Hakaru.Syntax2
import Language.Hakaru.Lambda
import qualified Language.Hakaru.Types as T

import Test.Framework (defaultMain, testGroup)
import Test.Framework.Providers.HUnit

import Test.HUnit

tests = [
        testGroup "Distribution checks" D.qtest,   
        testCase "alwaysPass" (1 @?= 1)
        --testCase "alwaysFail" (error "Fail!")
    ]

main = defaultMain tests