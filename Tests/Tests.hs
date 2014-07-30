module Tests.Tests ( tests ) where

import Prelude hiding (Real)

import qualified Tests.ImportanceSampler as IS
import qualified Tests.Metropolis as MH

import Language.Hakaru.Syntax2
import Language.Hakaru.Lambda
import qualified Language.Hakaru.Types as T

import Distribution.TestSuite as C
-- import Distribution.TestSuite.HUnit as H

tests :: IO [Test]
tests = return [ 
  test "foo" Pass,
  test "bar" (Fail "oops!")
  ]

test :: String -> Result -> Test
test name r = Test t where
  t = TestInstance {
      run = return (Finished r)
    , name = name
    , tags = []
    , options = []
    , setOption = \_ _ -> Right t
  }
