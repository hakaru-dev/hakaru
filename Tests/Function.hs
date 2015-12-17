{-# LANGUAGE DataKinds, NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Tests.Function (allTests) where

import Prelude ((.), id, ($), asTypeOf)

import Language.Hakaru.Syntax.Prelude
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Syntax.AST (Term)
import Language.Hakaru.Syntax.ABT (ABT)
import Language.Hakaru.Expect     (expect)

import Test.HUnit
import Tests.TestTools

allTests :: Test
allTests = test [
    "t41"            ~: testS t41,
    "pairFun"        ~: testSS [] (pair (lam exp) pi),
    "pairFunSimp"    ~: testSS [pair (lam exp) (lam (log . exp))]
                               (pair (lam exp) (lam id)),
    "unknownMeasure" ~: testSS
        [lam $ \m ->
            normal zero one >>
            asTypeOf m (dirac (pair pi pi))
        ] (lam id)
    ]

t41 :: (ABT Term abt)
    => abt '[] ('HMeasure (('HProb ':-> 'HProb) ':-> 'HProb))
t41 = dirac $ expect (unsafeProb <$> uniform zero (prob_ 2)) lam
