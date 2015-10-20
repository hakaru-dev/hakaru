{-# LANGUAGE OverloadedStrings, DataKinds #-}

module Tests.Parser where

import Prelude hiding (unlines)

import Language.Hakaru.Parser.Parser
import Language.Hakaru.Parser.AST

import Data.Text
import Test.HUnit
import Text.Parsec.Error

stripMetadata :: AST' Text -> AST' Text
stripMetadata (WithMeta ast m) = ast
stripMetadata ast              = ast

testParse :: Text -> AST' Text -> Assertion
testParse s p = case parseHakaru s of
                   Left  m  -> assertFailure (show m)
                   Right p' -> assertEqual "" p (stripMetadata p')

if1, if2, if3, if4, if5 :: Text

if1 = "if True: 1 else: 2"

if2 = unlines ["if True: 1 else:"
              ,"2"
              ] 

if3 = unlines ["if True:"
              ,"  1"
              ,"else:"
              ,"  2"
              ]

if4 = unlines ["if True:"
              ,"  1 else: 2"
              ]

if5 = unlines ["if True:"
              ,"   4"
              ,"else:"
              ,"   if False:"
              ,"      2"
              ,"   else:"
              ,"      3"
              ]

ifAST1 = App (App (App (Op "if")
                       (Op "True"))
                  (Value (Nat 1)))
              (Value (Nat 2))

ifAST2 = App (App (App (Op "if")
                           (Op "True"))
              (Value (Nat 4)))
         (App (App (App (Op "if")
                            (Op "False"))
               (Value (Nat 2)))
          (Value (Nat 3)))

testIfs :: Test
testIfs = test
   [ testParse if1 ifAST1
   , testParse if2 ifAST1
   , testParse if3 ifAST1
   , testParse if4 ifAST1
   , testParse if5 ifAST2
   ]

lam1 :: Text
lam1 = "fn x: x+3"

lam1AST = Lam "x" (App (App (Op "+")
                        (Var "x"))
                   (Value (Nat 3)))

def1 :: Text
def1 = unlines ["def foo(x):"
               ,"    x + 3"
               ,"foo(5)"
               ]

def1AST = Let "foo"
              (Lam "x" (App (App (Op "+")
                             (Var "x"))
                        (Value (Nat 3))))
              (App (Op "foo") (Value (Nat 5)))

testLams :: Test
testLams = test
   [ testParse lam1 lam1AST
   , testParse def1 def1AST
   ]

let1 :: Text
let1 = unlines ["x = 3"
               ,"y = 2"
               ,"x + y"
               ]

let1AST = Let "x" (Value (Nat 3))
          (Let "y" (Value (Nat 2))
           (App (App (Op "+")
                 (Var "x"))
            (Var "y")))

testLets :: Test
testLets = test
   [ testParse let1 let1AST ]

bind1 :: Text
bind1 = unlines ["x <~ uniform(0,1)"
                ,"y <~ normal(x, 1)"
                ,"dirac(y)"
                ]

bind2 :: Text
bind2 = unlines ["x <~ uniform(0,1)"
                ,"y <~ normal(x, 1)"
                ,"return y"
                ]


bind1AST = Bind "x" (App (App (Op "uniform")
                          (Value (Nat 0)))
                     (Value (Nat 1)))
           (Bind "y" (App (App (Op "normal")
                           (Var "x"))
                      (Value (Nat 1)))
            (App (Op "dirac") (Var "y")))

testBinds :: Test
testBinds = test
   [ testParse bind1 bind1AST
   , testParse bind2 bind1AST
   ]

easyRoad1 :: Text
easyRoad1 = unlines ["noiseT <~ uniform(3, 8)"
                    ,"noiseE <~ uniform(1, 4)"
                    ,"x1 <~ normal( 0, noiseT)"
                    ,"m1 <~ normal(x1, noiseE)"
                    ,"x2 <~ normal(x1, noiseT)"
                    ,"m2 <~ normal(x2, noiseE)"
                    ,"return ((m1, m2), (noiseT, noiseE))"
                    ]

easyRoadAST :: AST' Text
easyRoadAST = Bind "noiseT" (App (App (Op "uniform")
                                          (Value (Nat 3)))
                                          (Value (Nat 8)))
              (Bind "noiseE" (App (App (Op "uniform")
                                           (Value (Nat 1)))
                              (Value (Nat 4)))
               (Bind "x1" (App (App (Op "normal")
                                        (Value (Nat 0)))
                                        (Var "noiseT"))
                (Bind "m1" (App (App (Op "normal")
                                         (Var "x1"))
                                         (Var "noiseE"))
                 (Bind "x2" (App (App (Op "normal")
                                          (Var "x1"))
                                          (Var "noiseT"))
                  (Bind "m2" (App (App (Op "normal")
                                           (Var "x2"))
                                           (Var "noiseE"))
                   (App (Op "dirac")
                            (App (App (Op "Pair")
                                          (App (App (Op "Pair")
                                                        (Var "m1"))
                                                        (Var "m2")))
                                           (App (App (Op "Pair")
                                                         (Var "noiseT"))
                                                         (Var "noiseE")))))))))

testRoadmap :: Test
testRoadmap = test
   [ testParse easyRoad1 easyRoadAST
--   , testParse easyRoad2 easyRoad2AST
   ]

allTests :: Test
allTests = test
   [ testIfs
   , testLams
   , testLets
   , testBinds
   , testRoadmap
   ]


