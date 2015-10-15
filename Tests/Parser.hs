{-# LANGUAGE OverloadedStrings, DataKinds #-}

module Tests.Parser where

import Prelude hiding (unlines)

import Language.Hakaru.Parser.Parser
import Language.Hakaru.Parser.AST

import Data.Text
import Test.HUnit
import Text.Parsec.Error

testParse :: Text -> AST' Text -> Assertion
testParse s p = case parseHakaru s of
                   Left  m  -> assertFailure (show m)
                   Right p' -> assertEqual "" p p'

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

def1 :: Text
def1 = unlines ["def foo(x):"
               ,"    x + 3"
               ,"foo(5)"
               ]

testLams :: Test
testLams = undefined

let1 :: Text
let1 = unlines ["x = 3"
               ,"y = 2"
               ,"x + y"
               ]

testLets :: Test
testLets = undefined

bind1 :: Text
bind1 = unlines ["x <~ uniform(0,1)"
                ,"y <~ normal(x, 1)"
                ,"return y"
                ]

testBinds :: Test
testBinds = undefined

allTests :: Test
allTests = test
   [ testIfs
   , testLams
   , testLets
   , testBinds
   ]


