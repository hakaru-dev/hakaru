-- | A script for generating unrolled versions of three R2 benchmarks

-- For example, `makeCoinBias 42` will generate a file `CoinBias42.hs`
-- containing an unrolled version of the "coinBias" model that uses an
-- array of length 42

module Unroll where

import Text.PrettyPrint (parens, space, (<+>), punctuate, int, vcat,
                         Doc(..), text, render, ($$), (<>), nest)

       
-- Helpers
----------------------------------------------------------------------

makeNVars :: Int -> String -> [Doc]
makeNVars n var = [text var <> int i | i <- [0..n-1]]

makePair :: String -> Doc -> Doc -> Doc
makePair str a b = text str <+> a $$ b

pair :: Doc -> Doc -> Doc
pair = makePair "pair"

hPair :: Doc -> Doc -> Doc
hPair = makePair "HPair"

nested :: (Doc -> Doc -> Doc) -> [Doc] -> Doc
nested f vars = let ds = punctuate space vars
                in foldr1 (\a -> parens . f a) ds

lastLine :: [Doc] -> String -> Doc
lastLine vars b = text "dirac" <+>
                  parens (pair (nested pair vars) (text b))

model :: Doc -> Doc -> Doc
model a b = text "Model" <+> a $$ b

makeNTypes :: Int -> String -> [Doc]
makeNTypes n typ = replicate n (text typ)                         

decl :: String -> Int -> String -> String -> Doc
decl name n a b =
    let typeDecl = text name <+> text "::" <+>
                   model (nested hPair (makeNTypes n a))
                         (text b)
        nameDecl = text name <+> text "="
    in typeDecl $$ nameDecl

arrow :: Doc
arrow = text "->"

nat :: Int -> Doc
nat i = parens $ text "nat_" <+> int i

whereDef :: [String] -> Doc
whereDef defns = text "where" $$ vcat (map (nest l) (map text defns))
    where l = length "where" + 1



-- Models
----------------------------------------------------------------------              
              
coinBias :: Int -> Doc
coinBias n =
    let firstTwo = decl "coinBias" n "HBool" "'HProb"
        vars = makeNVars n "tossResult"
        prog = vcat $
               [text $ "beta (prob_ 2) (prob_ 5) >>= \\bias ->"] ++
               [text "bern bias >>= \\" <> v <+> arrow | v <- vars] ++
               [lastLine vars "bias"]
    in firstTwo $$ nest 4 prog

digitRecognition :: Int -> Doc
digitRecognition n =
    let firstTwo = decl "digitRecognition" n "HBool" "'HNat"
        vars = makeNVars n "x"
        prog = vcat $
               [text $ "categorical dataPrior >>= \\y ->"] ++
               [text "bern ((dataParams ! y) !" <+> nat i <> text ") >>= \\" <>
                (vars !! i) <+> arrow | i <- [0..n-1]] ++
               [lastLine vars "y"] ++
               [whereDef ["dataPrior  = var (Variable \"dataPrior\"  73 (SArray SProb))",
                          "dataParams = var (Variable \"dataParams\" 41 (SArray (SArray SProb)))"]]
    in firstTwo $$ nest 4 prog

linearRegression :: Int -> Doc
linearRegression n =
    let firstTwo = decl "linearRegression" n "'HReal" "HUnit"
        vars = makeNVars n "y"
        prog = vcat $
               [text "normal (real_ 0) (prob_ 1) >>= \\a ->",
                text "normal (real_ 5) (prob_ 1.825) >>= \\b ->",
                text "gamma (prob_ 1) (prob_ 1) >>= \\invNoise ->"] ++
               [text "normal (a * (dataX !" <+> nat i <>
                text ")) (recip (sqrt invNoise)) >>= \\" <>
                (vars !! i) <+> arrow | i <- [0..n-1]] ++
               [lastLine vars "unit"] ++
               [whereDef ["dataX = var (Variable \"dataX\" 73 (SArray SReal))"]]
    in firstTwo $$ nest 4 prog
               
               

-- Make files
----------------------------------------------------------------------

pragmas :: Doc
pragmas = text "{-# LANGUAGE DataKinds, TypeOperators, OverloadedStrings #-}\n"

moduleName :: String -> Doc
moduleName name = text "module" <+> text name <+> text "where\n"                  

imports :: Doc
imports = vcat $
          [text "import Prelude (print, length, IO)",
           text "import Language.Hakaru.Syntax.Prelude",
           text "import Language.Hakaru.Disintegrate",
           text "import Language.Hakaru.Syntax.ABT",
           text "import Language.Hakaru.Syntax.AST",
           text "import Language.Hakaru.Types.DataKind",
           text "import Language.Hakaru.Types.Sing\n"]

synonyms :: Doc
synonyms = text "type Model a b = TrivialABT Term '[] ('HMeasure (HPair a b))"
           $$ text "type Cond  a b = TrivialABT Term '[] (a ':-> 'HMeasure b)\n"

mainCall :: String -> Doc
mainCall name =
    text "main :: IO ()" $$
    text "main =" <+>
    text "print (length (disintegrate" <+> text name <> text "))\n"

makeCoinBias :: Int -> IO ()
makeCoinBias n =
    let name = "CoinBias" ++ show n
        doc = pragmas $$
              moduleName name $$
              imports $$
              synonyms $$
              coinBias n <> text "\n" $$ 
              mainCall "coinBias"
    in writeFile (name ++ ".hs") (render doc)

makeDigitRecognition :: Int -> IO ()
makeDigitRecognition n =
    let name = "DigitRecognition" ++ show n
        doc = pragmas $$
              moduleName name $$
              imports $$
              synonyms $$
              digitRecognition n <> text "\n" $$ 
              mainCall "digitRecognition"
    in writeFile (name ++ ".hs") (render doc)

makeLinearRegression :: Int -> IO ()
makeLinearRegression n =
    let name = "LinearRegression" ++ show n
        doc = pragmas $$
              moduleName name $$
              imports $$
              synonyms $$
              linearRegression n <> text "\n" $$ 
              mainCall "linearRegression"
    in writeFile (name ++ ".hs") (render doc)
               
main :: IO ()
main = makeCoinBias 5 >>
       makeCoinBias 500
       

