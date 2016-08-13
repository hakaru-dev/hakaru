{-# LANGUAGE CPP,
             OverloadedStrings,
             DataKinds,
             GADTs,
             KindSignatures #-}

----------------------------------------------------------------
--                                                    2016.06.23
-- |
-- Module      :  Language.Hakaru.CodeGen.Wrapper
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  zsulliva@indiana.edu
-- Stability   :  experimental
-- Portability :  GHC-only
--
--   The purpose of the wrapper is to intelligently wrap CStatements
-- into CFunctions and CProgroms to be printed by 'hkc'
--
----------------------------------------------------------------


module Language.Hakaru.CodeGen.Wrapper where

import           Language.Hakaru.Syntax.ABT
import qualified Language.Hakaru.Syntax.AST as T
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Types.Sing

import Language.Hakaru.CodeGen.CodeGenMonad
import Language.Hakaru.CodeGen.HOAS.Declaration
import Language.Hakaru.CodeGen.Flatten
import Language.Hakaru.Types.DataKind (Hakaru(..))

import           Language.C.Data.Ident
import qualified Language.C.Pretty as C

import           Prelude            as P hiding (unlines)
import           Data.Text          as D
import           Text.PrettyPrint (render)

#if __GLASGOW_HASKELL__ < 710
import           Data.Monoid
#endif

-- | Create program is the top level C codegen. Depending on the type a program
--   will have a different construction. HNat will just return while a measure
--   returns a sampling program.
createProgram :: TypedAST (TrivialABT T.Term) -> Text
createProgram (TypedAST tt abt) =
  let ident = builtinIdent "result"
      m = case tt of
           (SData _ _) ->
             do declare $ datumDeclaration tt ident
                expr <- flattenABT abt
                assign ident expr
           (SMeasure internalT) ->
             do declare $ typeDeclaration internalT ident
                expr <- flattenABT abt
                assign ident expr
           _ ->
             do declare $ typeDeclaration tt ident
                expr <- flattenABT abt
                assign ident expr
      (funcs,decls,stmts) = runCodeGen m
  in  unlines [ header tt
              , measureFunc (fmap (\d -> mconcat [cToString d,";"]) decls)
                            (fmap cToString stmts)
              , mainWith tt [] []]

----------------------------------------------------------------


-- | Create function will produce a C function that samples if it is a measure
createFunction :: TypedAST (TrivialABT T.Term) -> Text
createFunction (TypedAST (SFun _ _) abt) = let (fs,_,_) = runCodeGen $ flattenABT abt
                                           in mconcat (fmap cToString fs)
createFunction (TypedAST tt@(SMeasure internalT) abt) =
  let ident           = builtinIdent "result"
      (_,decls,stmts) = runCodeGen (do declare $ typeDeclaration internalT ident
                                       expr <- flattenABT abt
                                       assign ident expr)
  in  unlines [ header tt
              , measureFunc (fmap (\d -> mconcat [cToString d,";"]) decls)
                            (fmap cToString stmts)
              ]
createFunction _ = error $ "createFunction only works on programs of type 'Measure a' and 'Fun a b'"

----------------------------------------------------------------
cToString :: C.Pretty a => a -> Text
cToString = pack . render . C.pretty



header :: Sing (a :: Hakaru) -> Text
header (SMeasure _) = unlines [ "#include <time.h>"
                              , "#include <stdlib.h>"
                              , "#include <stdio.h>"
                              , "#include <math.h>" ]
header _            = unlines [ "#include <stdio.h>"
                              , "#include <math.h>" ]

normalC :: Text
normalC = unlines
        [ "double normal(double mu, double sd) {"
        , "  double u = ((double)rand() / (RAND_MAX)) * 2 - 1;"
        , "  double v = ((double)rand() / (RAND_MAX)) * 2 - 1;"
        , "  double r = u*u + v*v;"
        , "  if (r==0 || r>1) return normal(mu,sd);"
        , "  double c = sqrt(-2 * log(r) / r);"
        , "  return mu + u * c * sd;"
        , "}" ]

measureFunc :: [Text] -> [Text] -> Text
measureFunc decl stmts = unlines
 [ "double measure(){"
 , unlines decl
 , unlines stmts
 , "return result;"
 , "}"
 ]

mainWith :: Sing (a :: Hakaru) -> [Text] -> [Text] -> Text
mainWith typ decl stmts = unlines
 [ "int main(){"
 , case typ of
     SMeasure _ -> "srand(time(NULL));\n"
     _ -> ""
 , unlines decl
 , unlines stmts
 , case typ of
     SMeasure t -> mconcat ["while(1) printf(",printft t,",measure());"]
     _          -> mconcat ["printf(",printft typ,",result);"]
 , "return 0;"
 , "}" ]

printft :: Sing (a :: Hakaru) -> Text
printft SInt         = "\"%d\\n\""
printft SNat         = "\"%d\\n\""
printft SProb        = "\"exp(%.17f)\\n\""
printft SReal        = "\"%.17f\\n\""
printft (SMeasure t) = printft t
printft (SArray t)   = printft t
printft x     = error $ "TODO: printft: " ++ show x
