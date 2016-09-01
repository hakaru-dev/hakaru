{-# LANGUAGE CPP,
             OverloadedStrings,
             DataKinds,
             GADTs,
             KindSignatures,
             ScopedTypeVariables #-}

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
import           Language.Hakaru.Syntax.TypeOf (typeOf)                        
import           Language.Hakaru.Types.Sing
import           Language.Hakaru.CodeGen.CodeGenMonad
import           Language.Hakaru.CodeGen.Flatten
import           Language.Hakaru.CodeGen.HOAS.Statement
import           Language.Hakaru.CodeGen.HOAS.Declaration                 
import           Language.Hakaru.Types.DataKind (Hakaru(..))


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
      m = do declare tt ident
             expr <- flattenABT abt
             assign ident expr
      (funcs,decls,stmts) = runCodeGen m
      decls' = fmap (\d -> mconcat [cToString d,";"]) decls
      stmts' = fmap cToString stmts

  in  unlines [ header tt
              , unlines (fmap cToString funcs)
              , case tt of
                 (SFun _ _)   -> ""
                 (SMeasure _) -> unlines [ measureFunc decls' stmts'
                                         , mainWith tt [] []]
                 _ -> mainWith tt decls' stmts'
              ]

----------------------------------------------------------------


-- | Create function will produce a C function that samples if it is a measure
createFunction :: TypedAST (TrivialABT T.Term) -> String -> Text
createFunction (TypedAST tt abt) name =
  let funcId = builtinIdent name
      m = do body <- flattenABT abt
             -- -- cg <- get
             extDeclare . extFunc $ functionDef (typeOf abt)
                                                funcId
                                                []
                                                ([returnS body])

      (funcs,_,_) = runCodeGen m

  in  unlines [ header tt
              , unlines (fmap cToString funcs)
              ]


----------------------------------------------------------------
cToString :: C.Pretty a => a -> Text
cToString = pack . render . C.pretty


-- This should be handled in the CodeGenMonad eventually
header :: Sing (a :: Hakaru) -> Text
header (SMeasure _) = unlines [ "#include <time.h>"
                              , "#include <stdlib.h>"
                              , "#include <stdio.h>"
                              , "#include <math.h>" ]
header _            = unlines [ "#include <stdio.h>"
                              , "#include <stdlib.h>"
                              , "#include <math.h>" ]

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
     SMeasure t -> mconcat ["while(1) printf(\"",printft t,"\\n\",measure());"]
     SArray t   -> unlines ["printf(\"[ \");"
                           ,"for (int i = 0; i < result.size; i++) {"
                           , mconcat ["  printf(\"",printft t," \",*(result.data + i));"]
                           ,"}"
                           ,"printf(\"]\\n\");"]

     _          -> mconcat ["printf(\"",printft typ,"\\n\",result);"]
 , "return 0;"
 , "}" ]

printft :: Sing (a :: Hakaru) -> Text
printft SInt         = "%d"
printft SNat         = "%d"
printft SProb        = "exp(%.17f)"
printft SReal        = "%.17f"
printft (SMeasure t) = printft t
printft (SArray t)   = printft t
printft (SFun _ _)   = ""
printft (SData _ _)  = "TODO: printft datum"
-- printft (SData (STyCon x) _) = printft x
--   where printft' :: Sing (a :: Symbol) -> Text
--         printft' (SingSymbol :: Sing "Unit") = "()\\n"
