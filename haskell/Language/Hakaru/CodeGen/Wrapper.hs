{-# LANGUAGE BangPatterns,
             CPP,
             OverloadedStrings,
             DataKinds,
             FlexibleContexts,
             GADTs,
             KindSignatures,
             RankNTypes,
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


module Language.Hakaru.CodeGen.Wrapper
  ( wrapProgram ) where

import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Syntax.TypeOf (typeOf)
import           Language.Hakaru.Types.Sing
import           Language.Hakaru.CodeGen.CodeGenMonad
import           Language.Hakaru.CodeGen.Flatten
import           Language.Hakaru.CodeGen.HOAS.Expression
import           Language.Hakaru.CodeGen.HOAS.Statement
import           Language.Hakaru.CodeGen.HOAS.Declaration
import           Language.Hakaru.Types.DataKind (Hakaru(..))


import           Language.C.Data.Ident
import qualified Language.C.Pretty as C
import           Language.C.Syntax.AST

import           Control.Monad.State.Strict
import           Prelude            as P hiding (unlines)
import           Data.Text          as D
import           Text.PrettyPrint (render)

import           Data.Monoid

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative
#endif
                 

-- | Create program is the top level C codegen. Depending on the type a program
--   will have a different construction. HNat will just return while a measure
--   returns a sampling program.
wrapProgram :: TypedAST (TrivialABT Term) -> Maybe String -> Text
wrapProgram tast@(TypedAST typ _) mn = unlines [ header typ
                                               , unlines . mainLast . fmap cToString $ extdecls ]
  where mainLast []     = []
        mainLast (x:xs) = if D.take 10 x == "int main()"
                          then xs <> pure x
                          else pure x <> mainLast xs
        (extdecls,_,_) =
          runCodeGen $
            case (tast,mn) of
              ( TypedAST (SFun _ _) abt, Just name ) ->
                do reserveName name
                   flattenTopLambda abt $ builtinIdent name

              ( TypedAST (SFun _ _) abt, Nothing   ) ->
                genIdent' "fn" >>= flattenTopLambda abt

              ( TypedAST typ'       abt, Just name ) ->
                do reserveName name
                   defineFunction typ
                                  (builtinIdent name)
                                  (putStat . returnS =<< flattenABT abt)

              ( TypedAST typ'       abt, Nothing   ) ->
                mainFunction typ' abt



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


mainFunction
  :: ABT Term abt
  => Sing (a :: Hakaru)
  -> abt '[] (a :: Hakaru)
  -> CodeGen ()
mainFunction typ@(SMeasure _) abt =
  let ident = builtinIdent "measure"
      funId = builtinIdent "main"
  in  do reserveName "measure"
         defineFunction typ ident (putStat . returnS =<< flattenABT abt)

         -- need to set seed
         -- srand(time(NULL));
  
         reserveName "main"
         printf typ (varE ident)
         putStat . returnS $ intConstE 0

         !cg <- get
         extDeclare . extFunc $ functionDef SInt
                                            funId
                                            []
                                            (P.reverse $ declarations cg)
                                            (P.reverse $ statements cg)

mainFunction typ abt =
  let ident = builtinIdent "result"
      funId = builtinIdent "main"
  in  do reserveName "result"
         reserveName "main"

         declare typ ident
         expr <- flattenABT abt
         assign ident expr

         printf typ (varE ident)
         putStat . returnS $ intConstE 0

         cg <- get
         extDeclare . extFunc $ functionDef SInt
                                            funId
                                            []
                                            (P.reverse $ declarations cg)
                                            (P.reverse $ statements cg)

printf :: Sing (a :: Hakaru) -> CExpr -> CodeGen ()
printf (SMeasure t) arg =
  putStat . whileS (intConstE 1) . (:[]) . exprS
    $ callFuncE (varE . builtinIdent $ "printf")
                [ printfText t "\n"
                , callFuncE arg [] ]

printf (SArray t)   arg =
  do iterId <- genIdent' "it"
     declare SInt iterId
     assign iterId (intConstE 0)
     let iter   = varE iterId
         result = varE . builtinIdent $ "result"
         dataPtr = result ^! (builtinIdent "data")
         sizeVar = result ^! (builtinIdent "size")
         cond     = iter ^< sizeVar
         inc      = postInc iter
         currInd  = indirectE (dataPtr ^+ iter)
         loopBody = do putStat . exprS $ callFuncE (varE . builtinIdent $ "printf")
                                                   [ printfText t " ", currInd ]


     putString "[ "
     forCG iter cond inc loopBody
     putString "]\n"
  where putString s = putStat . exprS $ callFuncE (varE . builtinIdent $ "printf")
                                                  [stringE s]

printf typ          arg =
  putStat . exprS $ callFuncE (varE . builtinIdent $ "printf")
                              [ printfText typ "\n"
                              , arg ]


printfText :: Sing (a :: Hakaru) -> (String -> CExpr)
printfText SInt         = \s -> stringE $ "%d" ++ s
printfText SNat         = \s -> stringE $ "%d" ++ s
printfText SProb        = \s -> stringE $ "exp(%.17f)" ++ s
printfText SReal        = \s -> stringE $ "%.17f" ++ s
printfText (SMeasure t) = printfText t
printfText (SArray t)   = printfText t
printfText (SFun _ _)   = \s -> stringE s
printfText (SData _ _)  = \s -> stringE $ "TODO: printft datum" ++ s



flattenTopLambda
  :: ABT Term abt
  => abt '[] a
  -> Ident
  -> CodeGen ()
flattenTopLambda abt name =
    coalesceLambda abt $ \vars abt' ->
    let varMs = foldMap11 (\v -> [mkVarDecl v =<< createIdent v]) vars
    in  do argDecls <- sequence varMs

           cg <- get
           let m       = putStat . returnS =<< flattenABT abt'
               (_,cg') = runState m $ cg { statements = []
                                         , declarations = [] }
           put $ cg' { statements   = statements cg
                     , declarations = declarations cg }

           extDeclare . extFunc $ functionDef (typeOf abt')
                                              name
                                              argDecls
                                              (P.reverse $ declarations cg')
                                              (P.reverse $ statements cg')
  -- do at top level
  where coalesceLambda
          :: ABT Term abt
          => abt '[] a
          -> ( forall (ys :: [Hakaru]) b
             . List1 Variable ys -> abt '[] b -> r)
          -> r
        coalesceLambda abt k =
          caseVarSyn abt (const (k Nil1 abt)) $ \term ->
            case term of
              (Lam_ :$ body :* End) ->
                caseBind body $ \v body' ->
                  coalesceLambda body' $ \vars body'' -> k (Cons1 v vars) body''
              _ -> k Nil1 abt


        mkVarDecl :: Variable (a :: Hakaru) -> Ident -> CodeGen CDecl
        mkVarDecl (Variable _ _ SInt)  = return . typeDeclaration SInt
        mkVarDecl (Variable _ _ SNat)  = return . typeDeclaration SNat
        mkVarDecl (Variable _ _ SProb) = return . typeDeclaration SProb
        mkVarDecl (Variable _ _ SReal) = return . typeDeclaration SReal
        mkVarDecl (Variable _ _ (SArray t)) = \i -> do extDeclare $ arrayStruct t
                                                       return $ arrayDeclaration t i
        mkVarDecl (Variable _ _ d@(SData _ _)) = \i -> do extDeclare $ datumStruct d
                                                          return $ datumDeclaration d i
        mkVarDecl v = error $ "flattenSCon.Lam_.mkVarDecl cannot handle vars of type " ++ show v
