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
import           Language.Hakaru.CodeGen.Types
import           Language.Hakaru.CodeGen.AST
import           Language.Hakaru.Types.DataKind (Hakaru(..))

import           Control.Monad.State.Strict
import           Prelude            as P hiding (unlines)


#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative
#endif


-- | Create program is the top level C codegen. Depending on the type a program
--   will have a different construction. HNat will just return while a measure
--   returns a sampling program.
wrapProgram :: TypedAST (TrivialABT Term) -> Maybe String -> CAST
wrapProgram tast@(TypedAST typ _) mn = CAST $ fmap CPPExt (header typ) ++ extdecls
  where (extdecls,_,_) =
          runCodeGen $
            case (tast,mn) of
              ( TypedAST (SFun _ _) abt, Just name ) ->
                do reserveName name
                   flattenTopLambda abt $ Ident name

              ( TypedAST (SFun _ _) abt, Nothing   ) ->
                genIdent' "fn" >>= flattenTopLambda abt

              ( TypedAST typ'       abt, Just name ) ->
                do reserveName name
                   defineFunction typ'
                                  (Ident name)
                                  []
                                  (putStat . CReturn . Just =<< flattenABT abt)

              ( TypedAST typ'       abt, Nothing   ) ->
                mainFunction typ' abt



----------------------------------------------------------------

header :: Sing (a :: Hakaru) -> [Preprocessor]
header (SMeasure _) = fmap PPInclude ["time.h", "stdlib.h", "stdio.h", "math.h"]
header _            = fmap PPInclude ["stdlib.h", "stdio.h", "math.h"]

mainFunction
  :: ABT Term abt
  => Sing (a :: Hakaru)
  -> abt '[] (a :: Hakaru)
  -> CodeGen ()
mainFunction typ@(SMeasure t) abt =
  let ident = Ident "measure"
      funId = Ident "main"
  in  do reserveName "measure"
         reserveName "sample"
         let body      = do putStat . CReturn . Just =<< flattenABT abt
             sample    = Ident "sample"
             samplePtr = typePtrDeclaration t sample
         defineFunction typ ident [samplePtr] body

         declare t sample

         -- need to set seed
         -- srand(time(NULL));


         -- insert main function
         reserveName "main"
         printf typ (CVar ident)
         putStat . CReturn . Just $ intE 0

         !cg <- get
         extDeclare . CFunDefExt $ functionDef SInt
                                               funId
                                               []
                                               (P.reverse $ declarations cg)
                                               (P.reverse $ statements cg)

mainFunction typ abt =
  let ident = Ident "result"
      funId = Ident "main"
  in  do reserveName "result"
         reserveName "main"

         declare typ ident
         expr <- flattenABT abt
         assign ident expr

         printf typ (CVar ident)
         putStat . CReturn . Just $ intE 0

         cg <- get
         extDeclare . CFunDefExt $ functionDef SInt
                                              funId
                                              []
                                              (P.reverse $ declarations cg)
                                              (P.reverse $ statements cg)

printf :: Sing (a :: Hakaru) -> CExpr -> CodeGen ()

printf (SMeasure t) arg =
  let sample              = CVar . Ident $ "sample"
      sampleLoc           = address sample
      stat typ@(SArray _) = do mId <- genIdent' "meas"
                               declare typ mId
                               runCodeGenBlock (do assign mId $ CCall arg []
                                                   printf typ (CVar mId))
      stat typ = return . CExpr . Just $ CCall (CVar . Ident $ "printf")
                                               [ printfText typ "\n"
                                              , sample ]
  in do s <- stat t
        putStat $ CWhile (intE 1)
                         (CCompound . fmap CBlockStat $ [CExpr . Just $ CCall arg [sampleLoc]
                                                        , s])
                         False

printf (SArray t)   arg =
  do iterId <- genIdent' "it"
     declare SInt iterId
     let iter   = CVar iterId
         result = arg
         dataPtr = CMember result (Ident "data") True
         sizeVar = CMember result (Ident "size") True
         cond     = iter .<. sizeVar
         inc      = CUnary CPostIncOp iter
         currInd  = indirect (dataPtr .+. iter)
         loopBody = do putStat . CExpr . Just $ CCall (CVar . Ident $ "printf")
                                                      [ printfText t " ", currInd ]


     putString "[ "
     forCG (iter .=. (intE 0)) cond inc loopBody
     putString "]\n"
  where putString s = putStat . CExpr . Just $ CCall (CVar . Ident $ "printf")
                                                     [stringE s]

printf typ          arg =
  putStat . CExpr . Just $ CCall (CVar . Ident $ "printf")
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
           let m       = putStat . CReturn . Just =<< flattenABT abt'
               (_,cg') = runState m $ cg { statements = []
                                         , declarations = [] }
           put $ cg' { statements   = statements cg
                     , declarations = declarations cg }

           extDeclare . CFunDefExt $ functionDef (typeOf abt')
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
        coalesceLambda abt_ k =
          caseVarSyn abt_ (const (k Nil1 abt_)) $ \term ->
            case term of
              (Lam_ :$ body :* End) ->
                caseBind body $ \v body' ->
                  coalesceLambda body' $ \vars body'' -> k (Cons1 v vars) body''
              _ -> k Nil1 abt_


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
