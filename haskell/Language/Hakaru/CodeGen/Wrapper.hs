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
wrapProgram :: TypedAST (TrivialABT Term) -> Maybe String -> CodeGen ()
wrapProgram tast@(TypedAST typ _) mn =
  do sequence_ . fmap (extDeclare . CPPExt) . header $ typ
     baseCG
     return ()
  where baseCG = case (tast,mn) of
               ( TypedAST (SFun _ retT) abt, Just name ) ->
                 do reserveName name
                    case retT of
                      SMeasure _ -> do reserveName "sample"
                                       putSample (Sample (Ident "sample") undefined)
                                       flattenTopLambda abt $ Ident name
                      _          -> flattenTopLambda abt $ Ident name

               ( TypedAST (SFun _ retT) abt, Nothing   ) ->
                 genIdent' "fn" >>= \name ->
                   case retT of
                     SMeasure _ -> do reserveName "sample"
                                      putSample (Sample (Ident "sample") undefined)
                                      flattenTopLambda abt name
                     _          -> flattenTopLambda abt name


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
         sampleId <- genIdent' "s"
         let samplePtr = typePtrDeclaration t sampleId
         putSample $ Sample sampleId (undefined :: CExpr)

         -- defined a measure function that returns a Double
         defineFunction SProb ident [samplePtr]
           $ do wE <- flattenABT abt
                (Sample i sE) <- getSample
                putStat . CExpr . Just $ (indirect . CVar $ i) .=. sE
                putStat . CReturn . Just $ wE

         -- need to set seed?
         -- srand(time(NULL));

         -- main function
         reserveName "main"

         -- get a place to return a sample
         reserveName "sample"
         declare t (Ident "sample")
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
  let sampleE              = CVar . Ident $ "sample"
      sampleELoc           = address sampleE

  in  case t of
        (SArray _) -> do mId <- genIdent' "plate"
                         declare t mId
                         s <- runCodeGenBlock $ printf t (CVar mId)
                         mpB <- isOpenMP
                         when mpB . putStat . CPPStat . PPPragma
                           $ ["omp","parallel","for"]
                         putStat $ CFor Nothing Nothing Nothing
                                     $ CCompound . fmap CBlockStat
                                        $ [ CExpr . Just $ CCall arg [sampleELoc]
                                          , s ]

        _ -> do -- Need to have space for #NUMTHREADS samples
                -- mpB <- isOpenMP
                -- when mpB . putStat . CPPStat . PPPragma
                --   $ ["omp","parallel","for"]
                putStat $ CFor Nothing Nothing Nothing
                            $ CCompound . fmap CBlockStat
                                $ [ CExpr . Just $ CCall arg [sampleELoc]
                                  , CExpr . Just $ CCall (CVar . Ident $ "printf")
                                                         [ printfText t "\n"
                                                         , sampleE ]]

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
        typ   = typeOf abt'
    in  do argDecls <- sequence varMs
           cg <- get

           case typ of
             SMeasure _ -> do let m       = putStat . CReturn . Just =<< flattenABT abt'
                                  (_,cg') = runState m $ cg { statements = []
                                                            , declarations = [] }
                              put $ cg' { statements   = statements cg
                                        , declarations = declarations cg }
                              extDeclare . CFunDefExt
                                $ functionDef typ name
                                                  argDecls
                                                  (P.reverse $ declarations cg')
                                                  (P.reverse $ statements cg')
             _ -> do let m       = putStat . CReturn . Just =<< flattenABT abt'
                         (_,cg') = runState m $ cg { statements = []
                                                   , declarations = [] }
                     put $ cg' { statements   = statements cg
                               , declarations = declarations cg }
                     extDeclare . CFunDefExt
                       $ functionDef typ name
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
