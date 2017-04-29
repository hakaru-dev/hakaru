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
  ( wrapProgram
  , PrintConfig(..)
  ) where

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
import           Language.Hakaru.CodeGen.Libs
import           Language.Hakaru.Types.DataKind (Hakaru(..))

import           Control.Monad.State.Strict
import           Prelude            as P hiding (unlines,exp)


#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative
#endif


-- | wrapProgram is the top level C codegen. Depending on the type a program
--   will have a different construction. It will produce an effect in the
--   CodeGenMonad that will produce a standalone C file containing the CPP
--   includes, struct declarations, functions, and sometimes a main.
wrapProgram
  :: TypedAST (TrivialABT Term) -- ^ Some Hakaru ABT
  -> Maybe String               -- ^ Maybe an output name
  -> PrintConfig                -- ^ show weights?
  -> CodeGen ()
wrapProgram tast@(TypedAST typ _) mn pconfig =
  do sequence_ . fmap (extDeclare . CPPExt) . header $ typ
     isManagedMem <- managedMem <$> get
     when isManagedMem $ extDeclare . CPPExt . PPInclude $ "gc.h"
     baseCG
  where baseCG = case (tast,mn) of
               ( TypedAST (SFun _ _) abt, Just name ) ->
                 do reserveName name
                    flattenTopLambda abt $ Ident name

               ( TypedAST (SFun _ _) abt, Nothing   ) ->
                 genIdent' "fn" >>= \name ->
                   flattenTopLambda abt name


               ( TypedAST typ' abt,       Just name ) ->
                 -- still buggy for measures
                 do reserveName name
                    funCG (head . buildType $ typ')
                          (Ident name)
                          []
                          (do outE <- flattenWithName' abt "out"
                              putStat . CReturn . Just $ outE)

               ( TypedAST typ'       abt, Nothing   ) ->
                 mainFunction pconfig typ' abt



header :: Sing (a :: Hakaru) -> [Preprocessor]
header (SMeasure _) = fmap PPInclude ["time.h", "stdlib.h", "stdio.h", "math.h"]
header _            = fmap PPInclude ["stdlib.h", "stdio.h", "math.h"]



--------------------------------------------------------------------------------
--                             A Main Function                                --
--------------------------------------------------------------------------------
{-

Create standalone C program for a Hakaru ABT. This program will also print the
computed value to stdin.

-}

mainFunction
  :: ABT Term abt
  => PrintConfig
  -> Sing (a :: Hakaru)    -- ^ type of program
  -> abt '[] (a :: Hakaru) -- ^ Hakaru ABT
  -> CodeGen ()

-- when measure, compile to a sampler
mainFunction pconfig typ@(SMeasure _) abt =
  do reserveName "measure"
     reserveName "mdata"
     reserveName "main"
     let measureFunId = Ident "measure"
     extDeclareTypes typ

     -- defined a measure function that returns mdata
     funCG (head . buildType $ typ) measureFunId  [] $
       (putStat . CReturn . Just) =<< flattenWithName' abt "samp"

     funCG CInt (Ident "main") [] $
       do isManagedMem <- managedMem <$> get
          when isManagedMem (putExprStat gc_initE)

          -- need to set seed?
          -- srand(time(NULL));
          printCG pconfig typ (CVar measureFunId)
          putStat . CReturn . Just $ intE 0

-- just a computation
mainFunction pconfig typ abt =
  do reserveName "result"
     reserveName "main"
     let resId = Ident "result"
         resE  = CVar resId

     funCG CInt (Ident "main") [] $
       do declare typ resId

          isManagedMem <- managedMem <$> get
          when isManagedMem (putExprStat gc_initE)

          flattenABT abt resE
          printCG pconfig typ resE
          putStat . CReturn . Just $ intE 0


--------------------------------------------------------------------------------
--                               Printing Values                              --
--------------------------------------------------------------------------------
{-

In HKC the printconfig is parsed from the command line. The default being that
we don't show weights and probabilities are printed as normal real values.

-}

data PrintConfig
  = PrintConfig { showWeights   :: Bool
                , showProbInLog :: Bool
                } deriving Show


printCG
  :: PrintConfig
  -> Sing (a :: Hakaru) -- ^ Hakaru type to be printed
  -> CExpr              -- ^ CExpr representing value
  -> CodeGen ()
printCG pconfig mtyp@(SMeasure typ) sampleFunc =
  do mE <- localVar' mtyp "m"
     whileCG (intE 1) $
       do putExprStat $ mE .=. (CCall sampleFunc [])
          printCG pconfig typ (mdataSample mE)

printCG pconfig (SArray typ) arg =
  do itE <- localVar' SInt "it"
     putString "[ "
     mkSequential
     forCG (itE .=. (intE 0))
           (itE .<. (arraySize arg))
           (CUnary CPostIncOp itE)
           (putExprStat
           $ printfE [ stringE $ printFormat pconfig typ " "
                     , index (arrayData arg) itE ])
     putString "]\n"
  where putString s = putExprStat $ printfE [stringE s]

printCG pconfig SProb arg =
  putExprStat $ printfE
                      [ stringE $ printFormat pconfig SProb "\n"
                      , if showProbInLog pconfig
                        then arg
                        else expE arg ]

printCG pconfig typ arg =
  putExprStat $ printfE
              [ stringE $ printFormat pconfig typ "\n"
              , arg ]

printFormat :: PrintConfig -> Sing (a :: Hakaru) -> (String -> String)
printFormat _ SInt         = \s -> "%d" ++ s
printFormat _ SNat         = \s -> "%d" ++ s
printFormat c SProb        = \s -> if showProbInLog c
                                  then "exp(%.15f)" ++ s
                                  else "%.15f" ++ s
printFormat _ SReal        = \s -> "%.17f" ++ s
printFormat c (SMeasure t) = if showWeights c
                            then \s -> if showProbInLog c
                                       then "exp(%.15f) " ++ printFormat c t s
                                       else "%.15f " ++ printFormat c t s
                            else printFormat c t
printFormat c (SArray t)   = printFormat c t
printFormat _ (SFun _ _)   = id
printFormat _ (SData _ _)  = \s -> "TODO: printft datum" ++ s


--------------------------------------------------------------------------------
--                           Wrapping   Lambdas                               --
--------------------------------------------------------------------------------
{-

Lambdas become function in C. The Hakaru ABT only allows one arguement for each
lambda. So at the top level of a Hakaru program that is a function there may be
several nested lambdas. In C however, we can and should coalesce these into one
function with several arguements. This is what flattenTopLambda is for.

-}


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
           funCG (head . buildType $ typ) name argDecls $
             (putStat . CReturn . Just) =<< flattenWithName' abt' "out"

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
        mkVarDecl (Variable _ _ (SArray t)) = \i ->
          extDeclareTypes (SArray t) >> (return $ arrayDeclaration t i)

        mkVarDecl (Variable _ _ d@(SData _ _)) = \i ->
          extDeclareTypes d >> (return $ datumDeclaration d i)

        mkVarDecl v = error $ "flattenSCon.Lam_.mkVarDecl cannot handle vars of type " ++ show v
