{-# LANGUAGE BangPatterns,
             CPP,
             OverloadedStrings,
             DataKinds,
             FlexibleContexts,
             GADTs,
             KindSignatures,
             RankNTypes,
             ScopedTypeVariables,
             TypeOperators #-}

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
     cg <- get
     when (managedMem cg)  $ extDeclare . CPPExt $ gcHeader
     when (sharedMem cg)   $ extDeclare . CPPExt $ openMpHeader
     case (tast,mn) of
       ( TypedAST (SFun _ _) abt, Just name ) ->
         flattenTopLambda abt =<< reserveIdent name

       ( TypedAST typ' abt,       Just name ) ->
         -- still buggy for measures
         do mfId <- reserveIdent name
            funCG (head . buildType $ typ') mfId [] $
              do outE <- flattenWithName' abt "out"
                 putStat . CReturn . Just $ outE

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
  do mfId    <- reserveIdent "measure"
     mdataId <- reserveIdent "mdata"
     mainId  <- reserveIdent "main"
     argVId <- reserveIdent "argv"
     argCId <- reserveIdent "argc"
     let (argCE:argVE:[]) = fmap CVar [argCId,argVId]
     extDeclareTypes typ

     -- defined a measure function that returns mdata
     funCG (head . buildType $ typ) mfId  [] $
       (putStat . CReturn . Just) =<< flattenWithName' abt "samp"

     funCG CInt mainId mainArgs $
       do isManagedMem <- managedMem <$> get
          when isManagedMem (putExprStat gcInit)

          nSamples <- parseNumSamples argCE argVE

          -- need to set seed?
          -- srand(time(NULL));
          putStat $ opComment "Run Hakaru Sampler"
          printCG pconfig typ (CCall (CVar mfId) []) (Just nSamples)
          putStat . CReturn . Just $ intE 0

mainFunction pconfig typ@(SFun _ _) abt =
  coalesceLambda abt $ \vars abt' ->
    do resId  <- reserveIdent "result"
       mainId <- reserveIdent "main"
       argVId <- reserveIdent "argv"
       argCId <- reserveIdent "argc"
       funId  <- genIdent' "fn"
       flattenTopLambda abt funId
       let (resE:funE:argCE:argVE:[]) = fmap CVar [resId,funId,argCId,argVId]
           typ' = typeOf abt'

       funCG CInt mainId mainArgs $
         do isManagedMem <- managedMem <$> get
            when isManagedMem (putExprStat gcInit)
            declare typ' resId

            mns <- maybeNumSamples argCE argVE typ'

            withLambdaDepth' 0 abt $ \d ->
              let argErr 0 = ""
                  argErr n = (argErr (pred n)) ++ "<arg" ++ show n ++ "> " in
                ifCG (argCE .<. (intE (d+1)))
                     (do putExprStat $ printfE
                           [ stringE $ "Usage: %s " ++ argErr d ++ "\n"
                           , (index argVE (intE 0)) ]
                         putExprStat $ mkCallE "abort" [ ])
                     (return ())

            putStat $ opComment "Parse Args"
            argEs <- foldLambdaWithIndex 1 abt $ \i (Variable _ _ t) ->
                       do argE <- localVar' t "arg"
                          parseCG t (index argVE (intE i)) argE
                          return argE

            case typ' of
              SMeasure _ -> do putStat $ opComment "Run Hakaru Sampler"
                               printCG pconfig typ' (CCall funE argEs) mns

              _ -> do putStat $ opComment "Run Hakaru Program"
                      putExprStat $ resE .=. (CCall funE argEs)
                      putStat $ opComment "Print Result"
                      printCG pconfig typ' resE mns

            putStat . CReturn . Just $ intE 0


  where withLambdaDepth'
          :: ABT Term abt
          => Integer
          -> abt '[] a
          -> ( forall (x :: Hakaru)
             .  Integer
             -> CodeGen ())
          -> CodeGen ()
        withLambdaDepth' n abt_ k =
          caseVarSyn abt_
            (const (k n))
            (\term ->
              case term of
                (Lam_ :$ body :* End) ->
                  caseBind body $ \_ abt_' ->
                    withLambdaDepth' (succ n) abt_' k
                _ -> k n)

        maybeNumSamples
          :: CExpr -> CExpr -> Sing (a :: Hakaru) -> CodeGen (Maybe CExpr)
        maybeNumSamples c v (SMeasure _) = Just <$> parseNumSamples c v
        maybeNumSamples _ _ _ = return Nothing

-- just a computation
mainFunction pconfig typ abt =
  do resId  <- reserveIdent "result"
     mainId <- reserveIdent "main"
     let resE  = CVar resId

     funCG CInt mainId [] $
       do declare typ resId

          isManagedMem <- managedMem <$> get
          when isManagedMem (putExprStat gcInit)

          flattenABT abt resE
          printCG pconfig typ resE Nothing
          putStat . CReturn . Just $ intE 0

mainArgs :: [CDecl]
mainArgs = [ CDecl [CTypeSpec CInt]
                   [(CDeclr Nothing (CDDeclrIdent (Ident "argc")), Nothing)]
           , CDecl [CTypeSpec CChar]
                   [(CDeclr (Just (CPtrDeclr []))
                            (CDDeclrArr (CDDeclrIdent (Ident "argv")) Nothing)
                     , Nothing)]
           ]

parseNumSamples :: CExpr -> CExpr -> CodeGen CExpr
parseNumSamples argc argv =
  do itE <- localVar SInt
     outE <- localVar SInt
     putStat $ opComment "Num Samples?"
     putExprStat $ outE .=. (intE (-1))
     forCG (itE .=. (intE 1))
           (itE .<. argc)
           (CUnary CPostIncOp itE)
           (ifCG ((index (index argv itE) (intE 0) .==. (charE '-')) .&&.
                  (index (index argv itE) (intE 1) .==. (charE 'n')))
                 (putExprStat $
                   sscanfE [index argv itE,stringE "-n%d",address outE])
                 (return ()))
     putStat $ opComment "End Num Samples?"
     return outE


--------------------------------------------------------------------------------
--                               Parsing Values                               --
--------------------------------------------------------------------------------

parseCG :: Sing (a :: Hakaru) -> CExpr -> CExpr -> CodeGen CExpr
parseCG (SArray t) from to =
  do fpId <- genIdent' "fp"
     buffId <- genIdent' "buff"
     declare' $ CDecl [CTypeSpec fileT]
                      [(CDeclr (Just (CPtrDeclr []))
                               (CDDeclrIdent fpId)
                               , Nothing)]
     declare' $ CDecl [CTypeSpec CChar]
                      [(CDeclr Nothing
                               (CDDeclrArr (CDDeclrIdent buffId) (Just (intE 1024)))
                               , Nothing)]
     let fpE = CVar fpId
         buffE = CVar buffId
     putExprStat $ fpE .=. (fopenE from (stringE "r"))
     itE <- localVar SNat
     putExprStat $ itE .=. (intE 0)
     whileCG (fgetsE buffE (intE 1024) fpE .!=. nullE)
             (putExprStat $ CUnary CPostIncOp itE)
     putExprStat $ arraySize to .=. itE
     putMallocStat (arrayData to) itE t
     putExprStat $ itE .=. (intE 0)
     putExprStat $ rewindE fpE
     whileCG (fgetsE buffE (intE 1024) fpE .!=. nullE)
             (do checkE <- parseCG t buffE (index (arrayData to) itE)
                 ifCG (checkE .==. (intE 1))
                      (putExprStat $ CUnary CPostIncOp itE)
                      (putExprStat $ CUnary CPostDecOp (arraySize to)))
     putExprStat $ fcloseE fpE
     localVar SNat

parseCG t from to =
  do checkE <- localVar SNat
     putExprStat $ checkE .=. sscanfE [from,stringE . parseFormat $ t,address to]
     case t of
       SProb -> putExprStat $ to .=. logE to
       _ -> return ()
     return checkE

parseFormat :: Sing (a :: Hakaru) -> String
parseFormat SInt  = "%d"
parseFormat SNat  = "%u"
parseFormat SReal = "%lf"
parseFormat SProb = "%lf"
parseFormat t = error $ "parseCG{" ++ show t ++ "}: no available parsing form"


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
  -> Maybe CExpr        -- ^ If measure type, expr for num samples
  -> CodeGen ()
printCG pconfig mtyp@(SMeasure typ) sampleFunc (Just numSamples) =
  do mE <- localVar' mtyp "m"
     itE <- localVar SInt
     putExprStat $ itE .=. numSamples
     whileCG (itE .!=. (intE 0)) $
       do putExprStat $ mE .=. sampleFunc
          printCG pconfig typ (mdataSample mE) Nothing
          ifCG (numSamples .>=. (intE 0))
               (putExprStat $ CUnary CPostDecOp itE)
               (return ())

printCG pconfig (SArray typ) arg Nothing =
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

printCG pconfig SProb arg Nothing =
  putExprStat $ printfE
                      [ stringE $ printFormat pconfig SProb "\n"
                      , if showProbInLog pconfig
                        then arg
                        else expE arg ]

printCG pconfig typ arg Nothing =
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
    let varMs = foldMap11 (\v -> [mkVarDecl v =<< createIdent' "param" v]) vars
        typ   = typeOf abt'
    in  do argDecls <- sequence varMs
           funCG (head . buildType $ typ) name argDecls $
             (putStat . CReturn . Just) =<< flattenWithName' abt' "out"

  -- do at top level
  where mkVarDecl :: Variable (a :: Hakaru) -> Ident -> CodeGen CDecl
        mkVarDecl (Variable _ _ SInt)  = return . typeDeclaration SInt
        mkVarDecl (Variable _ _ SNat)  = return . typeDeclaration SNat
        mkVarDecl (Variable _ _ SProb) = return . typeDeclaration SProb
        mkVarDecl (Variable _ _ SReal) = return . typeDeclaration SReal
        mkVarDecl (Variable _ _ (SArray t)) = \i ->
          extDeclareTypes (SArray t) >> (return $ arrayDeclaration t i)

        mkVarDecl (Variable _ _ d@(SData _ _)) = \i ->
          extDeclareTypes d >> (return $ datumDeclaration d i)

        mkVarDecl v = error $ "flattenSCon.Lam_.mkVarDecl cannot handle vars of type " ++ show v

coalesceLambda
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

foldLambdaWithIndex
  :: ABT Term abt
  => Integer
  -> abt '[] a
  -> ( forall (x :: Hakaru)
     .  Integer
     -> Variable x
     -> CodeGen CExpr)
  -> CodeGen [CExpr]
foldLambdaWithIndex n abt_ k =
  caseVarSyn abt_
    (const (return []))
    (\term ->
      case term of
        (Lam_ :$ body :* End) ->
          caseBind body $ \v abt_' ->
            (do x <- k n v
                xs <- foldLambdaWithIndex (succ n) abt_' k
                return (x:xs))
        _ -> return [])
