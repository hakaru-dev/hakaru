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
wrapProgram tast@(TypedAST typ _) mn pc =
  do sequence_ . fmap (extDeclare . CPPExt) . header $ typ
     baseCG
     return ()
  where baseCG = case (tast,mn) of
               ( TypedAST (SFun _ retT) abt, Just name ) ->
                 do reserveName name
                    flattenTopLambda abt $ Ident name

               ( TypedAST (SFun _ retT) abt, Nothing   ) ->
                 genIdent' "fn" >>= \name ->
                   flattenTopLambda abt name


  --              ( TypedAST typ'       abt, Just name ) ->
  --                do reserveName name
  --                   defineFunction typ'
  --                                  (Ident name)
  --                                  []
  --                                  (putStat . CReturn . Just =<< flattenABT abt)

               ( TypedAST typ'       abt, Nothing   ) ->
                 mainFunction pc typ' abt



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
mainFunction pc typ@(SMeasure t) abt =
  let ident   = Ident "measure"
      funId   = Ident "main"
      mdataId = Ident "mdata"
  --     isArray = isSArray t
  --     isPlate = isSArray t
  in  do reserveName "measure"
         reserveName "mdata"
         reserveName "main"

         extDeclare . mdataStruct $ t

         -- defined a measure function that returns mdata
         funCG CVoid ident [mdataPtrDeclaration t mdataId] $
           do flattenABT abt (CVar mdataId)
              putStat (CReturn Nothing)

  --        -- need to set seed?
  --        -- srand(time(NULL));

         -- main function

  --        -- if it is a plate then allocate space here
  --        when isArray $
  --          do let arityABT = caseVarSyn abt (error "mainFunction Plate") getPlateArity
  --             aE <- flattenABT arityABT
  --             let dataPtr = CMember (CVar . Ident $ "sample") (Ident "data") True
  --                 size    = CMember (CVar . Ident $ "sample") (Ident "size") True
  --                 innerType = getArrayType t
  --                 mallocCall = CCast (mkPtrDecl innerType)
  --                                    (mkUnary "malloc"
  --                                      (aE .*. (CSizeOfType . mkDecl $ innerType)))
  --             putStat . CExpr . Just $ size .=. aE
  --             putStat . CExpr . Just $ dataPtr .=. mallocCall


         printf pc typ (CVar ident)
         putStat . CReturn . Just $ intE 0

         !cg <- get
         extDeclare . CFunDefExt $ functionDef SInt
                                               funId
                                               []
                                               (P.reverse $ declarations cg)
                                               (P.reverse $ statements cg)
  where isSArray (SArray _) = True
        isSArray _          = False
        mkArrayStruct :: Sing (a :: Hakaru) -> CExtDecl
        mkArrayStruct (SArray t) = arrayStruct t
        mkArrayStruct _          = error "Not Array"
        getArrayType :: Sing (b :: Hakaru) -> [CTypeSpec]
        getArrayType (SArray t) = case buildType t of
                                    [] -> error "wrapper: this shouldn't happen"
                                    t  -> t
        getArrayType _          = error "Not Array"
        getPlateArity :: ABT Term abt => Term abt a -> abt '[] 'HNat
        getPlateArity (Plate :$ arity :* _ :* End) = arity
        getPlateArity _ = error "mainFunction not a plate"

-- just a computation
mainFunction pc typ abt =
  let resId = Ident "result"
      resE  = CVar resId
      funId = Ident "main"
  in  do reserveName "result"
         reserveName "main"

         declare typ resId
         flattenABT abt resE

         printf pc typ resE
         putStat . CReturn . Just $ intE 0

         cg <- get
         extDeclare . CFunDefExt $ functionDef SInt
                                              funId
                                              []
                                              (P.reverse $ declarations cg)
                                              (P.reverse $ statements cg)


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


printf
  :: PrintConfig
  -> Sing (a :: Hakaru) -- ^ Hakaru type to be printed
  -> CExpr              -- ^ CExpr representing value
  -> CodeGen ()

printf pc mt@(SMeasure t) sampleFunc =
  case t of
    -- (SArray _) -> do s <- runCodeGenBlock $ do putStat . CExpr . Just $ CCall arg [sampleELoc]
    --                                            printf t sampleE
    --                  putStat $ CFor Nothing Nothing Nothing s
    _ -> do mId <- genIdent' "m"
            declare mt mId
            let mE = CVar mId
                getSampleS   = CExpr . Just $ CCall sampleFunc [address mE]
                printSampleE = CExpr . Just
                             $ CCall (CVar . Ident $ "printf")
                                     $ [ stringE $ printfText pc mt "\n"]
                                     ++ (if showWeights pc
                                         then [ if showProbInLog pc
                                                then mdataWeight mE
                                                else exp $ mdataWeight mE ]
                                         else [])
                                     ++ [ mdataSample mE ]
                wrapSampleFunc = CCompound $ [CBlockStat getSampleS
                                             ,CBlockStat $ CIf (mdataWeight mE .==. (floatE 0)) printSampleE Nothing]
            putStat $ CWhile (intE 1) wrapSampleFunc False


printf pc (SArray t) arg =
  do iterId <- genIdent' "it"
     declare SInt iterId
     let iter   = CVar iterId
         result = arg
         dataPtr = CMember result (Ident "data") True
         sizeVar = CMember result (Ident "size") True
         cond     = iter .<. sizeVar
         inc      = CUnary CPostIncOp iter
         currInd  = indirect (dataPtr .+. iter)
         loopBody = putExprStat $ CCall (CVar . Ident $ "printf")
                                        [ stringE $ printfText pc t " "
                                        , currInd ]


     putString "[ "
     mkSequential -- cant print arrays in parallel
     forCG (iter .=. (intE 0)) cond inc loopBody
     putString "]\n"
  where putString s = putExprStat $ CCall (CVar . Ident $ "printf")
                                          [stringE s]

printf pc SProb arg =
  putExprStat $ CCall (CVar . Ident $ "printf")
                      [ stringE $ printfText pc SProb "\n"
                      , if showProbInLog pc
                        then arg
                        else exp arg ]

printf pc typ arg =
  putExprStat $ CCall (CVar . Ident $ "printf")
                      [ stringE $ printfText pc typ "\n"
                      , arg ]



printfText :: PrintConfig -> Sing (a :: Hakaru) -> (String -> String)
printfText _ SInt         = \s -> "%d" ++ s
printfText _ SNat         = \s -> "%d" ++ s
printfText c SProb        = \s -> if showProbInLog c
                                  then "exp(%.15f)" ++ s
                                  else "%.15f" ++ s
printfText _ SReal        = \s -> "%.17f" ++ s
printfText c (SMeasure t) = if showWeights c
                            then \s -> if showProbInLog c
                                       then "exp(%.15f) " ++ printfText c t s
                                       else "%.15f " ++ printfText c t s
                            else printfText c t
printfText c (SArray t)   = printfText c t
printfText c (SFun _ _)   = id
printfText c (SData _ _)  = \s -> "TODO: printft datum" ++ s


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
           cg <- get

           case typ of
             -- SMeasure _ -> error "flattenTopLambda: for Measures"
             -- SMeasure _ -> do let m       = putStat . CReturn . Just =<< flattenABT abt'
             --                      (_,cg') = runState m $ cg { statements = []
             --                                                , declarations = [] }
             --                  put $ cg' { statements   = statements cg
             --                            , declarations = declarations cg }
             --                  extDeclare . CFunDefExt
             --                    $ functionDef typ name
             --                                      argDecls
             --                                      (P.reverse $ declarations cg')
             --                                      (P.reverse $ statements cg')
             _ -> do let m       = do outId <- genIdent' "out"
                                      declare (typeOf abt') outId
                                      let outE = CVar outId
                                      flattenABT abt' outE
                                      putStat . CReturn . Just $ outE
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
