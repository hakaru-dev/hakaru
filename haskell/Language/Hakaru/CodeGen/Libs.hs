----------------------------------------------------------------
--                                                    2016.12.20
-- |
-- Module      :  Language.Hakaru.CodeGen.Libraries
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  zsulliva@indiana.edu
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Bindings to common C libraries
--
----------------------------------------------------------------

module Language.Hakaru.CodeGen.Libs
  ( -- math.h
    expE, expm1E, logE, log1pE, sqrtE,
    infinityE,negInfinityE,

    -- stdio.h
    printfE, sscanfE, fopenE, fcloseE, fileT, feofE, fgetsE, rewindE,

    -- stdlib.h
    randE, srandE, mallocE, freeE,

    -- Boehm Gargbage Collector
    gcHeader, gcInit, gcMalloc,

    -- OpenMP
    openMpHeader, ompGetNumThreads, ompGetThreadNum, OMP(..), Directive(..),
    ompToPP
  ) where

import Language.Hakaru.CodeGen.AST
import Language.Hakaru.CodeGen.Pretty
import Text.PrettyPrint (render)

{-

  As a convention to make the CExpressions standout, functions that return CExpr
  have a suffix 'E' for instance 'printfE'

-}


--------------------------------------------------------------------------------
--                                 Lib C                                      --
--------------------------------------------------------------------------------
{-
  Here we have calls to a very small subset of functionality provided by libc.
  In the future, we should have a standard way to add in bindings to C
  libraries. Easily generating code for existing C libraries is one of the key
  design goals of pedantic-c
-}

------------
-- math.h --
------------

expE,expm1E,logE,log1pE,sqrtE :: CExpr -> CExpr
expE   = mkUnaryE "exp"
expm1E = mkUnaryE "expm1"
logE   = mkUnaryE "log"
log1pE = mkUnaryE "log1p"
sqrtE  = mkUnaryE "sqrt"

infinityE,negInfinityE :: CExpr
infinityE    = (intE 1) ./. (intE 0)
negInfinityE = logE (intE 0)

--------------
-- stdlib.h --
--------------

randE :: CExpr
randE = mkCallE "rand" []

srandE :: CExpr -> CExpr
srandE e = mkCallE "srand" [e]

mallocE :: CExpr -> CExpr
mallocE = mkUnaryE "malloc"

freeE :: CExpr -> CExpr
freeE = mkUnaryE "free"

--------------
-- stdio.h --
--------------

printfE,sscanfE :: [CExpr] -> CExpr
printfE = mkCallE "printf"
sscanfE = mkCallE "sscanf"

fopenE :: CExpr -> CExpr -> CExpr
fopenE e0 e1 = mkCallE "fopen" [e0,e1]

fcloseE,feofE,rewindE :: CExpr -> CExpr
fcloseE e = mkCallE "fclose" [e]
feofE e = mkCallE "feof" [e]
rewindE e = mkCallE "rewind" [e]

fgetsE :: CExpr -> CExpr -> CExpr -> CExpr
fgetsE e0 e1 e2 = mkCallE "fgets" [e0,e1,e2]

fileT :: CTypeSpec
fileT = CTypeDefType (Ident "FILE")

--------------------------------------------------------------------------------
--                            Boehm Garbage Collector                         --
--------------------------------------------------------------------------------
{-
   Currently needed for handling arrays and datum.

   In the future, an intermediate language based on the region calculus will be
   employed here.
-}

gcHeader :: Preprocessor
gcHeader = PPInclude "gc.h"

gcInit :: CExpr
gcInit = mkCallE "GC_INIT" []

gcMalloc :: CExpr -> CExpr
gcMalloc e = mkCallE "GC_MALLOC" [e]

--------------------------------------------------------------------------------
--                                  OpenMP                                    --
--------------------------------------------------------------------------------
{-
   For generating pragmas for shared memory parallelism, that is parallelism on
   on a single process that makes use of multithreaded processors. This
   interface is implemented in most C compilers and is accessed through pragmas

   This is a subset of the the OpenMP 4.5 standard.
-}

openMpHeader :: Preprocessor
openMpHeader = PPInclude "omp.h"

ompGetNumThreads :: CExpr
ompGetNumThreads = mkCallE "omp_get_num_threads" []

ompGetThreadNum :: CExpr
ompGetThreadNum = mkCallE "omp_get_thread_num" []

data OMP = OMP Directive

data Directive
  = Parallel [Directive]
  | For
  | Critical
  | Reduction (Either CBinaryOp Ident) [CExpr]
  | DeclareRed Ident CTypeSpec CExpr CExpr

ompToPP :: OMP -> Preprocessor
ompToPP (OMP d) = PPPragma $ "omp":(showDirective d)
  where showDirective :: Directive -> [String]
        showDirective (Parallel ds)      = "parallel":(concatMap showDirective ds)
        showDirective For                = ["for"]
        showDirective Critical           = ["critical"]
        showDirective (Reduction eop vs) =
          let op = case eop of
                     Left binop -> render . pretty $ binop
                     Right (Ident s) -> s
          in  ["reduction(",op,":",unwords . fmap (render. pretty) $ vs,")"]
        showDirective (DeclareRed (Ident name) typ mul unit) =
          let typ'  = render . pretty $ typ
              mul'  = render . pretty $ mul
              unit' = render . pretty $ unit
          in ["declare","reduction(",name,":",typ',":",mul',") initializer ("
             ,unit',")"]
