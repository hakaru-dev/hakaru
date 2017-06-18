{-# LANGUAGE CPP,
             BangPatterns,
             DataKinds,
             FlexibleContexts,
             FlexibleInstances,
             GADTs,
             KindSignatures,
             PolyKinds,
             StandaloneDeriving,
             TypeOperators,
             RankNTypes        #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

----------------------------------------------------------------
--                                                    2016.07.01
-- |
-- Module      :  Language.Hakaru.CodeGen.CodeGenMonad
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  zsulliva@indiana.edu
-- Stability   :  experimental
-- Portability :  GHC-only
--
--   This module provides a monad for C code generation as well
-- as some useful helper functions for manipulating it
----------------------------------------------------------------


module Language.Hakaru.CodeGen.CodeGenMonad
  ( CodeGen
  , CG(..)
  , runCodeGen
  , runCodeGenBlock
  , runCodeGenWith
  , emptyCG

  -- codegen effects
  , declare
  , declare'
  , assign
  , putStat
  , putExprStat
  , extDeclare
  , extDeclareTypes

  , funCG
  , isParallel
  , mkParallel
  , mkSequential

  , reserveIdent
  , genIdent
  , genIdent'

  -- Hakaru specific
  , createIdent
  , createIdent'
  , lookupIdent

  -- control mechanisms
  , ifCG
  , whileCG
  , doWhileCG
  , forCG
  , reductionCG
  , codeBlockCG

  -- memory
  , putMallocStat
  ) where

import Control.Monad.State.Strict

#if __GLASGOW_HASKELL__ < 710
import Data.Monoid (Monoid(..))
import Control.Applicative ((<$>))
#endif

import Language.Hakaru.Syntax.ABT hiding (var)
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing
import Language.Hakaru.CodeGen.Types
import Language.Hakaru.CodeGen.AST
import Language.Hakaru.CodeGen.Pretty
import Language.Hakaru.CodeGen.Libs

import Data.Number.Nat (fromNat)
import qualified Data.IntMap.Strict as IM
import qualified Data.Text          as T
import qualified Data.Set           as S

import Text.PrettyPrint (render)

-- CG after "codegen", holds the state of a codegen computation
data CG = CG { freshNames    :: [String]     -- ^ fresh names for code generations
             , reservedNames :: S.Set String -- ^ reserve names during code generations
             , extDecls      :: [CExtDecl]   -- ^ total external declarations
             , declarations  :: [CDecl]      -- ^ declarations in local block
             , statements    :: [CStat]      -- ^ statements can include assignments as well as other side-effects
             , varEnv        :: Env          -- ^ mapping between Hakaru vars and codegeneration vars
             , managedMem    :: Bool         -- ^ garbage collected block
             , sharedMem     :: Bool         -- ^ shared memory supported block
             , distributed   :: Bool         -- ^ distributed supported block
             , logProbs      :: Bool         -- ^ true by default, but might not matter in some situations
             }

emptyCG :: CG
emptyCG = CG cNameStream mempty mempty [] [] emptyEnv False False False True

type CodeGen = State CG

runCodeGen :: CodeGen a -> ([CExtDecl],[CDecl], [CStat])
runCodeGen m =
  let (_, cg) = runState m emptyCG
  in  ( reverse $ extDecls     cg
      , reverse $ declarations cg
      , reverse $ statements   cg )


runCodeGenBlock :: CodeGen a -> CodeGen CStat
runCodeGenBlock m =
  do cg <- get
     let (_,cg') = runState m $ cg { statements = []
                                   , declarations = [] }
     put $ cg' { statements   = statements cg
               , declarations = declarations cg' ++ declarations cg
               }
     return . CCompound . fmap CBlockStat . reverse . statements $ cg'

runCodeGenWith :: CodeGen a -> CG -> [CExtDecl]
runCodeGenWith cg start = let (_,cg') = runState cg start in reverse $ extDecls cg'

--------------------------------------------------------------------------------

isParallel :: CodeGen Bool
isParallel = sharedMem <$> get

mkParallel :: CodeGen ()
mkParallel =
  do cg <- get
     put (cg { sharedMem = True } )

mkSequential :: CodeGen ()
mkSequential =
  do cg <- get
     put (cg { sharedMem = False } )

--------------------------------------------------------------------------------

reserveIdent :: String -> CodeGen Ident
reserveIdent s = do
  get >>= \cg -> put $ cg { reservedNames = s `S.insert` reservedNames cg }
  return (Ident s)


genIdent :: CodeGen Ident
genIdent = genIdent' ""

genIdent' :: String -> CodeGen Ident
genIdent' s =
  do cg <- get
     let (freshNs,name) = pullName (freshNames cg) (reservedNames cg)
     put $ cg { freshNames = freshNs }
     return $ Ident name
  where pullName :: [String] -> S.Set String -> ([String],String)
        pullName (n:names) reserved =
          let name = s ++ "_" ++ n in
          if S.member name reserved
          then let (names',out) = pullName names reserved
               in  (n:names',out)
          else (names,name)
        pullName _ _ = error "should not happen, names is infinite"



createIdent :: Variable (a :: Hakaru) -> CodeGen Ident
createIdent = createIdent' ""

createIdent' :: String -> Variable (a :: Hakaru) -> CodeGen Ident
createIdent' s var@(Variable name _ _) =
  do !cg <- get
     let ident = Ident $ concat [concatMap toAscii . T.unpack $ name
                                ,"_",s,"_",head $ freshNames cg ]
         env'  = updateEnv var ident (varEnv cg)
     put $! cg { freshNames = tail $ freshNames cg
               , varEnv     = env' }
     return ident
  where toAscii c = let num = fromEnum c in
                    if num < 48 || num > 122
                    then "u" ++ (show num)
                    else [c]

lookupIdent :: Variable (a :: Hakaru) -> CodeGen Ident
lookupIdent var =
  do !cg <- get
     let !env = varEnv cg
     case lookupVar var env of
       Nothing -> error $ "lookupIdent: var not found --" ++ show var
       Just i  -> return i

-- | types like SData and SMeasure are impure in that they will produce extra
--   code in the CodeGenMonad while literal types SReal, SInt, SNat, and SProb
--   do not
declare :: Sing (a :: Hakaru) -> Ident -> CodeGen ()
declare SInt  = declare' . typeDeclaration SInt
declare SNat  = declare' . typeDeclaration SNat
declare SProb = declare' . typeDeclaration SProb
declare SReal = declare' . typeDeclaration SReal
declare m@(SMeasure t) = \i ->
  extDeclareTypes m >> (declare' $ mdataDeclaration t i)

declare a@(SArray t) = \i ->
  extDeclareTypes a >> (declare' $ arrayDeclaration t i)

declare d@(SData _ _)  = \i ->
  extDeclareTypes d >> (declare' $ datumDeclaration d i)

declare f@(SFun _ _) = \_ ->
  extDeclareTypes f >> return ()
  -- this currently avoids declaration if the type is a lambda, this is hacky

-- | for types that contain subtypes we need to recursively traverse them and
--   build up a list of external type declarations.
--   For example: Measure (Array Nat) will need to have structures for arrays
--   declared before the top level type
extDeclareTypes :: Sing (a :: Hakaru) -> CodeGen ()
extDeclareTypes SInt          = return ()
extDeclareTypes SNat          = return ()
extDeclareTypes SReal         = return ()
extDeclareTypes SProb         = return ()
extDeclareTypes (SMeasure i)  = extDeclareTypes i >> extDeclare (mdataStruct i)
extDeclareTypes (SArray i)    = extDeclareTypes i >> extDeclare (arrayStruct i)
extDeclareTypes (SFun x y)    = extDeclareTypes x >> extDeclareTypes y
extDeclareTypes d@(SData _ i) = extDeclDatum i    >> extDeclare (datumStruct d)
  where extDeclDatum :: Sing (a :: [[HakaruFun]]) -> CodeGen ()
        extDeclDatum SVoid       = return ()
        extDeclDatum (SPlus p s) = extDeclDatum s >> datumProdTypes p

        datumProdTypes :: Sing (a :: [HakaruFun]) -> CodeGen ()
        datumProdTypes SDone     = return ()
        datumProdTypes (SEt x p) = datumProdTypes p >> datumPrimTypes x

        datumPrimTypes :: Sing (a :: HakaruFun) -> CodeGen ()
        datumPrimTypes SIdent     = return ()
        datumPrimTypes (SKonst s) = extDeclareTypes s

declare' :: CDecl -> CodeGen ()
declare' d = do cg <- get
                put $ cg { declarations = d:(declarations cg) }

putStat :: CStat -> CodeGen ()
putStat s = do cg <- get
               put $ cg { statements = s:(statements cg) }

putExprStat :: CExpr -> CodeGen ()
putExprStat = putStat . CExpr . Just

assign :: Ident -> CExpr -> CodeGen ()
assign ident e = putStat . CExpr . Just $ (CVar ident .=. e)


extDeclare :: CExtDecl -> CodeGen ()
extDeclare d = do cg <- get
                  let extds = extDecls cg
                      extds' = if elem d extds
                               then extds
                               else d:extds
                  put $ cg { extDecls = extds' }

funCG :: CTypeSpec -> Ident -> [CDecl] -> CodeGen () -> CodeGen ()
funCG ts ident args m =
  do cg <- get
     let (_,cg') = runState m $ cg { statements   = []
                                   , declarations = []
                                   , freshNames   = cNameStream }
     let decls = reverse . declarations $ cg'
         stmts = reverse . statements   $ cg'
     -- reset local statements and declarations
     put $ cg' { statements   = statements cg
               , declarations = declarations cg
               , freshNames   = freshNames cg }
     extDeclare . CFunDefExt $
       CFunDef [CTypeSpec ts]
               (CDeclr Nothing (CDDeclrIdent ident))
               args
               (CCompound ((fmap CBlockDecl decls) ++ (fmap CBlockStat stmts)))




---------
-- ENV --
---------

newtype Env = Env (IM.IntMap Ident)
  deriving Show

emptyEnv :: Env
emptyEnv = Env IM.empty

updateEnv :: Variable (a :: Hakaru) -> Ident -> Env -> Env
updateEnv (Variable _ nat _) ident (Env env) =
  Env $! IM.insert (fromNat nat) ident env

lookupVar :: Variable (a :: Hakaru) -> Env -> Maybe Ident
lookupVar (Variable _ nat _) (Env env) =
  IM.lookup (fromNat nat) env

----------------------------------------------------------------
-- Control Flow

ifCG :: CExpr -> CodeGen () -> CodeGen () -> CodeGen ()
ifCG bE m1 m2 =
  do cg <- get
     let (_,cg') = runState m1 $ cg { statements   = []
                                    , declarations = [] }
         (_,cg'') = runState m2 $ cg' { statements   = []
                                      , declarations = [] }
         thnBlock =  (fmap CBlockDecl (reverse $ declarations cg'))
                  ++ (fmap CBlockStat (reverse $ statements cg'))
         elsBlock =  (fmap CBlockDecl (reverse $ declarations cg'')
                  ++ (fmap CBlockStat (reverse $ statements cg'')))
     put $ cg'' { statements = statements cg
                , declarations = declarations cg }
     putStat $ CIf bE
                   (CCompound thnBlock)
                   (case elsBlock of
                      [] -> Nothing
                      _  -> Just . CCompound $ elsBlock)

whileCG' :: Bool -> CExpr -> CodeGen () -> CodeGen ()
whileCG' isDoWhile bE m =
  do cg <- get
     let (_,cg') = runState m $ cg { statements = []
                                   , declarations = [] }
     put $ cg' { statements = statements cg
               , declarations = declarations cg }
     putStat $ CWhile bE
                      (CCompound $ (fmap CBlockDecl (reverse $ declarations cg')
                                ++ (fmap CBlockStat (reverse $ statements cg'))))
                      isDoWhile
whileCG :: CExpr -> CodeGen () -> CodeGen ()
whileCG = whileCG' False

doWhileCG :: CExpr -> CodeGen () -> CodeGen ()
doWhileCG = whileCG' True

-- forCG and reductionCG both create C for loops, their difference lies in the
-- parallel code they generate
forCG
  :: CExpr
  -> CExpr
  -> CExpr
  -> CodeGen ()
  -> CodeGen ()
forCG iter cond inc body =
  do cg <- get
     let (_,cg') = runState body $ cg { statements = []
                                      , declarations = []
                                      , sharedMem = False }
     put $ cg' { statements   = statements cg
               , declarations = declarations cg
               , sharedMem    = sharedMem cg } -- only use pragmas at the top level
     par <- isParallel
     when par . putStat . CPPStat . ompToPP $ OMP (Parallel [For])
     putStat $ CFor (Just iter)
                    (Just cond)
                    (Just inc)
                    (CCompound $  (fmap CBlockDecl (reverse $ declarations cg')
                               ++ (fmap CBlockStat (reverse $ statements cg'))))

{-
The operation for a reduction is either a builtin binary op, or must be
specified
-}
reductionCG
  :: Either CBinaryOp (CExpr -> CExpr -> CExpr)
  -> Ident
  -> CExpr
  -> CExpr
  -> CExpr
  -> CodeGen ()
  -> CodeGen ()
reductionCG op acc iter cond inc body =
  do cg <- get
     let (_,cg') = runState body $ cg { statements = []
                                      , declarations = []
                                      , sharedMem = False } -- only use pragmas at the top level
     put $ cg' { statements   = statements cg
               , declarations = declarations cg
               , sharedMem    = sharedMem cg }
     par <- isParallel
     when par $
       case op of
         Left binop -> putStat . CPPStat . ompToPP $
                         OMP (Parallel [For,Reduction (Left binop) [CVar acc]])
         -- INCOMPLETE
         Right red  -> do redId@(Ident redName) <- genIdent' "red"
                          let declRedPragma = [ "omp","declare","reduction("
                                              , redName,":",undefined,":"
                                              , render . pretty $
                                                  red (CVar . Ident $ "omp_in")
                                                      (CVar . Ident $ "omp_out")
                                              , ")"]
                          putStat . CPPStat . PPPragma $ declRedPragma
                          putStat . CPPStat . ompToPP $
                            OMP (Parallel [For,Reduction (Right redId) [CVar acc]])
     putStat $ CFor (Just iter)
                    (Just cond)
                    (Just inc)
                    (CCompound $  (fmap CBlockDecl (reverse $ declarations cg')
                               ++ (fmap CBlockStat (reverse $ statements cg'))))


-- not control flow, but like these it creates a block with local variables
codeBlockCG :: CodeGen () -> CodeGen ()
codeBlockCG body =
  do cg <- get
     let (_,cg') = runState body $ cg { statements = []
                                      , declarations = [] }
     put $ cg' { statements = statements cg
               , declarations = declarations cg }
     putStat $ (CCompound $  (fmap CBlockDecl (reverse $ declarations cg')
                          ++ (fmap CBlockStat (reverse $ statements cg'))))



--------------------------------------------------------------------------------
-- ^ Takes a cexpression for the location and size and a hakaru type, and
--   generates a statement for allocating the memory
putMallocStat :: CExpr -> CExpr -> Sing (a :: Hakaru) -> CodeGen ()
putMallocStat loc size typ = do
  isManagedMem <- managedMem <$> get
  let malloc' = if isManagedMem then gcMalloc else mallocE
      typ' = buildType typ
  putExprStat $   loc
              .=. ( CCast (CTypeName typ' True)
                  $ malloc' (size .*. (CSizeOfType (CTypeName typ' False))))
