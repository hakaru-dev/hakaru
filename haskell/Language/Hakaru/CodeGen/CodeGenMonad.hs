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
  , emptyCG

  -- codegen effects
  , declare
  , declare'
  , assign
  , putStat
  , extDeclare
  , defineFunction
  , runCodeGenBlock

  , reserveName
  , genIdent
  , genIdent'

  -- Hakaru specific
  , createIdent
  , lookupIdent

  -- control mechanisms
  , whileCG
  , doWhileCG
  , forCG
  ) where

import Control.Monad.State.Strict

#if __GLASGOW_HASKELL__ < 710
import Data.Monoid (Monoid(..))
import Control.Applicative ((<$>))
#endif

import Language.Hakaru.Syntax.ABT hiding (var)
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing
import Language.Hakaru.CodeGen.HOAS.Declaration
import Language.Hakaru.CodeGen.HOAS.Statement

import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Syntax.AST

import Data.Number.Nat (fromNat)
import qualified Data.IntMap.Strict as IM
import qualified Data.Text          as T
import qualified Data.Set           as S

suffixes :: [String]
suffixes = filter (\n -> not $ elem (head n) ['0'..'9']) names
  where base :: [Char]
        base = ['0'..'9'] ++ ['a'..'z']
        names = [[x] | x <- base] `mplus` (do n <- names
                                              [n++[x] | x <- base])


-- CG after "codegen", holds the state of a codegen computation
data CG = CG { freshNames    :: [String]
             , reservedNames :: S.Set String
             , extDecls      :: S.Set CExtDecl
             , declarations  :: [CDecl]
             , statements    :: [CStat]    -- statements can include assignments as well as other side-effects
             , varEnv        :: Env      }

emptyCG :: CG
emptyCG = CG suffixes mempty mempty [] [] emptyEnv

type CodeGen = State CG

runCodeGen :: CodeGen a -> ([CExtDecl],[CDecl], [CStat])
runCodeGen m =
  let (_, cg) = runState m emptyCG
  in  ( S.toList $ extDecls     cg
      , reverse  $ declarations cg
      , reverse  $ statements   cg )


runCodeGenBlock :: CodeGen a -> CodeGen CStat
runCodeGenBlock m =
  do cg <- get
     let (_,cg') = runState m $ cg { statements = []
                                   , declarations = [] }
     put $ cg' { statements   = statements cg
               , declarations = declarations cg }
     return $ (CCompound [] ((fmap CBlockDecl (reverse $ declarations cg'))
                            ++ (fmap CBlockStmt (reverse $statements cg'))) undefNode)



reserveName :: String -> CodeGen ()
reserveName s =
  get >>= \cg -> put $ cg { reservedNames = s `S.insert` reservedNames cg }


genIdent :: CodeGen Ident
genIdent =
  do cg <- get
     let (freshNs,name) = pullName (freshNames cg) (reservedNames cg)
     put $ cg { freshNames = freshNs }
     return $ builtinIdent name
  where pullName :: [String] -> S.Set String -> ([String],String)
        pullName (n:names) reserved =
          let name = "_" ++ n in
          if S.member name reserved
          then let (names',out) = pullName names reserved
               in  (n:names',out)
          else (names,name)
        pullName _ _ = error "should not happen, names is infinite"

genIdent' :: String -> CodeGen Ident
genIdent' s =
  do cg <- get
     let (freshNs,name) = pullName (freshNames cg) (reservedNames cg)
     put $ cg { freshNames = freshNs }
     return $ builtinIdent name
  where pullName :: [String] -> S.Set String -> ([String],String)
        pullName (n:names) reserved =
          let name = s ++ "_" ++ n in
          if S.member name reserved
          then let (names',out) = pullName names reserved
               in  (n:names',out)
          else (names,name)
        pullName _ _ = error "should not happen, names is infinite"



createIdent :: Variable (a :: Hakaru) -> CodeGen Ident
createIdent var@(Variable name _ _) =
  do !cg <- get
     let ident = builtinIdent $ (T.unpack name) ++ "_" ++ (head $ freshNames cg)
         env'  = updateEnv var ident (varEnv cg)
     put $! cg { freshNames = tail $ freshNames cg
               , varEnv     = env' }
     return ident

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
declare SInt          = declare' . typeDeclaration SInt
declare SNat          = declare' . typeDeclaration SNat
declare SProb         = declare' . typeDeclaration SProb
declare SReal         = declare' . typeDeclaration SReal
declare (SMeasure x)  = declare x
declare (SArray t)    = \i -> do extDeclare $ arrayStruct t
                                 declare'   $ arrayDeclaration t i
declare d@(SData _ _) = \i -> do extDeclare $ datumStruct d
                                 declare'   $ datumDeclaration d i
declare (SFun _ _)    = \_ -> return () -- function definitions handeled in flatten


declare' :: CDecl -> CodeGen ()
declare' d = do cg <- get
                put $ cg { declarations = d:(declarations cg) }

putStat :: CStat -> CodeGen ()
putStat s = do cg <- get
               put $ cg { statements = s:(statements cg) }

assign :: Ident -> CExpr -> CodeGen ()
assign v e = putStat (assignS v e)


extDeclare :: CExtDecl -> CodeGen ()
extDeclare d = do cg <- get
                  put $ cg { extDecls = d `S.insert` extDecls cg }

defineFunction :: Sing (a :: Hakaru) -> Ident -> [CDecl] -> CodeGen () -> CodeGen ()
defineFunction typ ident args mbody =
  do cg <- get
     mbody
     !cg' <- get
     let decls = reverse . declarations $ cg'
         stmts = reverse . statements   $ cg'
         def SInt         = functionDef SInt  ident args decls stmts
         def SNat         = functionDef SNat  ident args decls stmts
         def SProb        = functionDef SProb ident args decls stmts
         def SReal        = functionDef SReal ident args decls stmts
         def (SMeasure t) = functionDef t ident args decls stmts
         def t            = error $ "TODO: defined function of type: " ++ show t

     -- reset local statements and declarations
     put $ cg' { statements   = statements cg
               , declarations = declarations cg }
     extDeclare . extFunc $ def typ


--------------------------------------------------------------------------------
-- CODE

data CCode :: * where
  CPP         :: String -> CCode
  Statement   :: CStat  -> CCode
  Declaration :: CDecl  -> CCode


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

whileCG :: CExpr -> CodeGen () -> CodeGen ()
whileCG bE m =
  let (_,_,stmts) = runCodeGen m
  in putStat $ whileS bE stmts

doWhileCG :: CExpr -> CodeGen () -> CodeGen ()
doWhileCG bE m =
  let (_,_,stmts) = runCodeGen m
  in putStat $ doWhileS bE stmts

forCG :: CExpr -> CExpr -> CExpr -> CodeGen () -> CodeGen ()
forCG iter cond inc body =
  do cg <- get
     let (_,cg') = runState body $ cg { statements = [] }
     put $ cg' { statements = statements cg }
     putStat $ forS iter cond inc (reverse $ statements cg')


----------------------------------------------------------------
-- Deriving Eq instances for C ASTs

-- this is done in this module because the CodeGen monad is the
-- only thing that cares about the uniqueness of generated code
-- Orphaned instances beware

deriving instance Eq (CExternalDeclaration NodeInfo)
deriving instance Eq (CDeclaration NodeInfo)
deriving instance Eq (CStringLiteral NodeInfo)
deriving instance Eq (CExpression NodeInfo)
deriving instance Eq (CFunctionDef NodeInfo)
deriving instance Eq (CInitializer NodeInfo)
deriving instance Eq (CDeclarator NodeInfo)
deriving instance Eq (CDerivedDeclarator NodeInfo)
deriving instance Eq (CPartDesignator NodeInfo)
deriving instance Eq (CDeclarationSpecifier NodeInfo)
deriving instance Eq (CTypeSpecifier NodeInfo)
deriving instance Eq (CTypeQualifier NodeInfo)
deriving instance Eq (CAttribute NodeInfo)
deriving instance Eq (CStatement NodeInfo)
deriving instance Eq (CArraySize NodeInfo)
deriving instance Eq (CStructureUnion NodeInfo)
deriving instance Eq (CConstant NodeInfo)
deriving instance Eq (CEnumeration NodeInfo)
deriving instance Eq (CCompoundBlockItem NodeInfo)
deriving instance Eq (CBuiltinThing NodeInfo)
deriving instance Eq (CAssemblyStatement NodeInfo)
deriving instance Eq (CAssemblyOperand NodeInfo)

deriving instance Ord (CExternalDeclaration NodeInfo)
deriving instance Ord (CDeclaration NodeInfo)
deriving instance Ord (CStringLiteral NodeInfo)
deriving instance Ord (CExpression NodeInfo)
deriving instance Ord (CFunctionDef NodeInfo)
deriving instance Ord (CInitializer NodeInfo)
deriving instance Ord (CDeclarator NodeInfo)
deriving instance Ord (CDerivedDeclarator NodeInfo)
deriving instance Ord (CPartDesignator NodeInfo)
deriving instance Ord (CDeclarationSpecifier NodeInfo)
deriving instance Ord (CTypeSpecifier NodeInfo)
deriving instance Ord (CTypeQualifier NodeInfo)
deriving instance Ord (CAttribute NodeInfo)
deriving instance Ord (CStatement NodeInfo)
deriving instance Ord (CArraySize NodeInfo)
deriving instance Ord (CStructureUnion NodeInfo)
deriving instance Ord (CConstant NodeInfo)
deriving instance Ord (CEnumeration NodeInfo)
deriving instance Ord (CCompoundBlockItem NodeInfo)
deriving instance Ord (CBuiltinThing NodeInfo)
deriving instance Ord (CAssemblyStatement NodeInfo)
deriving instance Ord (CAssemblyOperand NodeInfo)
deriving instance Ord CStructTag
