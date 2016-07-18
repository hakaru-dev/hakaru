{-# LANGUAGE CPP,
             DataKinds,
             FlexibleContexts,
             GADTs,
             KindSignatures,
             RankNTypes        #-}

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
  , runCodeGen

  -- effects
  , declare
  , assign
  , funDef
  , putStat
  , putCpp

  , genIdent
  , genIdent'

  -- Hakaru specific
  , createIdent
  , lookupIdent

  -- control mechanisms
  , whileCG
  , doWhileCG
  ) where

import Control.Monad.State

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative ((<$>))
#endif

import Language.Hakaru.Syntax.ABT hiding (var)
import Language.Hakaru.Types.DataKind
import Language.Hakaru.CodeGen.HOAS.Statement

import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Syntax.AST

import Data.Number.Nat (fromNat)
import qualified Data.IntMap as IM
import qualified Data.Set    as S
import qualified Data.Text   as T


node :: NodeInfo
node = undefNode

suffixes :: [String]
suffixes = filter (\n -> not $ elem (head n) ['0'..'9']) names
  where base :: [Char]
        base = ['0'..'9'] ++ ['a'..'z']
        names = [[x] | x <- base] `mplus` (do n <- names
                                              [n++[x] | x <- base])


-- CG after "codegen", holds the state of a codegen computation
data CG = CG { freshNames   :: [String]
             , functions    :: S.Set CFunDef
             , cpp          :: S.Set T.Text
             , declarations :: [CDecl]
             , statements   :: [CStat]    -- statements can include assignments as well as other side-effects
             , varEnv       :: Env      }

emptyCG :: CG
emptyCG = CG suffixes S.empty S.empty [] [] emptyEnv

type CodeGen = State CG

runCodeGen :: CodeGen a -> ([CFunDef],[CDecl], [CStat])
runCodeGen m =
  let (_, cg) = runState m emptyCG
  in  ( S.toList $ functions    cg
      , reverse  $ declarations cg
      , reverse  $ statements   cg )

genIdent :: CodeGen Ident
genIdent = do cg <- get
              put $ cg { freshNames = tail $ freshNames cg }
              return $ builtinIdent $ "_" ++ (head $ freshNames cg)

genIdent' :: String -> CodeGen Ident
genIdent' s = do cg <- get
                 put $ cg { freshNames = tail $ freshNames cg }
                 return $ builtinIdent $ s ++ "_" ++ (head $ freshNames cg)

createIdent :: Variable (a :: Hakaru) -> CodeGen Ident
createIdent var@(Variable name _ _) =
  do cg <- get
     let ident = builtinIdent $ (T.unpack name) ++ "_" ++ (head $ freshNames cg)
         env'  = updateEnv (EAssoc var ident) (varEnv cg)
     put $ cg { freshNames = tail $ freshNames cg
              , varEnv     = env' }
     return ident

lookupIdent :: Variable (a :: Hakaru) -> CodeGen Ident
lookupIdent var = do cg <- get
                     case lookupVar var (varEnv cg) of
                       Nothing -> error $ "lookupIdent: var not found"
                       Just i  -> return i

declare :: CDecl -> CodeGen ()
declare d = do cg <- get
               put $ cg { declarations = d:(declarations cg) }

putStat :: CStat -> CodeGen ()
putStat s = do cg <- get
               put $ cg { statements = s:(statements cg) }

assign :: Ident -> CExpr -> CodeGen ()
assign var expr =
  let assignment = CExpr (Just (CAssign CAssignOp
                                        (CVar var node)
                                        expr
                                        node))
                         node
  in  putStat assignment

funDef :: CFunDef -> CodeGen ()
funDef x = undefined
  -- do cg <- get
  --    put $ cg { functions = functions cg `S.union` (S.singleton x) }

putCpp :: T.Text -> CodeGen ()
putCpp x =
  do cg <- get
     put $ cg { cpp = cpp cg `S.union` (S.singleton x) }


---------
-- ENV --
---------

data EAssoc =
    forall (a :: Hakaru). EAssoc !(Variable a) !Ident

newtype Env = Env (IM.IntMap EAssoc)

emptyEnv :: Env
emptyEnv = Env IM.empty

updateEnv :: EAssoc -> Env -> Env
updateEnv v@(EAssoc x _) (Env xs) =
    Env $ IM.insert (fromNat $ varID x) v xs

lookupVar :: Variable (a :: Hakaru) -> Env -> Maybe Ident
lookupVar x (Env env) = do
    EAssoc _ e' <- IM.lookup (fromNat $ varID x) env
    -- Refl         <- varEq x x' -- extra check?
    return e'

----------------------------------------------------------------

whileCG :: CExpr -> CodeGen () -> CodeGen ()
whileCG bE m = let (_,_,stmts) = runCodeGen m
               in putStat $ whileS bE stmts

doWhileCG :: CExpr -> CodeGen () -> CodeGen ()
doWhileCG bE m = let (_,_,stmts) = runCodeGen m
                 in putStat $ doWhileS bE stmts
