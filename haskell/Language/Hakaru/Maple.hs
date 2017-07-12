{-# LANGUAGE FlexibleInstances
           , FlexibleContexts
           , DeriveDataTypeable
           , DataKinds
           , ScopedTypeVariables
           , RecordWildCards
           , ViewPatterns
           , LambdaCase
           , KindSignatures
           , DeriveFunctor, DeriveFoldable, DeriveTraversable
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
-- |
-- Module      :  Language.Hakaru.Maple 
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Take strings from Maple and interpret them in Haskell (Hakaru), 
-- in a type-safe way. 
----------------------------------------------------------------
module Language.Hakaru.Maple 
  ( MapleException(..)
  , MapleOptions(..)
  , defaultMapleOptions
  , sendToMaple, sendToMaple'
  , maple
  ) where 
    
import Control.Exception
import Control.Monad (when)

import qualified Language.Hakaru.Pretty.Maple as Maple

import Language.Hakaru.Parser.Maple
import Language.Hakaru.Parser.AST (Name)
import qualified Language.Hakaru.Parser.SymbolResolve as SR (resolveAST', fromVarSet)

import Language.Hakaru.Types.Sing
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.TypeCheck
import Language.Hakaru.Syntax.TypeOf
import Language.Hakaru.Syntax.Command 

import Language.Hakaru.Evaluation.ConstantPropagation

import Data.Typeable (Typeable)

import System.MapleSSH (maple)
import System.IO
import Data.Text (pack)
import qualified Data.Map as M 
import Data.List (intercalate) 

import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Control.Monad.Except (ExceptT(..), runExceptT)

----------------------------------------------------------------
data MapleException       
  = MapleInterpreterException String String
  | MapleInputTypeMismatch String String
  | MapleUnknownCommand String
      deriving Typeable

instance Exception MapleException

-- Maple prints errors with "cursors" (^) which point to the specific position
-- of the error on the line above. The derived show instance doesn't preserve
-- positioning of the cursor.
instance Show MapleException where
    show (MapleInterpreterException toMaple_ fromMaple) =
        "MapleException:\n" ++ fromMaple ++
        "\nafter sending to Maple:\n" ++ toMaple_
    show (MapleInputTypeMismatch command ty) =
      concat["Maple command ", command, " does not take input of type ", ty] 
    show (MapleUnknownCommand command) = 
      concat["Maple command ", command, " does not exist"] 

data MapleOptions nm = MapleOptions 
  { command   :: nm 
  , debug     :: Bool 
  , timelimit :: Int 
  , extraOpts :: M.Map String String 
  } deriving (Functor, Foldable, Traversable) 

defaultMapleOptions :: MapleOptions () 
defaultMapleOptions = MapleOptions
  { command = ()    
  , debug = False 
  , timelimit = 90
  , extraOpts = M.empty }

sendToMaple' 
    :: ABT Term (abt Term) 
    => MapleOptions String 
    -> TypedAST (abt Term) 
    -> IO (TypedAST (abt Term))
sendToMaple' o@MapleOptions{..} =
  (either throw return =<<) . runExceptT .
  dynCmd command (mapleCommand o)

type MapleCommands = '[ "Simplify", "Disintegrate", "Reparam", "Summarize" ]

mapleCommand
  :: ABT Term abt => MapleOptions o -> DynCommand ('OneOf MapleCommands) abt IO
mapleCommand o = DynCmd $ \c -> sendToMaple o { command = c }

sendToMaple  
    :: (ABT Term abt)
    => MapleOptions (CommandType ('OneOf MapleCommands) i o) 
    -> abt '[] i 
    -> IO (abt '[] o)
sendToMaple MapleOptions{command=OneOfCmds _ command,..} e = do 
  let typ_in = typeOf e
      typ_out = commandIsType command typ_in 
      optStr (k,v) = concat["_",k,"=",v]
      optsStr = 
        intercalate "," $ 
        map optStr $ M.assocs $ 
        M.insert "command" (ssymbolVal(nameOfCommand command)) extraOpts 
      toMaple_ = "use Hakaru, NewSLO in timelimit("
                 ++ show timelimit ++ ", RoundTrip("
                 ++ Maple.pretty e ++ ", " ++ Maple.mapleType typ_in (", "
                 ++ optsStr ++ ")) end use;")
  when debug (hPutStrLn stderr ("Sent to Maple:\n" ++ toMaple_))
  fromMaple <- maple toMaple_
  case fromMaple of
    '_':'I':'n':'e':'r':'t':_ -> do
      when debug $ do
        ret <- maple ("FromInert(" ++ fromMaple ++ ")")
        hPutStrLn stderr ("Returning from Maple:\n" ++ ret)
      either (throw  . MapleInterpreterException toMaple_)
             (return . constantPropagation) $ do
        past <- leftShow $ parseMaple (pack fromMaple)
        let m = checkType typ_out
                 (SR.resolveAST' (getNames e) (maple2AST past))
        leftShow $ unTCM m (freeVars e) Nothing UnsafeMode
    _ -> throw (MapleInterpreterException toMaple_ fromMaple)
  
leftShow :: forall b c. Show b => Either b c -> Either String c
leftShow (Left err) = Left (show err)
leftShow (Right x)  = Right x

getNames :: ABT Term abt => abt '[] a -> [Name]
getNames = SR.fromVarSet . freeVars

----------------------------------------------------------------
----------------------------------------------------------- fin.
