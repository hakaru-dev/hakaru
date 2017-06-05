{-# LANGUAGE TypeSynonymInstances
           , FlexibleInstances
           , FlexibleContexts
           , DeriveDataTypeable
           , CPP
           , GADTs
           , DataKinds
           , OverloadedStrings
           , ScopedTypeVariables
           , TypeOperators
           , RecordWildCards
           , ViewPatterns
           , KindSignatures
           , RankNTypes
           , TypeApplications
           , MultiParamTypeClasses
           , FunctionalDependencies
           , UndecidableInstances 
           , LambdaCase
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
  ( MapleException(..), MapleInputTypeMismatch(..)
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
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.TypeCheck
import Language.Hakaru.Syntax.TypeOf
import Language.Hakaru.Syntax.Command 

import Language.Hakaru.Evaluation.ConstantPropagation

import Data.Typeable (Typeable)

import System.MapleSSH (maple)
import System.IO
import GHC.TypeLits (Symbol)
import qualified GHC.TypeLits as TL
import Data.Type.Equality 
import Data.Text (pack)

import Data.Foldable (Foldable)
import Data.Traversable (Traversable)


----------------------------------------------------------------
data MapleException       = MapleException String String
    deriving Typeable

data MapleInputTypeMismatch = MapleInputTypeMismatch String String
    deriving Typeable

-- Maple prints errors with "cursors" (^) which point to the specific position
-- of the error on the line above. The derived show instance doesn't preserve
-- positioning of the cursor.
instance Show MapleException where
    show (MapleException toMaple_ fromMaple) =
        "MapleException:\n" ++ fromMaple ++
        "\nafter sending to Maple:\n" ++ toMaple_
instance Exception MapleException

instance Show MapleInputTypeMismatch where
    show (MapleInputTypeMismatch command ty) =
      concat["Maple command ", command, " does not take input of type ", ty] 
instance Exception MapleInputTypeMismatch

data MapleOptions nm = MapleOptions 
  { command   :: nm 
  , debug     :: Bool 
  , timelimit :: Int 
  } deriving (Functor, Foldable, Traversable) 

defaultMapleOptions :: MapleOptions () 
defaultMapleOptions = MapleOptions
  { command = ()    
  , debug = False 
  , timelimit = 90 }

sendToMaple' 
    :: ABT Term (abt Term) 
    => MapleOptions String 
    -> TypedAST (abt Term) 
    -> IO (TypedAST (abt Term))
sendToMaple' MapleOptions{..} (TypedAST ty expr) = 
  someSSymbol command $ \cmd -> 
  commandFromName cmd ty $ \case 
    Nothing        -> throw $ MapleInputTypeMismatch command (show ty) 
    Just (c, ty_o) -> TypedAST ty_o <$> sendToMaple MapleOptions{command=c,..} expr 

sendToMaple  
    :: (ABT Term abt)
    => MapleOptions (CommandType c i o) 
    -> abt '[] i 
    -> IO (abt '[] o)
sendToMaple MapleOptions{..} e = do 
  let typ_in = typeOf e
      typ_out = commandIsType command typ_in 
      commandStr = "_command="++ssymbolVal(nameOfCommand command)
      toMaple_ = "use Hakaru, NewSLO in timelimit("
                 ++ show timelimit ++ ", RoundTrip("
                 ++ Maple.pretty e ++ ", " ++ Maple.mapleType typ_in (", "
                 ++ commandStr ++ ")) end use;")
  when debug (hPutStrLn stderr ("Sent to Maple:\n" ++ toMaple_))
  fromMaple <- maple toMaple_
  case fromMaple of
    '_':'I':'n':'e':'r':'t':_ -> do
      when debug $ do
        ret <- maple ("FromInert(" ++ fromMaple ++ ")")
        hPutStrLn stderr ("Returning from Maple:\n" ++ ret)
      either (throw  . MapleException toMaple_)
             (return . constantPropagation) $ do
        past <- leftShow $ parseMaple (pack fromMaple)
        let m = checkType typ_out
                 (SR.resolveAST' (getNames e) (maple2AST past))
        leftShow $ unTCM m (freeVars e) Nothing UnsafeMode
    _ -> throw (MapleException toMaple_ fromMaple)
  
leftShow :: forall b c. Show b => Either b c -> Either String c
leftShow (Left err) = Left (show err)
leftShow (Right x)  = Right x

getNames :: ABT Term abt => abt '[] a -> [Name]
getNames = SR.fromVarSet . freeVars

----------------------------------------------------------------
----------------------------------------------------------- fin.
