{-# LANGUAGE FlexibleInstances
           , FlexibleContexts
           , DeriveDataTypeable
           , DataKinds
           , ScopedTypeVariables
           , RecordWildCards
           , ViewPatterns
           , LambdaCase
           , KindSignatures
           , TypeOperators
           , GADTs
           , RankNTypes
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
  , MapleCommand(MapleCommand)
  , defaultMapleOptions
  , sendToMaple, sendToMaple'
  , maple
  ) where

import Control.Exception (Exception, throw)
import Control.Monad (when)
import Data.Typeable (Typeable)

import qualified Language.Hakaru.Pretty.Maple as Maple

import Language.Hakaru.Parser.Maple
import Language.Hakaru.Parser.AST (Name)
import Language.Hakaru.Pretty.Concrete (prettyType)
import qualified Language.Hakaru.Parser.SymbolResolve as SR
                  (resolveAST', fromVarSet)

import Language.Hakaru.Types.Sing
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Transform
import Language.Hakaru.Syntax.TypeCheck
import Language.Hakaru.Syntax.TypeOf
import Language.Hakaru.Syntax.IClasses

import Language.Hakaru.Evaluation.ConstantPropagation

import System.MapleSSH (maple)
import System.IO
import Data.Text (pack)
import qualified Data.Map as M
import Data.List (isInfixOf, intercalate)
import Data.Char (toLower)
import Data.Function (on)
import Data.Monoid (Monoid(..))
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

----------------------------------------------------------------
data MapleException
  = MapleInterpreterException String String
  | MapleInputTypeMismatch String String
  | MapleUnknownCommand String
  | MapleAmbiguousCommand String [String]
  | MultipleErrors [MapleException]
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
    show (MapleAmbiguousCommand str cmds) =
      concat [ "Ambiguous command\n"
             , str, " could refer to any of\n"
             , intercalate "," cmds ]
    show (MultipleErrors es) =
      concat $ "Multiple errors" : map (("\n\n" ++) . show) es

data MapleOptions nm = MapleOptions 
  { command   :: nm 
  , debug     :: Bool 
  , timelimit :: Int 
  , extraOpts :: M.Map String String 
  , context   :: TransformCtx
  } deriving (Functor, Foldable, Traversable) 

defaultMapleOptions :: MapleOptions () 
defaultMapleOptions = MapleOptions
  { command = ()    
  , debug = False 
  , timelimit = 90
  , extraOpts = M.empty
  , context = mempty }

--------------------------------------------------------------------------------

-- | Maple commands operate on closed terms and take a single argument, and can
--   be applied under functions.
data MapleCommand (i :: Hakaru) (o :: Hakaru) where
  MapleCommand :: !(Transform '[ '( '[], i ) ] o) -> MapleCommand i o
  UnderFun     :: !(MapleCommand i o) -> MapleCommand (x ':-> i) (x ':-> o)

typeOfMapleCommand :: MapleCommand i o -> Sing i -> Sing o
typeOfMapleCommand (MapleCommand t) i =
  typeOfTransform t (Pw (Lift1 ()) i :* End)
typeOfMapleCommand (UnderFun c) (SFun x i) =
  SFun x (typeOfMapleCommand c i)

newtype CommandMatcher
   = CommandMatcher (forall i . Sing i
                             -> Either MapleException (Some1 (MapleCommand i)))

infixl 3 <-|>
(<-|>) :: Either MapleException x
       -> Either MapleException x
       -> Either MapleException x
(<-|>) (Left x) (Left y) =
  Left $ MultipleErrors (unnest x ++ unnest y) where
    unnest (MultipleErrors e) = concatMap unnest e
    unnest                 e  = [e]
(<-|>) Left{}         x  = x
(<-|>) x@Right{}      _  = x

matchUnderFun :: CommandMatcher -> CommandMatcher
matchUnderFun (CommandMatcher k) = CommandMatcher go where
  go :: Sing i -> Either MapleException (Some1 (MapleCommand i))
  go ty@(SFun x i) =
    fmap (\(Some1 c) -> Some1 (UnderFun c)) (go i) <-|>
    k ty
  go ty =
    k ty <-|>
    Left (MapleInputTypeMismatch "x -> y" (show $ prettyType 0 ty))

mapleCommands
  :: [ (String, CommandMatcher) ]
mapleCommands =
  [ ("Simplify"
    , CommandMatcher $ \i -> return $ Some1 $ MapleCommand Simplify)
  , ("Reparam"
    , CommandMatcher $ \i -> return $ Some1 $ MapleCommand Reparam)
  , ("Summarize"
    , CommandMatcher $ \i -> return $ Some1 $ MapleCommand Summarize)
  , ("Disintegrate"
    , matchUnderFun $ CommandMatcher $ \i ->
        case i of
          SMeasure (SData (STyApp (STyApp
              (STyCon (jmEq1 sSymbol_Pair -> Just Refl)) a) b) _) ->
            return $ Some1 $ MapleCommand $ Disint InMaple
          _ -> Left $
                  MapleInputTypeMismatch "measure (pair (a,b))"
                                         (show $ prettyType 0 i))
  ]

matchCommandName :: String -> Sing i
                 -> Either MapleException (Some1 (MapleCommand i))
matchCommandName s i =
  case filter ((isInfixOf `on` map toLower) s . fst) mapleCommands of
    [(_,CommandMatcher m)]
       -> m i
    [] -> Left $ MapleUnknownCommand s
    cs -> Left $ MapleAmbiguousCommand s (map fst cs)

nameOfMapleCommand :: MapleCommand i o -> Either MapleException String
nameOfMapleCommand (MapleCommand t) = nm t where
  nm :: Transform xs x -> Either MapleException String
  nm Simplify         = Right "Simplify"
  nm (Disint InMaple) = Right "Disintegrate"
  nm Summarize        = Right "Summarize"
  nm Reparam          = Right "Reparam"
  nm t                = Left $ MapleUnknownCommand (show t)
nameOfMapleCommand (UnderFun c) = nameOfMapleCommand c

--------------------------------------------------------------------------------

sendToMaple' 
    :: ABT Term (abt Term) 
    => MapleOptions String 
    -> TypedAST (abt Term) 
    -> IO (TypedAST (abt Term))
sendToMaple' o@MapleOptions{..} (TypedAST typ term) = do
  Some1 cmdT <- either throw return $ matchCommandName command typ
  res        <- sendToMaple o{command=cmdT} term
  return $ TypedAST (typeOf res) res

sendToMaple
    :: (ABT Term abt)
    => MapleOptions (MapleCommand i o)
    -> abt '[] i
    -> IO (abt '[] o)
sendToMaple MapleOptions{..} e = do
  nm <- either throw return $ nameOfMapleCommand command
  let typ_in = typeOf e
      typ_out = typeOfMapleCommand command typ_in 
      optStr (k,v) = concat["_",k,"=",v]
      optsStr = 
        intercalate "," $ 
        map optStr $ M.assocs $ 
        M.insert "command" nm extraOpts 
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
                 (SR.resolveAST' (max (nextFreeOrBind e) (nextFreeVar context))
                                 (getNames e) (maple2AST past))
        leftShow $ unTCM m (freeVars e) Nothing UnsafeMode
    _ -> throw (MapleInterpreterException toMaple_ fromMaple)

leftShow :: forall b c. Show b => Either b c -> Either String c
leftShow (Left err) = Left (show err)
leftShow (Right x)  = Right x

getNames :: ABT Term abt => abt '[] a -> [Name]
getNames = SR.fromVarSet . freeVars

----------------------------------------------------------------
----------------------------------------------------------- fin.
