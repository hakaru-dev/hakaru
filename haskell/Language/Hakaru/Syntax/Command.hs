{-# LANGUAGE FlexibleInstances
           , GADTs
           , DataKinds
           , TypeOperators
           , ViewPatterns
           , KindSignatures
           , RankNTypes
           , UndecidableInstances
           , ScopedTypeVariables
           , ConstraintKinds
           , PolyKinds
           , TypeFamilies
           , DefaultSignatures
           , FlexibleContexts
           , StandaloneDeriving
           , MultiParamTypeClasses
           , OverlappingInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
-- |
-- Module      :  Language.Hakaru.Syntax.Command  
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- An encoding of (some) Hakaru commands and their types. 
----------------------------------------------------------------
module Language.Hakaru.Syntax.Command
  ( module Language.Hakaru.Syntax.Command
  , Symbol
  , Some1(..) )
  where

import Language.Hakaru.Types.Sing
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.AST.Transforms (underLam')
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.TypeCheck (TypedAST(..))
import Language.Hakaru.Pretty.Concrete (prettyType)

import GHC.Exts (Constraint)
import GHC.TypeLits (Symbol, KnownSymbol, symbolVal)

import Control.Exception (Exception)
import Control.Monad.Identity (Identity(..))
import Control.Monad.Except (ExceptT(..), runExcept, MonadError(..))
import Control.Monad.Trans (MonadTrans(..))
import Control.Monad (liftM)
import Data.Functor.Compose (Compose(..))

import Data.List (isInfixOf, intercalate)
import Data.Char (toLower)
import Data.Function (on)
import Data.Typeable (Typeable, Proxy(..))
import Data.Either (isRight)

----------------------------------------------------------------

-- | The family of inputs and outputs of commands
data family CommandType (c :: k) (i :: Hakaru) (o :: Hakaru)

-- | Injective version of `CommandSpec' which also packs the instance
data CommandSpec (c :: k) where
  CmdSpec :: IsCommand c => CommandSpec' c -> CommandSpec c

-- | Either a string representing a type, or a type itself
type HakaruTypeRep = Either String (Some1 (Sing :: Hakaru -> *))

-- | Possible errors when matching commands
data CommandMatchError
  = AmbiguousCommandName String [SomeCommand]
  | UnknownCommandName String [SomeCommand] -- | Expected command name
                                            -- and actual names
  | CommandTypeMismatch
       HakaruTypeRep         -- | Expected type
       HakaruTypeRep         -- | Actual type
   deriving (Typeable)

instance Exception CommandMatchError

instance Show CommandMatchError where
  show (AmbiguousCommandName str cmds) =
    concat[ "Ambiguous command\n"
          , str, " could refer to any of\n"
          , intercalate "," $ map nameOfSomeCommand cmds ]
  show (UnknownCommandName str cmds) =
    concat[ "Unknown command\n"
          , str, " doesn't match any available commands:\n"
          , intercalate "," $ map nameOfSomeCommand cmds ]
  show (CommandTypeMismatch expt act) =
    let showCmd = either id (\(Some1 x) -> show $ prettyType 0 x) in
    concat[ "Type of input\n"
          , showCmd expt, " doesn't match expected command type:\n"
          , showCmd act ]

--------------------------------------------------------------------------------
-- | The class of commands
class (SingI c, Show (Sing c)) => IsCommand (c :: k) where
  -- | A specification of how the command will run. For most commands, this is
  -- given by the name alone
  type CommandSpec' c
  type CommandSpec' c = ()

  -- | Match the name of the command against a string
  matchCommandName :: String
                   -> Either CommandMatchError (CommandSpec c)

  -- | Match the type of an input program against the command input type
  matchCommandType :: CommandSpec c
                   -> Sing (i :: Hakaru)
                   -> Either CommandMatchError (Some1 (CommandType c i))

  -- | If the input type is a valid type, so is the output type
  commandIsType    :: CommandType c i o -> Sing i -> Sing o

-- | The name of a command
nameOfCommand   :: IsCommand c => CommandType c i o -> Sing c
nameOfCommand _ = sing

-- | An instance of `IsCommand' packed into a datatype
type IsCommandDict = Holds (IsCommand :: k -> Constraint)

-- | An existentially quantified instane of `IsCommand'
data SomeCommand where
  SomeCommand :: forall (c :: k) . IsCommandDict c -> SomeCommand

nameOfSomeCommand :: SomeCommand -> String
nameOfSomeCommand (SomeCommand cmd@(Holds :: IsCommandDict x)) = 
  show $ singOf cmd

-- | A default implementation for `Symbol`-kinded commands for
-- `matchCommandName' which performs 'fuzzy matching'
matchSymbolCommandName
  :: forall (c :: Symbol)
   . (IsCommand c, KnownSymbol c, CommandSpec' c ~ ())
  => String
  -> Either CommandMatchError (CommandSpec c)
matchSymbolCommandName s
    | (isInfixOf `on` map toLower) s (symbolVal (Proxy :: Proxy c))
    = Right $ CmdSpec ()
    | otherwise
    = Left $ UnknownCommandName s [SomeCommand (Holds :: IsCommandDict c)]

--------------------------------------------------------------------------------
-- | A dynamic command for a particular command type
data DynCommand' c (abt :: [Hakaru] -> Hakaru -> *) m where
  DynCmd :: (forall i o . c i o
                        -> abt '[] i -> m (abt '[] o))
         -> DynCommand' c abt m

type DynCommand c = DynCommand' (CommandType c)
type PureDynCommand c abt = DynCommand c abt Identity

dynCmd
  :: (ABT term abt, Monad m, IsCommand c)
  => String
  -> DynCommand c abt m
  -> TypedAST abt -> ExceptT CommandMatchError m (TypedAST abt)
dynCmd cmdNm cmd t =
  (ExceptT . return) (matchCommandName cmdNm) >>= \s ->
  dynCommand s cmd t

dynCommand
  :: (ABT term abt, Monad m)
  => CommandSpec c
  -> DynCommand c abt m
  -> TypedAST abt -> ExceptT CommandMatchError m (TypedAST abt)
dynCommand spec@CmdSpec{} (DynCmd runCmd) (TypedAST tyi termi) = do
  Some1 c <- ExceptT $ return $ matchCommandType spec tyi
  let tyo = commandIsType c tyi
  liftM (TypedAST tyo) $ lift (runCmd c termi)

dynCommand'
  :: (ABT term abt, Monad m, IsCommand c, CommandSpec' c ~ ())
  => DynCommand c abt m
  -> TypedAST abt -> ExceptT CommandMatchError m (TypedAST abt)
dynCommand' = dynCommand (CmdSpec ())

dynCommandPure
  :: (ABT term abt)
  => CommandSpec c -> PureDynCommand c abt
  -> TypedAST abt -> Either CommandMatchError (TypedAST abt)
dynCommandPure s c = runExcept . dynCommand s c

dynCommand'Pure
  :: (ABT term abt, IsCommand c, CommandSpec' c ~ ())
  => PureDynCommand c abt
  -> TypedAST abt -> Either CommandMatchError (TypedAST abt)
dynCommand'Pure = dynCommandPure (CmdSpec ())

--------------------------------------------------------------------------------
-- Some commands
--------------------------------------------------------------------------------
-- | A helper for commands which can be applied under function types
data UnderFun (c :: Hakaru -> Hakaru -> *) (i :: Hakaru) (o :: Hakaru) where
  UnderFun :: !(UnderFun c i o) -> UnderFun c (x ':-> i) (x ':-> o)
  HereCmd  :: !(c i o)          -> UnderFun c         i          o

underFunIsType :: (forall i' o' . c i' o' -> Sing i' -> Sing o')
               -> UnderFun c i o -> Sing i -> Sing o
underFunIsType k (HereCmd  c)         i  = k c i
underFunIsType k (UnderFun c) (SFun x i) = SFun x (underFunIsType k c i)

infixl 3 <-|>
(<-|>) :: Either e x -> Either e x -> Either e x
(<-|>) Left{}    x = x
(<-|>) x@Right{} _ = x

matchUnderFun :: (forall i' . Sing i' -> Either CommandMatchError (Some1 (c i')))
              -> Sing i -> Either CommandMatchError (Some1 (UnderFun c i))
matchUnderFun k ty@(SFun x i) =
  fmap (\(Some1 c) -> Some1 (UnderFun c)) (matchUnderFun k i) <-|>
  (\(Some1 c) -> Some1 $ HereCmd c) <$> k ty
matchUnderFun k ty =
  (\(Some1 c) -> Some1 $ HereCmd c) <$> k ty <-|>
  Left (CommandTypeMismatch (Left "x -> y") (Right $ Some1 ty))

commandUnderFun' :: forall c abt m
                 . (ABT Term abt, Monad m)
                => (forall i o .          c i o -> abt '[] i -> m (abt '[] o))
                -> (forall i o . UnderFun c i o -> abt '[] i -> m (abt '[] o))
commandUnderFun' run = go where
  go :: forall i o . UnderFun c i o -> abt '[] i -> m (abt '[] o)
  go c0 =
    case c0 of
      HereCmd  c -> run c
      UnderFun c -> underLam' (go c)

commandUnderFun'Pure
  :: forall c abt
   . (ABT Term abt)
  => (forall i o .          c i o -> abt '[] i -> abt '[] o)
  -> (forall i o . UnderFun c i o -> abt '[] i -> abt '[] o)
commandUnderFun'Pure run c i0 =
  runIdentity $ commandUnderFun' (\c i -> pure $ run c i) c i0

commandUnderFun :: forall c abt m
                 . (ABT Term abt, Monad m)
                => DynCommand'           c  abt m
                -> DynCommand' (UnderFun c) abt m
commandUnderFun (DynCmd run) = DynCmd $ commandUnderFun' run

--------------------------------------------------------------------------------
data OneOf x = OneOf [x]

data In (xs :: [k]) (x :: k) where
  InH :: In (x ': xs) x
  InT :: !(In xs x) -> In (x0 ': xs) x

class Member (xs :: [k]) (x :: k) where
  inj :: f x -> In xs x
instance Member (x ': xs) x where
  inj _ = InH
instance Member xs x => Member (x0 ': xs) x where
  inj = InT . inj

listSing :: forall xs . All SingI xs => List1 Sing xs
listSing = fmap11 (\c@Holds -> singOf c) (allHolds :: List1 (Holds SingI) xs)

newtype instance Sing ('OneOf xs) = SingOneOf (List1 Sing xs)

deriving instance Show1 (Sing :: k -> *) => Show (Sing ('OneOf (xs :: [k])))

instance All SingI xs => SingI ('OneOf xs) where sing = SingOneOf listSing

data instance CommandType ('OneOf cs) i o where
  OneOfCmds :: IsCommand c
            => !(In cs c) -> !(CommandType c i o)
            -> CommandType ('OneOf cs) i o

injCmd :: (IsCommand c, Member cs c)
       => CommandType c i o
       -> CommandType ('OneOf cs) i o
injCmd c = OneOfCmds (inj Proxy) c

instance (All IsCommand cs, All SingI cs, Show1 (Sing :: k -> *))
  => IsCommand ('OneOf (cs :: [k])) where
  type CommandSpec' ('OneOf cs) = Some1 (Pair1 (In cs) CommandSpec)

  commandIsType (OneOfCmds _ c) = commandIsType c

  matchCommandType (CmdSpec (Some1 (Pair1 el cs@CmdSpec{}))) i =
    fmap (\(Some1 o) -> Some1 $ OneOfCmds el o) $ matchCommandType cs i

  matchCommandName cmdStr =
    let go :: (forall c . In cs1 c -> In cs2 c)
           -> List1 IsCommandDict cs1
           -> List1 (Compose (Either CommandMatchError)
                             (Pair1 (In cs2) CommandSpec)) cs1
        go _ Nil1 = Nil1
        go k (Cons1 c@(Holds :: IsCommandDict c) cs)
           = Cons1 (Compose $ fmap (\c' -> Pair1 (k InH) c')
                            $ matchCommandName cmdStr)
                   (go (k . InT) cs)

        availCmds = allHolds :: List1 IsCommandDict cs
        scOfSpec (Some1 (Pair1 _ c@(CmdSpec{} :: CommandSpec c)))
          = SomeCommand (Holds :: IsCommandDict c)
        matchingCmd =
          foldMap11 (either (const []) (pure . Some1) . getCompose)
            (go id availCmds)

    in case matchingCmd of
         [c] -> Right $ CmdSpec c
         []  -> Left $ UnknownCommandName cmdStr
                  (foldMap11 (pure . SomeCommand) availCmds)
         cs  -> Left $ AmbiguousCommandName cmdStr (map scOfSpec cs)

--------------------------------------------------------------------------------
data instance CommandType "Simplify" i o where
  Simplify :: CommandType "Simplify" a a

instance IsCommand "Simplify" where
  matchCommandName = matchSymbolCommandName
  commandIsType Simplify = id
  matchCommandType _ _ = return $ Some1 $ Simplify

--------------------------------------------------------------------------------
data instance CommandType "Reparam" i o where
  Reparam :: CommandType "Reparam" a a

instance IsCommand "Reparam" where
  matchCommandName = matchSymbolCommandName
  commandIsType Reparam = id
  matchCommandType _ _ = return $ Some1 $ Reparam

--------------------------------------------------------------------------------
data instance CommandType "Summarize" i o where
  Summarize :: CommandType "Summarize" a a

instance IsCommand "Summarize" where
  matchCommandName = matchSymbolCommandName
  commandIsType Summarize = id
  matchCommandType _ _ = return $ Some1 $ Summarize

--------------------------------------------------------------------------------
data DisintCommand :: Hakaru -> Hakaru -> * where
  Disint :: DisintCommand (HMeasure (HPair a b)) (a :-> HMeasure b)

newtype instance CommandType "Disintegrate" i o =
  DisintCmd (UnderFun DisintCommand i o)

instance IsCommand "Disintegrate" where
  matchCommandName = matchSymbolCommandName
  commandIsType (DisintCmd c) =
    underFunIsType (\Disint (sUnMeasure -> (sUnPair->(a,b))) ->
                      SFun a (SMeasure b)) c
  matchCommandType _ =
    fmap (\(Some1 c) -> Some1 $ DisintCmd c) .
    matchUnderFun (\i ->
    case i of
      SMeasure (SData (STyApp (STyApp
          (STyCon (jmEq1 sSymbol_Pair -> Just Refl)) a) b) _) ->
        return $ Some1 Disint
      _ -> throwError $
              CommandTypeMismatch (Left "measure (pair (a,b))")
                                  (Right $ Some1 i))
