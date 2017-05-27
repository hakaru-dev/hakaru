{-# LANGUAGE CPP
           , OverloadedStrings
           , PatternGuards
           , DataKinds
           , GADTs
           , TypeOperators
           #-}

module Main where

import           Language.Hakaru.Syntax.AST.Transforms
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Syntax.Value

import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Types.Sing
import           Language.Hakaru.Types.DataKind

import           Language.Hakaru.Sample
import           Language.Hakaru.Pretty.Concrete
import           Language.Hakaru.Command ( parseAndInfer, parseAndInfer'
                                         , readFromFile, Term)

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..), (<$>))
#endif
import           Control.Monad

import           Data.Monoid
import           Data.Text
import qualified Data.Text.IO as IO
import qualified Data.Vector  as V
import           Data.Word
import           System.IO (stderr)
import           Text.PrettyPrint (renderStyle, style, mode, Mode(LeftMode))

import qualified Options.Applicative as O
import qualified System.Random.MWC   as MWC

data Options = Options
  { noWeights  :: Bool
  , seed       :: Maybe Word32
  , transition :: Maybe String
  , prog       :: String }

options :: O.Parser Options
options = Options
  <$> O.switch
      ( O.long "no-weights" <>
        O.help "Don't print the weights" )
  <*> O.optional (O.option O.auto
      ( O.long "seed" <>
        O.help "Set random seed" <>
        O.metavar "seed"))
  <*> O.optional (O.strOption
      ( O.long "transition-kernel" <>
        O.metavar "k" <>
        O.help "Use this program as transition kernel for running a markov chain"))
  <*> O.strArgument
      ( O.metavar "PROGRAM" <>
        O.help "Hakaru program to run" )

parseOpts :: IO Options
parseOpts = O.execParser $ O.info (O.helper <*> options)
      (O.fullDesc <> O.progDesc "Run a hakaru program")

main :: IO ()
main = do
  args   <- parseOpts
  g      <- case seed args of
              Nothing -> MWC.createSystemRandom
              Just s  -> MWC.initialize (V.singleton s)
  case transition args of
      Nothing    -> runHakaru' g (noWeights args) =<< readFromFile (prog args)
      Just prog2 -> do prog' <- readFromFile (prog args)
                       trans <- readFromFile prog2
                       randomWalk' g trans prog'

illustrate :: Sing a -> Bool -> MWC.GenIO -> Value a -> IO ()
illustrate (SMeasure s) weights g (VMeasure m) = do
    x <- m (VProb 1) g
    case x of
      Just (samp, w) -> (if weights then id else withWeight w) (illustrate s weights g samp)
      Nothing        -> illustrate (SMeasure s) weights g (VMeasure m)

illustrate _ _ _ x = renderLn x

withWeight :: Value 'HProb -> IO () -> IO ()
withWeight w m = render w >> putStr "\t" >> m

render :: Value a -> IO ()
render = putStr . renderStyle style {mode = LeftMode} . prettyValue

renderLn :: Value a -> IO ()
renderLn = putStrLn . renderStyle style {mode = LeftMode} . prettyValue

runHakaru :: MWC.GenIO -> Bool -> Text -> IO ()
runHakaru g weights prog' =
    case parseAndInfer prog' of
      Left err                 -> IO.hPutStrLn stderr err
      Right (TypedAST typ ast) -> do
        case typ of
          SMeasure _ -> forever (illustrate typ weights g $ run ast)
          _          -> illustrate typ weights g $ run ast
    where
    run :: Term a -> Value a
    run = runEvaluate . expandTransformations

runHakaru' :: MWC.GenIO -> Bool -> Text -> IO ()
runHakaru' g weights prog = do
    prog' <- parseAndInfer' prog
    case prog' of
      Left err                 -> IO.hPutStrLn stderr err
      Right (TypedAST typ ast) -> do
        case typ of
          SMeasure _ -> forever (illustrate typ weights g $ run ast)
          _          -> illustrate typ weights g $ run ast
    where
    run :: Term a -> Value a
    run = runEvaluate . expandTransformations

randomWalk :: MWC.GenIO -> Text -> Text -> IO ()
randomWalk g p1 p2 =
    case (parseAndInfer p1, parseAndInfer p2) of
      (Right (TypedAST typ1 ast1), Right (TypedAST typ2 ast2)) ->
          -- TODO: Use better error messages for type mismatch
          case (typ1, typ2) of
            (SFun a (SMeasure b), SMeasure c)
              | (Just Refl, Just Refl) <- (jmEq1 a b, jmEq1 b c)
              -> iterateM_ (chain $ run ast1) (run ast2)
            _ -> IO.hPutStrLn stderr "hakaru: programs have wrong type"
      (Left err, _) -> IO.hPutStrLn stderr err
      (_, Left err) -> IO.hPutStrLn stderr err
    where
    run :: Term a -> Value a
    run = runEvaluate . expandTransformations

    chain :: Value (a ':-> b) -> Value ('HMeasure a) -> IO (Value b)
    chain (VLam f) (VMeasure m) = do
      Just (samp,_) <- m (VProb 1) g
      renderLn samp
      return (f samp)

randomWalk' :: MWC.GenIO -> Text -> Text -> IO ()
randomWalk' g p1 p2 = do
    p1' <- parseAndInfer' p1
    p2' <- parseAndInfer' p2
    case (p1', p2') of
      (Right (TypedAST typ1 ast1), Right (TypedAST typ2 ast2)) ->
          -- TODO: Use better error messages for type mismatch
          case (typ1, typ2) of
            (SFun a (SMeasure b), SMeasure c)
              | (Just Refl, Just Refl) <- (jmEq1 a b, jmEq1 b c)
              -> iterateM_ (chain $ run ast1) (run ast2)
            _ -> IO.hPutStrLn stderr "hakaru: programs have wrong type"
      (Left err, _) -> IO.hPutStrLn stderr err
      (_, Left err) -> IO.hPutStrLn stderr err
    where
    run :: Term a -> Value a
    run = runEvaluate . expandTransformations

    chain :: Value (a ':-> b) -> Value ('HMeasure a) -> IO (Value b)
    chain (VLam f) (VMeasure m) = do
      Just (samp,_) <- m (VProb 1) g
      renderLn samp
      return (f samp)

-- From monad-loops
iterateM_ :: Monad m => (a -> m a) -> a -> m b
iterateM_ f = g
    where g x = f x >>= g
