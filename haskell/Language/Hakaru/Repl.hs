{-# LANGUAGE CPP
           , DataKinds
           , OverloadedStrings
           , FlexibleContexts
           , GADTs
           , RankNTypes
           #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Language.Hakaru.Repl where


import           Language.Hakaru.Types.Sing
import           Language.Hakaru.Syntax.ABT
import qualified Language.Hakaru.Syntax.AST as T
import           Language.Hakaru.Syntax.AST.Transforms
import           Language.Hakaru.Syntax.Variable ()
import qualified Language.Hakaru.Parser.AST as U
import           Language.Hakaru.Parser.Parser (parseHakaru, parseReplLine)
import           Language.Hakaru.Parser.SymbolResolve (resolveAST)
import           Language.Hakaru.Pretty.Concrete
import           Language.Hakaru.Syntax.TypeCheck
import           Language.Hakaru.Sample
import           Language.Hakaru.Syntax.Value

import           Control.Monad.State.Strict (StateT, evalStateT, get, modify)
import           Control.Monad.IO.Class
import           Data.List (intercalate)
import qualified Data.Text      as Text
import qualified Data.Text.IO   as IO
import qualified Data.Vector    as V
import           Text.PrettyPrint (renderStyle, style, mode, Mode(LeftMode))
import qualified System.Random.MWC as MWC
import           System.Console.Repline

type Binding = (U.AST' Text.Text -> U.AST' Text.Text)
type ReplM a = HaskelineT (StateT Binding IO) a

initialReplState :: Binding
initialReplState = id

extendBindings :: Binding -> Binding -> Binding
extendBindings = flip (.)

triv :: TrivialABT T.Term '[] a -> TrivialABT T.Term '[] a
triv = id

app1 :: a -> U.AST' a -> U.AST' a
app1 s x = U.Var s `U.App` x
       
resolveAndInfer :: U.AST' Text.Text
              -> Either Text.Text (TypedAST (TrivialABT T.Term))
resolveAndInfer x = resolveAndInferWithMode x LaxMode

resolveAndInferWithMode
  :: ABT T.Term abt
  => U.AST' Text.Text
  -> TypeCheckMode
  -> Either Text.Text (TypedAST abt)
resolveAndInferWithMode x mode' =
    let m = inferType (resolveAST x) in
    runTCM m Nothing mode'

               
splitLines :: Text.Text -> Maybe (V.Vector Text.Text)
splitLines = Just . V.fromList . Text.lines

whenE :: MonadIO m => Either Text.Text b -> m () -> m ()
whenE (Left  err) _ = liftIO $ IO.putStrLn err
whenE (Right _)   m = m 
             
illustrate :: Sing a -> MWC.GenIO -> Value a -> IO ()
illustrate (SMeasure s) g (VMeasure m) = do
    x <- m (VProb 1) g
    case x of
      Just (samp, _) -> illustrate s g samp
      Nothing        -> illustrate (SMeasure s) g (VMeasure m)

illustrate _ _ x = renderLn x

renderLn :: Value a -> IO ()
renderLn = putStrLn . renderStyle style {mode = LeftMode} . prettyValue
             
runOnce :: MWC.GenIO -> U.AST' Text.Text -> IO ()
runOnce g prog =
  case resolveAndInfer prog of
    Left err -> IO.putStrLn err
    Right (TypedAST typ ast) ->
        illustrate typ g (runEvaluate ast)

type_ :: [String] -> ReplM ()
type_ prog =
    let prog' = intercalate " " prog in
    case parseHakaru (Text.pack prog') of
      Left err -> liftIO $ putStrLn (show err)
      Right e  -> do
        bindings <- get
        let prog'' = bindings (app1 "dirac" e)
        case resolveAndInfer prog'' of
          Left err -> liftIO $ IO.putStrLn err
          Right (TypedAST (SMeasure typ) _) -> liftIO $ putStrLn (prettyTypeS typ)
          _        -> liftIO $ putStrLn "the impossible happened"
                   
initM :: ReplM ()
initM = liftIO $ putStrLn banner
                   
-- Evaluation

-- No Typechecking of bindings
cmd :: MWC.GenIO -> String -> ReplM ()
cmd g x =
    case parseReplLine (Text.pack x) of
      Left err         -> liftIO $ putStrLn (show err)
      Right (Left b)   -> modify (extendBindings b) 
      Right (Right e)  -> do
        bindings <- get
        let prog' = bindings (app1 "dirac" e)
        liftIO $ runOnce g prog'


-- Typecheck bindings before adding them
cmd2 :: MWC.GenIO -> String -> ReplM ()
cmd2 g x =
    case parseReplLine (Text.pack x) of
      Left err  -> liftIO $ putStrLn (show err)
      Right e   -> do
        bindings <- get
        case e of
          Left b   -> let prog = bindings . b $ (app1 "dirac" U.Unit) in
                      whenE (resolveAndInfer prog) (modify $ extendBindings b)
          Right e' -> let prog = bindings (app1 "dirac" e') in
                      liftIO $ runOnce g prog
               
repl :: MWC.GenIO -> IO ()
repl g = flip evalStateT initialReplState
        $ evalRepl (pure ">>> ") (cmd2 g) opts (Just ':') (Word comp) initM

                   
-- Completion
comp :: Monad m => WordCompleter m
comp = listWordCompleter [":help", ":expand", ":hist", ":type"]

-- Commands
help :: [String] -> ReplM ()
help _ = liftIO $ putStrLn "Help!"

expand :: [String] -> ReplM ()
expand prog =
    let prog' = intercalate " " prog in
    case parseReplLine (Text.pack prog') of
      Left err         -> liftIO $ putStrLn (show err)
      Right (Left b)   -> modify (extendBindings b) 
      Right (Right e)  -> do
        bindings <- get
        let prog'' = bindings e
        case resolveAndInfer prog'' of
          Left err -> liftIO $ IO.putStrLn err
          Right (TypedAST _ ast) -> liftIO $ print (pretty (expandTransformations ast))


hist :: [String] -> ReplM ()
hist = undefined

opts :: [(String, [String] -> ReplM ())]
opts = [
    ("help", help),
    ("expand", expand),
    ("hist", hist),
    ("type", type_)
  ]

banner :: String
banner = unlines
  ["    __  __      __",
   "   / / / /___ _/ /______ ________  __",
   "  / /_/ / __ `/ //_/ __ `/ ___/ / / /",
   " / __  / /_/ / ,< / /_/ / /  / /_/ /",
   "/_/ /_/\\__,_/_/|_|\\__,_/_/   \\__,_/"
  ]

main :: IO ()
main = MWC.createSystemRandom >>= repl
