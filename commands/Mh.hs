{-# LANGUAGE OverloadedStrings
           , PatternGuards
           , DataKinds
           , GADTs
           , KindSignatures
           , RankNTypes
           , TypeOperators
           , FlexibleContexts #-}

module Main where

import           Language.Hakaru.Pretty.Concrete  
import           Language.Hakaru.Syntax.TypeCheck

import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Syntax.ABT (ABT(..))
import           Language.Hakaru.Syntax.AST (Term(..))
import           Language.Hakaru.Types.Sing
import           Language.Hakaru.Types.DataKind (Hakaru(..))
import           Language.Hakaru.Inference
import           Language.Hakaru.Command hiding (Term)
  
import           Data.Text
import qualified Data.Text.IO as IO
import           System.IO (stderr)

import           System.Environment

main :: IO ()
main = do
  args  <- getArgs
  progs <- mapM readFromFile args
  case progs of
      [prog2, prog1] -> runMH prog1 prog2
      _              -> IO.hPutStrLn stderr "Usage: mh <target> <proposal>"

runMH :: Text -> Text -> IO ()
runMH prog1 prog2 =
    case (parseAndInfer prog1, parseAndInfer prog2) of
      (Right (TypedAST typ1 ast1), Right (TypedAST typ2 ast2)) ->
         either (IO.hPutStrLn stderr) (print . pretty) $
         runMH' typ1 ast1 typ2 ast2
      (Left err, _) -> IO.hPutStrLn stderr err
      (_, Left err) -> IO.hPutStrLn stderr err

runMH' :: (ABT Term abt)
       => Sing a -> abt '[] a
       -> Sing b -> abt '[] b
       -> Either Text (abt '[] a)
runMH' propty prop tgtty tgt =
  case (propty, tgtty) of
    -- TODO: figure out how to write this case
    -- (_, SFun a tgtty')                -> _
    (SFun a (SMeasure b), SMeasure c) ->
      case (jmEq1 a b, jmEq1 b c) of
        (Just Refl, Just Refl) -> Right $ mcmc prop tgt
        (Nothing  , Just _   ) ->
          typeMismatchErr "proposal" (Left "x -> measure x") (Right propty)
        (Just _   , Nothing  ) ->
          typeMismatchErr "target" (Right $ SMeasure b) (Right tgtty)

    (_                  , SMeasure _) ->
      typeMismatchErr "proposal" (Left "x -> measure x") (Right propty)

    (SFun a (SMeasure b), _         ) ->
      typeMismatchErr "target" (Left "measure x") (Right tgtty)

    _                                 ->
      typeMismatchErr "input" (Left "(measure x, x -> measure x)")
                              (Right $ sPair tgtty propty)

typeMismatchErr
  :: Text
  -> Either Text (Sing (a :: Hakaru))
  -> Either Text (Sing (b :: Hakaru))
  -> Either Text x
typeMismatchErr pref expt got = Left $
  mconcat[ "mh: ", pref, " has wrong type\n"
         , "expected ", either id prettyTypeT expt , "\n"
         , "but got ", either id prettyTypeT got ]
