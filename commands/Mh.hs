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
import           Language.Hakaru.Syntax.Command (dynCommand'Pure)
import           Language.Hakaru.Syntax.Prelude (pair_)
import           Language.Hakaru.Command hiding (Term)
  
import           Data.Text
import qualified Data.Text.IO as IO
import           System.IO (stderr)
import           Data.Monoid (Monoid(mconcat))

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
         either (IO.hPutStrLn stderr)
                (elimTypedAST $ \_ -> print . pretty) $
         runMH' typ1 ast1 typ2 ast2
      (Left err, _) -> IO.hPutStrLn stderr err
      (_, Left err) -> IO.hPutStrLn stderr err

runMH' :: (ABT Term abt)
       => Sing a -> abt '[] a
       -> Sing b -> abt '[] b
       -> Either Text (TypedAST abt)
runMH' propty prop tgtty tgt =
  either (Left . pack . show) Right $
  dynCommand'Pure dynMCMC $
  TypedAST (sPair propty tgtty) $ pair_ propty tgtty prop tgt
