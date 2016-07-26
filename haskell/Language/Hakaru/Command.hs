{-# LANGUAGE DataKinds #-}
module Language.Hakaru.Command where

import           Language.Hakaru.Syntax.ABT
import qualified Language.Hakaru.Syntax.AST as T
import           Language.Hakaru.Parser.Parser hiding (style)
import           Language.Hakaru.Parser.SymbolResolve (resolveAST')
import           Language.Hakaru.Syntax.TypeCheck

import           Data.Text
import qualified Data.Text.IO as IO

type Term a = TrivialABT T.Term '[] a

parseAndInfer :: Text
              -> Either String (TypedAST (TrivialABT T.Term))
parseAndInfer x =
    case parseHakaru x of
    Left  err  -> Left (show err)
    Right past ->
        let m = inferType (resolveAST past) in
        runTCM m LaxMode

readFromFile :: String -> IO Text
readFromFile "-" = IO.getContents
readFromFile x   = IO.readFile x

writeToFile :: String -> (Text -> IO ())
writeToFile "-" = IO.putStrLn
writeToFile x   = IO.writeFile x
