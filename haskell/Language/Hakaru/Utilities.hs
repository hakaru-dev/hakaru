module Language.Hakaru.Utilities where

import           Language.Hakaru.Syntax.ABT
import qualified Language.Hakaru.Syntax.AST as T
import           Language.Hakaru.Parser.Parser hiding (style)
import           Language.Hakaru.Parser.SymbolResolve (resolveAST)
import           Language.Hakaru.Syntax.TypeCheck

import Data.Text

parseAndInfer :: Text
              -> Either String (TypedAST (TrivialABT T.Term))
parseAndInfer x =
    case parseHakaru x of
    Left  err  -> Left (show err)
    Right past ->
        let m = inferType (resolveAST past) in
        runTCM m LaxMode
