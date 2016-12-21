{-# LANGUAGE CPP, OverloadedStrings #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Language.Hakaru.Parser.Import where

import           Language.Hakaru.Parser.AST
import           Language.Hakaru.Parser.Parser

import qualified Data.Text                     as T
import qualified Data.Text.IO                  as IO
import           Text.Parsec                   hiding (Empty)

replaceBody :: AST' T.Text -> AST' T.Text -> AST' T.Text
replaceBody e1 e2 =
    case e1 of
      Let      x  e3 e4 -> Let x e3 (replaceBody e4 e2)
      Ann      e3 t     -> Ann      (replaceBody e3 e2) t
      WithMeta e3 s     -> WithMeta (replaceBody e3 e2) s
      _                 -> e2

expandImports
    :: ASTWithImport' T.Text
    -> IO (Either ParseError (AST' T.Text))
expandImports (ASTWithImport' (Import i:is) ast) = do
    file <- IO.readFile . T.unpack $ T.append i ".hk"
    case parseHakaruWithImports file of
      Left err    -> return (Left err)
      Right astIm -> expandImports astIm >>= \astE ->
        case astE of
          Left err   -> return (Left err)
          Right ast' ->
              expandImports (ASTWithImport' is (replaceBody ast' ast))
expandImports (ASTWithImport' [] ast) = return (Right ast)
