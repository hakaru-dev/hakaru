{-# LANGUAGE CPP, OverloadedStrings #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Language.Hakaru.Parser.Import (expandImports) where

import           Language.Hakaru.Parser.AST
import           Language.Hakaru.Parser.Parser (parseHakaruWithImports)

import           Control.Monad.Trans.Except
import           Control.Monad.IO.Class
import qualified Data.Text                     as T
import qualified Data.Text.IO                  as IO
import           Text.Parsec

replaceBody :: AST' T.Text -> AST' T.Text -> AST' T.Text
replaceBody e1 e2 =
    case e1 of
      Let      x  e3 e4 -> Let x e3 (replaceBody e4 e2)
      Ann      e3 t     -> Ann      (replaceBody e3 e2) t
      WithMeta e3 s     -> WithMeta (replaceBody e3 e2) s
      _                 -> e2

expandImports
    :: Maybe FilePath
    -> ASTWithImport' T.Text
    -> ExceptT ParseError IO (AST' T.Text)
expandImports dir (ASTWithImport' (Import i:is) ast) = do
    file  <- liftIO . IO.readFile . T.unpack $
             T.concat $ maybe [] ((:["/"]) . T.pack) dir ++ [ i, ".hk" ]
    astIm <- ExceptT . return $ parseHakaruWithImports file
    ast'  <- expandImports dir astIm
    expandImports dir (ASTWithImport' is (replaceBody ast' ast))
expandImports _ (ASTWithImport' [] ast) = return ast
