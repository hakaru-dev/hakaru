{-# LANGUAGE  RankNTypes
            , GADTs
            , ExistentialQuantification
            , StandaloneDeriving
            , OverloadedStrings #-}
module Language.Hakaru.Parser.Maple where

import           Language.Hakaru.Parser.AST
import           Control.Monad.Identity
import           Data.Text                     (Text)
import qualified Data.Text                     as Text
import           Data.Functor                  ((<$>), (<$))
import           Control.Applicative           (Applicative(..))
import           Text.Parsec
import           Text.Parsec.Text
import qualified Text.Parsec.Token as Token
import           Text.Parsec.Language

style :: GenLanguageDef Text st Identity
style = Token.LanguageDef
        { Token.commentStart   = "(*"
        , Token.commentEnd     = "*)"
        , Token.commentLine    = "#"
        , Token.nestedComments = True
        , Token.identStart     = letter <|> char '_'
        , Token.identLetter    = alphaNum <|> oneOf "_"
        , Token.opStart        = Token.opLetter style
        , Token.opLetter       = oneOf "+-*/<>="
        , Token.reservedOpNames= []
        , Token.reservedNames  = []
        , Token.caseSensitive  = False
        }

type TokenParser a = Token.GenTokenParser Text a Identity

lexer :: TokenParser ()
lexer = Token.makeTokenParser style

integer :: Parser Integer
integer = Token.integer lexer

float :: Parser Double
float = Token.float lexer

parens :: Parser a -> Parser a
parens = Token.parens lexer

identifier :: Parser Text
identifier = Text.pack <$> Token.identifier lexer

stringLiteral :: Parser Text
stringLiteral = Text.pack <$> Token.stringLiteral lexer

commaSep :: Parser a -> Parser [a]
commaSep = Token.commaSep lexer

text :: Text -> Parser Text
text = liftM Text.pack <$> string <$> Text.unpack

expr :: Parser (AST' Text)
expr =  try func
    <|> try name
    <|> intpos

func :: Parser (AST' Text)
func = do text "_Inert_FUNCTION"
          [f, x] <- parens (commaSep expr)
          return $ App f x

name :: Parser (AST' Text)
name = Var <$> (text "_Inert_NAME" *> parens stringLiteral)

intpos :: Parser (AST' Text)
intpos = (ULiteral . Nat . fromInteger) <$>
         (text "_Inert_INTPOS" *> parens integer)

parseMaple :: Text -> Either ParseError (AST' Text)
parseMaple = runParser (expr <* eof) () "<input>"
