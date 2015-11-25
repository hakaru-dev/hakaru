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

arg :: Parser a -> Parser [a]
arg e = parens (commaSep e)

apply1 :: Parser a -> Parser a
apply1 e = do
  args <- arg e
  case args of
    [e'] -> return e'
    _    -> error "Expected only one argument"

apply2 :: Parser a -> Parser (a, a)
apply2 e = do
  args <- arg e
  case args of
    [e1, e2] -> return (e1, e2)
    _        -> error "Expected only two arguments"


text :: Text -> Parser Text
text = liftM Text.pack <$> string <$> Text.unpack

expr :: Parser (AST' Text)
expr =  try func
    <|> try name
    <|> intpos

func :: Parser (AST' Text)
func = do text "_Inert_FUNCTION"
          (f, x) <- apply2 expr
          return $ App f x

name :: Parser (AST' Text)
name = Var <$> (text "_Inert_NAME" *> apply1 stringLiteral)

intpos :: Parser (AST' Text)
intpos = (ULiteral . Nat . fromInteger) <$>
         (text "_Inert_INTPOS" *> apply1 integer)

parseMaple :: Text -> Either ParseError (AST' Text)
parseMaple = runParser (expr <* eof) () "<input>"
