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

data NumOp = Pos | Neg deriving (Eq, Show)

data InertExpr =
     InertName Text
   | InertNum  NumOp Integer
   | InertArgs Text [InertExpr]
 deriving (Eq, Show)

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

expr :: Parser InertExpr
expr =  try func
    <|> try name
    <|> try expseq
    <|> try intpos
    <|> intneg

func :: Parser InertExpr
func = InertArgs <$> text "_Inert_FUNCTION" <*> arg expr

name :: Parser InertExpr
name = InertName <$> (text "_Inert_NAME" *> apply1 stringLiteral)

expseq :: Parser InertExpr
expseq = InertArgs <$> text "_Inert_EXPSEQ" <*> arg expr

intpos :: Parser InertExpr
intpos = InertNum <$> (text "_Inert_INTPOS" *> return Pos) <*> apply1 integer

intneg :: Parser InertExpr
intneg = InertNum <$> (text "_Inert_INTNEG" *> return Neg) <*> fmap negate (apply1 integer)

parseMaple :: Text -> Either ParseError InertExpr
parseMaple = runParser (expr <* eof) () "<input>"

maple2AST :: InertExpr -> AST' Text
maple2AST (InertNum Pos i) = ULiteral $ Nat $ fromInteger i
maple2AST (InertNum Neg i) = ULiteral $ Int $ fromInteger i
