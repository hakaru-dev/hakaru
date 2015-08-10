{-# LANGUAGE RankNTypes, GADTs, ExistentialQuantification,
             StandaloneDeriving, OverloadedStrings #-}
module Language.Hakaru.Parser.Parser where

import Prelude hiding (Real)

import Control.Applicative ((<$>))
import qualified Control.Monad as M
import Data.Functor.Identity
import Data.Text hiding (foldr)

import Text.Parsec hiding (Empty)
import Text.Parsec.Text hiding (Parser())
import Text.Parsec.Indentation
import Text.Parsec.Indentation.Char

import qualified Text.Parsec.Expr as Ex
import qualified Text.Parsec.Token as Tok

import Language.Hakaru.Parser.AST
import Language.Hakaru.Syntax

ops, dist, names :: [String]

ops   = ["+","*","-",":","<~", "==", "="]
dist  = ["return", "lebesgue", "counting", "uniform",
         "normal", "superpose", "categorical", "beta",
         "gamma", "poisson"
        ]
names = ["def","fn", "if","else","pi","inf"] ++ dist


type Parser = ParsecT (IndentStream (CharIndentStream Text)) () Identity

style = Tok.LanguageDef
        { Tok.commentStart   = ""
        , Tok.commentEnd     = ""
        , Tok.nestedComments = True
        , Tok.identStart     = letter <|> char '_'
        , Tok.identLetter    = alphaNum <|> oneOf "_'"
        , Tok.opStart        = oneOf ":!#$%&*+./<=>?@\\^|-~"
        , Tok.opLetter       = oneOf ":!#$%&*+./<=>?@\\^|-~"
        , Tok.caseSensitive  = True
        , Tok.commentLine = "#"
        , Tok.reservedOpNames = ops
        , Tok.reservedNames = names
        }

lexer = Tok.makeTokenParser style

integer :: Parser Integer
integer = Tok.integer lexer

float :: Parser Double
float = Tok.float lexer

parens :: Parser a -> Parser a
parens x = Tok.parens lexer (localIndentation Any x)

brackets :: Parser a -> Parser a
brackets x = Tok.brackets lexer (localIndentation Any x)

commaSep :: Parser a -> Parser [a]
commaSep = Tok.commaSep lexer

semiSep :: Parser a -> Parser [a]
semiSep = Tok.semiSep lexer

semiSep1 :: Parser a -> Parser [a]
semiSep1 = Tok.semiSep1 lexer
 
identifier :: Parser Text
identifier = M.liftM pack $ Tok.identifier lexer

reserved :: String -> Parser ()
reserved = Tok.reserved lexer

reservedOp :: String -> Parser ()
reservedOp = Tok.reservedOp lexer

symbol :: Text -> Parser Text
symbol = M.liftM pack . Tok.symbol lexer . unpack

binop :: Text ->  AST' Text ->  AST' Text ->  AST' Text
binop s x y = Op s `App` x `App` y

binary s assoc = Ex.Infix (do reservedOp s
                              return $ binop (pack s)) assoc

prefix s f = Ex.Prefix (reservedOp s >> return f)

table = [[prefix "+"  id],
         [binary "^"  Ex.AssocLeft]
        ,[binary "*"  Ex.AssocLeft,
          binary "/"  Ex.AssocLeft]
        ,[binary "+"  Ex.AssocLeft,
          binary "-"  Ex.AssocLeft]
        ,[binary "<"  Ex.AssocLeft,
          binary "==" Ex.AssocLeft]]

unit_ :: Parser (AST' a)
unit_ = do u <- string "()"
           return Empty

bool :: Parser (AST' Text)
bool = do
  b <- try (symbol "True")
       <|> (symbol "False")
  return $ Op b

int :: Parser Value'
int = withPos $ do
  n <- integer
  return $ case (n < 0) of
             True  -> Int (fromInteger n)
             False -> Nat (fromInteger n)

floating :: Parser Value'
floating = withPos $ do
  sign <- option '+' (oneOf "+-")
  n <- float
  return $ case sign of
             '-' -> Real (-1.0*n)
             '+' -> Prob n

inf_ :: Parser Value'
inf_ = withPos $ do
  s <- option '+' (oneOf "+-")
  reserved "inf";
  return $ case s of
             '-' -> Real (-1.0 / 0.0)
             '+' -> Prob ( 1.0 / 0.0)

var :: Parser (AST' Text)
var = do
  x <- identifier
  return (Var x)

pairs :: Parser (AST' Text)
pairs = do
  l <- parens $ commaSep op_expr
  return $ foldr (binop "Pair") Empty l

op_factor :: Parser (AST' Text)
op_factor = try undefined --floating
            -- <|> try inf_
            <|> try unit_
            -- <|> try int
            <|> try bool
            <|> try var
            <|> try pairs

op_expr :: Parser (AST' Text)
op_expr = Ex.buildExpressionParser table op_factor

if_expr :: Parser (AST' Text)
if_expr = do
  reserved "if"
  test_expr <- expr -- localIndentation Ge (absoluteIndentation expr)
  
  reservedOp ":"
  texp <- expr -- localIndentation Ge (absoluteIndentation expr)
  
  reserved "else"
  reservedOp ":"
  fexp <- expr -- localIndentation Ge (absoluteIndentation expr)
  return $ (Op "if") `App` test_expr `App` texp  `App` fexp

lam_expr :: Parser (AST' Text)
lam_expr = do
   reserved "fn"
   x <- identifier

   reservedOp ":"
   body <- expr
   return $ Lam x body

bind_expr :: Parser (AST' Text)
bind_expr = do
   x <- identifier
   reservedOp "<~"
   v <- expr

   body <- expr
   return $ Bind x v body

let_expr :: Parser (AST' Text)
let_expr = do
   x <- identifier
   reservedOp "="
   v <- expr

   body <- expr
   return $ Let x v body

def_expr :: Parser (AST' Text)
def_expr = do
  reserved "def"
  name <- identifier

  args <- parens identifier -- op_expr
  reservedOp ":"
  
  body <- expr
  rest <- expr

  return $ Let name (Lam args body) rest

call_expr :: Parser (AST' Text)
call_expr = do
  name <- identifier
  args <- parens basic_expr
  return $ App (Op name) args

basic_expr :: Parser (AST' Text)
basic_expr = try call_expr
         <|> try op_expr
 
expr :: Parser (AST' Text)
expr = if_expr
   <|> lam_expr
   <|> def_expr
   <|> try let_expr
   <|> try basic_expr
 
indentConfig :: Text -> IndentStream (CharIndentStream Text)
indentConfig input = mkIndentStream 0 infIndentation True Ge (mkCharIndentStream input)

parseHakaru :: Text -> Either ParseError (AST' Text)
parseHakaru input
  = case runParser expr () "<input>" (indentConfig input) of
      Left err -> Left err
      Right a  -> Right a

withPos :: Parser (Meta -> a) -> Parser a
withPos x = do
  s  <- getPosition
  x' <- x
  e  <- getPosition
  return $ x' (Meta (s, e))
