{-# LANGUAGE RankNTypes, GADTs, ExistentialQuantification, StandaloneDeriving #-}
module Language.Hakaru.Parser.Parser where

import Prelude hiding (Real)

import Control.Applicative ((<$>))
import Data.Functor.Identity

import Text.Parsec
import Text.Parsec.Indentation
import Text.Parsec.Indentation.Char

import qualified Text.Parsec.Expr as Ex
import qualified Text.Parsec.Token as Tok

import Language.Hakaru.Parser.AST
import Language.Hakaru.Syntax

ops   = ["+","*","-",":","<~", "==", "="]
dist  = ["return", "lebesgue", "counting", "uniform",
         "normal", "superpose", "categorical", "beta",
         "gamma", "poisson"
        ]
names = ["def","fn", "if","else","pi","inf"] ++ dist


type Parser = ParsecT (IndentStream (CharIndentStream String)) () Identity

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
 
identifier :: Parser String
identifier = Tok.identifier lexer

reserved :: String -> Parser ()
reserved = Tok.reserved lexer

reservedOp :: String -> Parser ()
reservedOp = Tok.reservedOp lexer

symbol :: String -> Parser String
symbol = Tok.symbol lexer

binary s f assoc = Ex.Infix (reservedOp s >> return f) assoc
prefix s f = Ex.Prefix (reservedOp s >> return f )

table = [[prefix "+" id],
         [binary "^"  Pow Ex.AssocLeft]
        ,[binary "*"  Times Ex.AssocLeft,
          binary "/"  Divide Ex.AssocLeft]
        ,[binary "+"  Plus Ex.AssocLeft,
          binary "-"  Minus Ex.AssocLeft]
        ,[binary "<"  Lt_ Ex.AssocLeft,
          binary "==" Eq_ Ex.AssocLeft]]

unit_ :: Parser UExpr
unit_ = do u <- string "()"
           return Unit

bool :: Parser UExpr
bool = do
  b <- try (symbol "True")
       <|> (symbol "False")
  return $ Bool (b == "True")

int :: Parser UExpr
int = do
  n <- integer
  return $ Int (fromInteger n)

floating :: Parser UExpr
floating = do
  sign <- option 1 (do
             {s <- oneOf "+-";
              return $ if s == '-' then -1.0 else 1.0})
  n <- float
  return $ Double (n*sign)

var :: Parser UExpr
var = do
  x <- identifier
  return (Var x)

list :: Parser UExpr
list = do
  l <- brackets $ commaSep op_expr
  return $ foldr Cons Nil l

pairs :: Parser UExpr
pairs = do
  l <- parens $ commaSep op_expr
  return $ foldr Pair Unit l

op_factor :: Parser UExpr
op_factor = try floating
            <|> try unit_
            <|> try int
            <|> try bool
            <|> try var
            <|> try pairs
            <|> try list

op_expr :: Parser UExpr
op_expr = Ex.buildExpressionParser table op_factor

if_expr :: Parser UExpr
if_expr = do
  reserved "if"
  test_expr <- expr -- localIndentation Ge (absoluteIndentation expr)
  
  reservedOp ":"
  texp <- expr -- localIndentation Ge (absoluteIndentation expr)
  
  reserved "else"
  reservedOp ":"
  fexp <- expr -- localIndentation Ge (absoluteIndentation expr)
  return $ If test_expr texp fexp

lam_expr :: Parser UExpr
lam_expr = do
   reserved "fn"
   x <- identifier

   reservedOp ":"
   body <- expr
   return $ Lam (Var x) body

bind_expr :: Parser Dist
bind_expr = do
   x <- identifier
   reservedOp "<~"
   v <- dist_expr

   body <- dist_expr
   return $ Bind (Var x) v body

lebesgue_ :: Parser Dist
lebesgue_ = do
   reserved "lebesgue"
   return Lebesgue

counting_ :: Parser Dist
counting_ = do
   reserved "counting"
   return Counting

dirac_ :: Parser Dist
dirac_ = do
   reserved "return"
   v <- expr
   return $ Dirac v

uniform_ :: Parser Dist
uniform_ = do
   reserved "uniform"
   Pair lo (Pair hi Unit) <- pairs
   return $ Uniform lo hi

normal_ :: Parser Dist
normal_ = do
   reserved "normal"
   Pair mu (Pair sd Unit) <- pairs
   return $ Normal mu sd

categorical_ :: Parser Dist
categorical_ = do
   reserved "categorical"
   Pair (Cons x xs) Unit <- pairs
   return $ Categorical (Cons x xs)

superpose_ :: Parser Dist
superpose_ = do
   reserved "superpose"
   Pair (Cons x xs) Unit <- pairs
   return $ Superpose (Cons x xs)

beta_ :: Parser Dist
beta_ = do
   reserved "beta"
   Pair a (Pair b Unit) <- pairs
   return $ Beta a b

gamma_ :: Parser Dist
gamma_ = do
   reserved "gamma"
   Pair a (Pair b Unit) <- pairs
   return $ Gamma a b

poisson_ :: Parser Dist
poisson_ = do
   reserved "poisson"
   Pair l Unit <- pairs
   return $ Poisson l

dist_expr :: Parser Dist
dist_expr = lebesgue_
        <|> counting_
        <|> uniform_
        <|> normal_
        <|> categorical_
        <|> superpose_
        <|> beta_
        <|> gamma_
        <|> poisson_
        <|> dirac_
        <|> try bind_expr

let_expr :: Parser UExpr
let_expr = do
   x <- identifier
   reservedOp "="
   v <- expr

   body <- expr
   return $ Let (Var x) v body

def_expr :: Parser UExpr
def_expr = do
  reserved "def"
  name <- identifier

  args <- parens basic_expr
  reservedOp ":"
  
  body <- expr
  rest <- expr

  return $ Let (Var name) (Lam args body) rest

call_expr :: Parser UExpr
call_expr = do
  name <- identifier
  args <- parens basic_expr
  return $ App (Var name) args

basic_expr :: Parser UExpr
basic_expr = try call_expr
         <|> try op_expr
 
expr :: Parser UExpr
expr = if_expr
   <|> lam_expr
   <|> def_expr
   <|> try (dist_expr >>= return . Dist)
   <|> try let_expr
   <|> try basic_expr
 
indentConfig :: String -> IndentStream (CharIndentStream String)
indentConfig input = mkIndentStream 0 infIndentation True Ge (mkCharIndentStream input)

parseHakaru :: String -> Either ParseError UExpr
parseHakaru input
  = case runParser expr () "<input>" (indentConfig input) of
      Left err -> Left err
      Right a  -> Right a
