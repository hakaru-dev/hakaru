{-# LANGUAGE RankNTypes, GADTs, ExistentialQuantification,
             StandaloneDeriving, OverloadedStrings #-}
module Language.Hakaru.Parser.Parser where

import Prelude hiding (Real)

import Control.Applicative ((<$>), (<*))
import qualified Control.Monad as M
import Data.Functor.Identity
import Data.Text hiding (foldr1, foldl)

import Text.Parsec hiding (Empty)
import Text.ParserCombinators.Parsec (chainl1)
import Text.Parsec.Combinator (eof)
import Text.Parsec.Text hiding (Parser())
import Text.Parsec.Indentation
import Text.Parsec.Indentation.Char
import qualified Text.Parsec.Indentation.Token as ITok

import qualified Text.Parsec.Expr as Ex
import qualified Text.Parsec.Token as Tok

import Language.Hakaru.Parser.AST
import Language.Hakaru.Syntax.DataKind

ops, names :: [String]

ops   = ["+","*","-",":","::", "<~","==", "=", "_"]
types = ["->"]
names = ["def","fn", "if","else","pi","inf",
         "return", "match", "data"]

type Parser = ParsecT (IndentStream (CharIndentStream Text)) () Identity

style = ITok.makeIndentLanguageDef $ Tok.LanguageDef
        { Tok.commentStart   = ""
        , Tok.commentEnd     = ""
        , Tok.nestedComments = True
        , Tok.identStart     = letter <|> char '_'
        , Tok.identLetter    = alphaNum <|> oneOf "_'"
        , Tok.opStart        = oneOf ":!#$%&*+./<=>?@\\^|-~"
        , Tok.opLetter       = oneOf ":!#$%&*+./<=>?@\\^|-~"
        , Tok.caseSensitive  = True
        , Tok.commentLine = "#"
        , Tok.reservedOpNames = ops ++ types
        , Tok.reservedNames = names
        }

lexer = ITok.makeTokenParser style

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
binop s x y = Var s `App` x `App` y

binary s assoc = Ex.Infix (do reservedOp s
                              return $ binop (pack s)) assoc

prefix s f = Ex.Prefix (reservedOp s >> return f)

table = [[prefix "+"  id],
         [binary "^"  Ex.AssocLeft]
        ,[binary "*"  Ex.AssocLeft,
          binary "/"  Ex.AssocLeft]
        ,[binary "+"  Ex.AssocLeft,
          binary "-"  Ex.AssocLeft]
        ,[binary ">"  Ex.AssocLeft,
          binary "==" Ex.AssocLeft]]

unit_ :: Parser (AST' a)
unit_ = string "()" >> return Empty

int :: Parser Value'
int = do
  n <- integer
  return $ case (n < 0) of
             True  -> Int (fromInteger n)
             False -> Nat (fromInteger n)

floating :: Parser Value'
floating = do
  sign <- option '+' (oneOf "+-")
  n <- float
  return $ case sign of
             '-' -> Real (-1.0*n)
             '+' -> Prob n

inf_ :: Parser Value'
inf_ = do
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
  return $ foldr1 (binop "Pair") l

type_var :: Parser (TypeAST' Text)
type_var = do
  t <- identifier
  return (TypeVar t)

type_app :: Parser (TypeAST' Text)
type_app = do
   f    <- identifier
   args <- parens $ commaSep type_expr
   return $ foldl TypeApp (TypeVar f) args

type_fun :: Parser (TypeAST' Text)
type_fun = do
   chainl1 (try type_app <|> type_var)
           (reservedOp "->" >> return TypeFun)

type_expr :: Parser (TypeAST' Text)
type_expr = try type_fun
        <|> try type_app
        <|> type_var

ann_expr :: Parser (AST' Text)
ann_expr = do
  e <- basic_expr
  reservedOp "::"
  t <- type_expr
  return $ Ann e t

pdat_expr :: Parser (Datum' Text)
pdat_expr = do
   n <- identifier
   args <- parens $ commaSep identifier
   return $ DV n args

pat_expr :: Parser (Pattern' Text)
pat_expr = do
      try (pdat_expr >>= return . PData')
  <|> (reservedOp "_" >> return PWild') 
  <|> (identifier >>= return . PVar')

branch_expr :: Parser (Branch' Text)
branch_expr = do
   p <- pat_expr
   reservedOp ":"
   e <- expr
   return $ Branch' p e

match_expr :: Parser (AST' Text)
match_expr = do
   reserved "match"
   a <- expr
   reservedOp ":"
   clauses <- localIndentation Gt $
                many $ absoluteIndentation branch_expr
   return $ Case a clauses

data_expr :: Parser (AST' Text)
data_expr = do
   reserved "data"
   name <- identifier
   args <- parens $ commaSep identifier
   reservedOp ":"
   defs <- localIndentation Gt $
             many $ absoluteIndentation (try type_app <|> type_var)
   return $ Data name defs
   

op_factor :: Parser (AST' Text)
op_factor =     try (M.liftM UValue floating)
            <|> try (M.liftM UValue inf_)
            <|> try unit_
            <|> try (M.liftM UValue int)
            <|> try var
            <|> try pairs

op_expr :: Parser (AST' Text)
op_expr = Ex.buildExpressionParser table op_factor

if_expr :: Parser (AST' Text)
if_expr = do
  reserved "if"
  test_expr <- localIndentation Ge expr
  
  reservedOp ":"
  texp <- localIndentation Ge expr
  
  reserved "else"
  reservedOp ":"
  fexp <- localIndentation Ge expr
  return $ If test_expr texp fexp

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

  args <- parens $ commaSep identifier
  reservedOp ":"
  
  body <- expr
  rest <- expr

  return $ Let name (defargs args body) rest

defargs :: [Text] -> AST' Text -> AST' Text
defargs (a:as) body = Lam a (defargs as body)
defargs []     body = body 

call_expr :: Parser (AST' Text)
call_expr = do
  name <- identifier
  args <- parens $ commaSep basic_expr
  return $ foldl App (Var name) args

return_expr :: Parser (AST' Text)
return_expr = do
  reserved "return"
  arg <- basic_expr
  return $ App (Var "dirac") arg

basic_expr :: Parser (AST' Text)
basic_expr = try call_expr
         <|> try op_expr
 
expr :: Parser (AST' Text)
expr = if_expr
   <|> return_expr
   <|> lam_expr
   <|> def_expr
   <|> try match_expr
   <|> try data_expr
   <|> try ann_expr
   <|> try let_expr
   <|> try bind_expr
   <|> try basic_expr
 
indentConfig :: Text -> IndentStream (CharIndentStream Text)
indentConfig input = mkIndentStream 0 infIndentation True Ge (mkCharIndentStream input)

parseHakaru :: Text -> Either ParseError (AST' Text)
parseHakaru input
  = case runParser (expr  <* eof) () "<input>" (indentConfig input) of
      Left err -> Left err
      Right a  -> Right a

withPos :: Parser (AST' a) -> Parser (AST' a)
withPos x = do
  s  <- getPosition
  x' <- x
  e  <- getPosition
  return $ WithMeta x' (Meta (s, e))
