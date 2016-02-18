{-# LANGUAGE CPP, OverloadedStrings #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Language.Hakaru.Parser.Parser where

import Prelude hiding (Real)

#if __GLASGOW_HASKELL__ < 710
import           Data.Functor                  ((<$>), (<$))
import           Control.Applicative           (Applicative(..))
#endif
import qualified Control.Monad                 as M
import           Data.Functor.Identity
import           Data.Text                     (Text)
import qualified Data.Text                     as Text
import           Text.Parsec                   hiding (Empty)
import           Text.Parsec.Text              () -- instances only
import           Text.Parsec.Indentation
import           Text.Parsec.Indentation.Char
import qualified Text.Parsec.Indentation.Token as ITok
import qualified Text.Parsec.Expr              as Ex
import qualified Text.Parsec.Token             as Tok

import Language.Hakaru.Parser.AST


ops, types, names :: [String]
ops   = ["+","*","-","^", "**", ":",".", "<~","==", "=", "_"]
types = ["->"]
names = ["def","fn", "if","else","inf", "∞",
         "return", "match", "data"]

type ParserStream    = IndentStream (CharIndentStream Text)
type Parser          = ParsecT     ParserStream () Identity
type Operator a      = Ex.Operator ParserStream () Identity a
type OperatorTable a = [[Operator a]]

style :: Tok.GenLanguageDef ParserStream st Identity
style = ITok.makeIndentLanguageDef $ Tok.LanguageDef
    { Tok.commentStart    = ""
    , Tok.commentEnd      = ""
    , Tok.nestedComments  = True
    , Tok.identStart      = letter <|> char '_'
    , Tok.identLetter     = alphaNum <|> oneOf "_'"
    , Tok.opStart         = oneOf "!#$%&*+./<=>?@\\^|-~"
    , Tok.opLetter        = oneOf "!#$%&*+./<=>?@\\^|-~"
    , Tok.caseSensitive   = True
    , Tok.commentLine     = "#"
    , Tok.reservedOpNames = ops ++ types
    , Tok.reservedNames   = names
    }

lexer :: Tok.GenTokenParser ParserStream () Identity
lexer = ITok.makeTokenParser style

integer :: Parser Integer
integer = Tok.integer lexer

float :: Parser Double
float = Tok.float lexer

parens :: Parser a -> Parser a
parens = Tok.parens lexer . localIndentation Any

braces :: Parser a -> Parser a
braces = Tok.parens lexer . localIndentation Any

brackets :: Parser a -> Parser a
brackets = Tok.brackets lexer . localIndentation Any

commaSep :: Parser a -> Parser [a]
commaSep = Tok.commaSep lexer

semiSep :: Parser a -> Parser [a]
semiSep = Tok.semiSep lexer

semiSep1 :: Parser a -> Parser [a]
semiSep1 = Tok.semiSep1 lexer

identifier :: Parser Text
identifier = M.liftM Text.pack $ Tok.identifier lexer

reserved :: String -> Parser ()
reserved = Tok.reserved lexer

reservedOp :: String -> Parser ()
reservedOp = Tok.reservedOp lexer

symbol :: Text -> Parser Text
symbol = M.liftM Text.pack . Tok.symbol lexer . Text.unpack

binop :: Text ->  AST' Text ->  AST' Text ->  AST' Text
binop s x y
    | s == "+"  = NaryOp Sum  [x, y]
    | s == "-"  = NaryOp Sum  [x, Var "negate" `App` y]
    | s == "*"  = NaryOp Prod [x, y]
    | s == "<"  = Var "less" `App` x `App` y
    | otherwise = Var s `App` x `App` y

binary :: String -> Ex.Assoc -> Operator (AST' Text)
binary s = Ex.Infix (binop (Text.pack s) <$ reservedOp s)

prefix :: String -> (a -> a) -> Operator a 
prefix s f = Ex.Prefix (f <$ reservedOp s)

table :: OperatorTable (AST' Text)
table =
    [ [ prefix "+"  id
      , prefix "-"  (App (Var "negate"))]
    , [ binary "^"  Ex.AssocRight
      , binary "**" Ex.AssocRight]
    , [ binary "*"  Ex.AssocLeft
      , binary "/"  Ex.AssocLeft]
    , [ binary "+"  Ex.AssocLeft
      , binary "-"  Ex.AssocLeft]
    -- TODO: add "<", "<=", ">=", "/="
    -- TODO: do you *really* mean AssocLeft? Shouldn't they be non-assoc?
    , [ Ex.Postfix ann_expr ]
    , [ binary "<"  Ex.AssocLeft
      , binary "==" Ex.AssocLeft]]

unit_ :: Parser (AST' a)
unit_ = Unit <$ symbol "()"

empty_ :: Parser (AST' a)
empty_ = Empty <$ symbol "[]"

int :: Parser (AST' a)
int = do
    n <- integer
    return $
        if n < 0
        then ULiteral $ Int (fromInteger n)
        else ULiteral $ Nat (fromInteger n)

floating :: Parser (AST' a)
floating = do
    sign <- option '+' (oneOf "+-")
    n <- float
    return $
        case sign of
        '-' -> ULiteral $ Real (negate n)
        '+' -> ULiteral $ Prob n
        _   -> error "floating: the impossible happened"

inf_ :: Parser (AST' Text)
inf_ = do
    s <- option '+' (oneOf "+-")
    reserved "inf" <|> reserved "∞"
    return $
        case s of
        '-' -> NegInfinity'
        '+' -> Infinity'
        _   -> error "inf_: the impossible happened"

var :: Parser (AST' Text)
var = Var <$> identifier

pairs :: Parser (AST' Text)
pairs = foldr1 (binop "pair") <$> parens (commaSep expr)

type_var :: Parser TypeAST'
type_var = TypeVar <$> identifier

type_app :: Parser TypeAST'
type_app = TypeApp <$> identifier <*> parens (commaSep type_expr)

type_fun :: Parser TypeAST'
type_fun =
    chainr1
        (    try type_app
         <|> try type_var
         <|> parens type_fun)
        (TypeFun <$ reservedOp "->")

type_expr :: Parser TypeAST'
type_expr = try type_fun
        <|> try type_app
        <|> try type_var
        <|> parens type_expr

ann_expr :: Parser (AST' Text -> AST' Text)
ann_expr = reservedOp "." *> (flip Ann <$> type_expr)

pdat_expr :: Parser (PDatum Text)
pdat_expr = DV <$> identifier <*> parens (commaSep pat_expr)

pat_expr :: Parser (Pattern' Text)
pat_expr =  try (PData' <$> pdat_expr)
        <|> (PWild' <$ reservedOp "_")
        <|> (PVar' <$> identifier)


-- | Blocks are indicated by colons, and must be indented.
blockOfMany :: Parser a -> Parser [a]
blockOfMany p = do
    reservedOp ":"
    localIndentation Gt (many $ absoluteIndentation p)


-- | Semiblocks are like blocks, but indentation is optional. Also,
-- there are only 'expr' semiblocks.
semiblockExpr :: Parser (AST' Text)
semiblockExpr = reservedOp ":" *> localIndentation Ge expr


-- | Pseudoblocks seem like semiblocks, but actually they aren't
-- indented.
--
-- TODO: do we actually want this in our grammar, or did we really
-- mean to use 'semiblockExpr' instead?
pseudoblockExpr :: Parser (AST' Text)
pseudoblockExpr = reservedOp ":" *> expr


branch_expr :: Parser (Branch' Text)
branch_expr = Branch' <$> pat_expr <*> semiblockExpr

match_expr :: Parser (AST' Text)
match_expr =
    reserved "match"
    *>  (Case
        <$> expr
        <*> blockOfMany branch_expr
        )

data_expr :: Parser (AST' Text)
data_expr =
    reserved "data"
    *>  (Data
        <$> identifier
        <*  parens (commaSep identifier) -- TODO: why throw them away?
        <*> blockOfMany (try type_app <|> type_var)
        )

expect_expr :: Parser (AST' Text)
expect_expr =
    reserved "expect"
    *> (Expect
        <$> identifier
        <*> expr
        <*> semiblockExpr
        )

array_expr :: Parser (AST' Text)
array_expr =
    reserved "array"
    *> (Array
        <$> identifier
        <*  symbol "of"
        <*> expr
        <*> semiblockExpr
        )

if_expr :: Parser (AST' Text)
if_expr =
    reserved "if"
    *>  (If
        <$> localIndentation Ge expr
        <*> semiblockExpr
        <*  reserved "else"
        <*> semiblockExpr
        )

lam_expr :: Parser (AST' Text)
lam_expr =
    reserved "fn"
    *>  (Lam
        <$> identifier
        <*> semiblockExpr
        )

bind_expr :: Parser (AST' Text)
bind_expr = Bind
    <$> identifier
    <*  reservedOp "<~"
    <*> expr
    <*> expr

let_expr :: Parser (AST' Text)
let_expr = Let
    <$> identifier
    <*  reservedOp "="
    <*> expr
    <*> expr

def_expr :: Parser (AST' Text)
def_expr = do
    reserved "def"
    name <- identifier
    (vars,varTyps) <- unzip <$> parens (commaSep defarg)
    bodyTyp <- optionMaybe type_expr
    body    <- semiblockExpr
    let body' = foldr Lam body vars
        typ   = foldr TypeFun <$> bodyTyp <*> sequence varTyps
    Let name (maybe id (flip Ann) typ body')
        <$> expr -- the \"rest\"; i.e., where the 'def' is in scope

defarg :: Parser (Text, Maybe TypeAST')
defarg = (,) <$> identifier <*> optionMaybe type_expr

call_expr :: Parser (AST' Text)
call_expr =
    foldl App
        <$> (Var <$> identifier)
        <*> parens (commaSep expr)

return_expr :: Parser (AST' Text)
return_expr = do
    reserved "return" <|> reserved "dirac"
    Dirac <$> expr

term :: Parser (AST' Text)
term =  try if_expr
    <|> try return_expr
    <|> try lam_expr
    <|> try def_expr
    <|> try match_expr
    -- <|> try data_expr
    <|> try expect_expr
    <|> try array_expr
    <|> try let_expr
    <|> try bind_expr
    <|> try call_expr
    <|> try floating
    <|> try inf_
    <|> try unit_
    <|> try int
    <|> try var
    <|> try pairs
    <|> parens expr

expr :: Parser (AST' Text)
expr = Ex.buildExpressionParser table term


indentConfig :: Text -> ParserStream
indentConfig =
    mkIndentStream 0 infIndentation True Ge . mkCharIndentStream

parseHakaru :: Text -> Either ParseError (AST' Text)
parseHakaru =
    runParser (expr <* eof) () "<input>" . indentConfig

withPos :: Parser (AST' a) -> Parser (AST' a)
withPos x = do
    s  <- getPosition
    x' <- x
    e  <- getPosition
    return $ WithMeta x' (Meta s e)
