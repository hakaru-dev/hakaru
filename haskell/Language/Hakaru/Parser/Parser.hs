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
import           Data.Ratio                    ((%))
import           Data.Char                     (digitToInt)
import           Text.Parsec                   hiding (Empty)
import           Text.Parsec.Text              () -- instances only
import           Text.Parsec.Indentation
import           Text.Parsec.Indentation.Char
import qualified Text.Parsec.Indentation.Token as ITok
import qualified Text.Parsec.Expr              as Ex
import qualified Text.Parsec.Token             as Tok

import Language.Hakaru.Parser.AST


ops, types, names :: [String]
ops   = ["+","*","-","^", "**", ":",".", "<~","==", "=", "_", "<|>"]
types = ["->"]
names = ["def", "fn", "if", "else", "∞", "expect", "observe",
         "return", "match", "integrate", "summate", "product",
         "data", "import"]

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
    , Tok.opStart         = oneOf "!$%&*+./<=>?@\\^|-~"
    , Tok.opLetter        = oneOf "!$%&*+./<=>?@\\^|-~"
    , Tok.caseSensitive   = True
    , Tok.commentLine     = "#"
    , Tok.reservedOpNames = ops ++ types
    , Tok.reservedNames   = names
    }

comments :: Parser ()
comments = string "#"
           *> manyTill anyChar newline
           *> return ()

emptyLine :: Parser ()
emptyLine = newline *> return ()

lexer :: Tok.GenTokenParser ParserStream () Identity
lexer = ITok.makeTokenParser style

whiteSpace :: Parser ()
whiteSpace = Tok.whiteSpace lexer

decimal :: Parser Integer
decimal = Tok.decimal lexer

integer :: Parser Integer
integer = Tok.integer lexer

float :: Parser Rational
float =  (decimal >>= fractExponent) <* whiteSpace
                  
fractFloat :: Integer -> Parser (Either Integer Rational)
fractFloat n  =  fractExponent n >>= return . Right

fractExponent   :: Integer -> Parser Rational
fractExponent n =  do{ fract <- fraction
                     ; expo  <- option 1 exponent'
                     ; return ((fromInteger n + fract)*expo)
                     }
                  <|>
                  do{ expo <- exponent'
                    ; return ((fromInteger n)*expo)
                    }

fraction        :: Parser Rational
fraction        =  do{ _ <- char '.'
                     ; digits <- many1 digit <?> "fraction"
                     ; return (foldr op 0 digits)
                     }
                  <?> "fraction"
                    where
                      op d f    = (f + fromIntegral (digitToInt d))/10

exponent'       :: Parser Rational
exponent'       =  do{ _ <- oneOf "eE"
                     ; f <- sign
                     ; e <- decimal <?> "exponent"
                     ; return (power (f e))
                     }
                  <?> "exponent"
                      where
                       power e  | e < 0      = 1.0/power(-e)
                                | otherwise  = fromInteger (10^e)
                       sign            =   (char '-' >> return negate)
                                       <|> (char '+' >> return id)
                                       <|> return id

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

app1 :: Text -> AST' Text -> AST' Text
app1 s x@(WithMeta _ m) = WithMeta (Var s `App` x) m
app1 s x                = Var s `App` x

app2 :: Text -> AST' Text -> AST' Text -> AST' Text
app2 s x y = Var s `App` x `App` y

-- | Smart constructor for divide
divide :: AST' Text -> AST' Text -> AST' Text
divide (ULiteral x') (ULiteral y') = ULiteral (go x' y')
  where go :: Literal' -> Literal' -> Literal'
        go (Nat  x) (Nat  y) = Prob (x % y)
        go x        y        = Real (litToRat x / litToRat y)

        litToRat :: Literal' -> Rational
        litToRat (Nat  x) = toRational x
        litToRat (Int  x) = toRational x
        litToRat (Prob x) = toRational x
        litToRat (Real x) = toRational x
divide x y = NaryOp Prod [x, app1 "recip" y]

binop :: Text ->  AST' Text ->  AST' Text ->  AST' Text
binop s x y
    | s == "+"   = NaryOp Sum  [x, y]
    | s == "-"   = NaryOp Sum  [x, app1 "negate" y]
    | s == "*"   = NaryOp Prod [x, y]
    | s == "/"   = x `divide` y
    | s == "<"   = app2 "less"  x y
    | s == ">"   = app2 "less"  y x
    | s == "=="  = app2 "equal" x y
    | s == "<="  = NaryOp Or [ app2 "less"  x y
                             , app2 "equal" x y]
    | s == ">="  = NaryOp Or [ app2 "less"  y x
                             , app2 "equal" x y]
    | s == "&&"  = NaryOp And  [x, y]
    | s == "<|>" = Msum [x, y]
    | otherwise  = app2 s x y

binary :: String -> Ex.Assoc -> Operator (AST' Text)
binary s = Ex.Infix (binop (Text.pack s) <$ reservedOp s)

prefix :: String -> (a -> a) -> Operator a 
prefix s f = Ex.Prefix (f <$ reservedOp s)

postfix :: Parser (a -> a) -> Operator a
postfix p = Ex.Postfix . chainl1 p . return $ flip (.)

table :: OperatorTable (AST' Text)
table =
    [ [ postfix array_index ]
    , [ prefix "+"  id ]
    , [ binary "^"  Ex.AssocRight
      , binary "**" Ex.AssocRight]
    , [ binary "*"  Ex.AssocLeft
      , binary "/"  Ex.AssocLeft]
    , [ binary "+"  Ex.AssocLeft
      , binary "-"  Ex.AssocLeft
      , prefix "-"  (app1 "negate")]
    -- TODO: add "<=", ">=", "/="
    -- TODO: do you *really* mean AssocLeft? Shouldn't they be non-assoc?
    , [ postfix ann_expr ]
    , [ binary "<|>" Ex.AssocRight]
    , [ binary "<"   Ex.AssocLeft
      , binary ">"   Ex.AssocLeft
      , binary "<="  Ex.AssocLeft
      , binary ">="  Ex.AssocLeft
      , binary "=="  Ex.AssocLeft]
    , [ binary "&&"  Ex.AssocLeft]]

unit_ :: Parser (AST' a)
unit_ = Unit <$ symbol "()"

empty_ :: Parser (AST' a)
empty_ = Empty <$ symbol "[]"

int :: Parser (AST' a)
int = do
    n <- integer
    return $
        if n < 0
        then ULiteral $ Int n
        else ULiteral $ Nat n

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
inf_ = reserved "∞" *> return Infinity'

var :: Parser (AST' Text)
var = Var <$> identifier

pairs :: Parser (AST' Text)
pairs = foldr1 Pair <$> parens (commaSep expr)

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
        <|> (PData' <$> (DV "pair" <$> parens (commaSep pat_expr)))
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

integrate_expr :: Parser (AST' Text)
integrate_expr =
    reserved "integrate"
    *> (Integrate
        <$> identifier
        <*  symbol "from"        
        <*> expr
        <*  symbol "to"
        <*> expr     
        <*> semiblockExpr
        )

summate_expr :: Parser (AST' Text)
summate_expr =
    reserved "summate"
    *> (Summate
        <$> identifier
        <*  symbol "from"        
        <*> expr
        <*  symbol "to"
        <*> expr     
        <*> semiblockExpr
        )

product_expr :: Parser (AST' Text)
product_expr =
    reserved "product"
    *> (Product
        <$> identifier
        <*  symbol "from"        
        <*> expr
        <*  symbol "to"
        <*> expr     
        <*> semiblockExpr
        )

expect_expr :: Parser (AST' Text)
expect_expr =
    reserved "expect"
    *> (Expect
        <$> identifier
        <*> expr
        <*> semiblockExpr
        )

observe_expr :: Parser (AST' Text)
observe_expr =
    reserved "observe"
    *> (Observe
        <$> expr
        <*> expr
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

array_index :: Parser (AST' Text -> AST' Text)
array_index = flip Index <$> brackets expr

array_literal :: Parser (AST' Text)
array_literal = checkEmpty <$> brackets (commaSep expr)
  where checkEmpty [] = Empty
        checkEmpty xs = Array "" (ULiteral . Nat . fromIntegral . length $ xs)
                        (go 0 xs)

        go _ []      = error "the impossible happened"
        go _ [x]     = x
        go n (x:xs)  = If (Var "equal" `App` (Var "") `App` (ULiteral $ Nat n))
                          x
                          (go (n + 1) xs)
                

plate_expr :: Parser (AST' Text)
plate_expr =
    reserved "plate"
    *> (Plate
        <$> identifier
        <*  symbol "of"
        <*> expr
        <*> semiblockExpr
        )

chain_expr :: Parser (AST' Text)
chain_expr =
    reserved "chain"
    *> (Chain
        <$> identifier
        <*> expr
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
        <*> type_expr
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
    vars <- parens (commaSep defarg)
    bodyTyp <- optionMaybe type_expr
    body    <- semiblockExpr
    let body' = foldr (\(var', varTyp) e -> Lam var' varTyp e) body vars
        typ   = foldr TypeFun <$> bodyTyp <*> return (map snd vars)
    Let name (maybe id (flip Ann) typ body')
        <$> expr -- the \"rest\"; i.e., where the 'def' is in scope

defarg :: Parser (Text, TypeAST')
defarg = (,) <$> identifier <*> type_expr

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
    <|> try integrate_expr
    <|> try summate_expr
    <|> try product_expr
    <|> try expect_expr
    <|> try observe_expr
    <|> try array_expr
    <|> try plate_expr
    <|> try chain_expr
    <|> try let_expr
    <|> try bind_expr
    <|> try call_expr
    <|> try array_literal
    <|> try floating
    <|> try inf_
    <|> try unit_
    <|> try empty_
    <|> try int
    <|> try var
    <|> try pairs
    <|> parens expr
    <?> "an expression"

expr :: Parser (AST' Text)
expr = withPos (Ex.buildExpressionParser table (withPos term) <?> "an expression")


indentConfig :: Text -> ParserStream
indentConfig =
    mkIndentStream 0 infIndentation True Ge . mkCharIndentStream

parseHakaru :: Text -> Either ParseError (AST' Text)
parseHakaru =
    runParser (skipMany (comments <|> emptyLine) *>
               expr <* eof) () "<input>" . indentConfig

parseHakaruWithImports :: Text -> Either ParseError (ASTWithImport' Text)
parseHakaruWithImports =
    runParser (skipMany (comments <|> emptyLine) *>
               exprWithImport <* eof) () "<input>" . indentConfig

withPos :: Parser (AST' a) -> Parser (AST' a)
withPos x = do
    s  <- getPosition
    x' <- x
    e  <- getPosition
    return $ WithMeta x' (SourceSpan s e)

data_expr :: Parser (AST' Text)
data_expr =
    reserved "data"
    *>  (Data
        <$> identifier
        <*  parens (commaSep identifier) -- TODO: why throw them away?
        <*> blockOfMany (try type_app <|> type_var)
        )

import_expr :: Parser (Import Text)
import_expr =
    reserved "import" *> (Import <$> identifier)

exprWithImport :: Parser (ASTWithImport' Text)
exprWithImport = ASTWithImport' <$> (many import_expr) <*> expr
